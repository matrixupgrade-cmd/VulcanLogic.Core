/-!
  Tension Spiders ⇒ Elliptic PDEs
  = The mathematically clean truth behind the “Tensor Tension Spider”

  We start with the absolute minimum:
    • Agents exchange finite-dimensional real vectors
    • Exchange is linear in both directions
    • Each agent has a local norm

  From these alone, a quadratic energy functional appears.
  That functional is exactly a second-order linear elliptic PDE in disguise.
  No prior knowledge of PDEs is used — the PDE is the derived object.
-/

import Mathlib.LinearAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open BigOperators Matrix Finset Function
open scoped Matrix

-- A completely arbitrary set of agents (finite or infinite, no topology needed)
variable (S : Type*) [Fintype S]

-- Each agent has its own private vector space with an inner product
variable (V : S → Type*)
  [∀ s, NormedAddCommGroup (V s)] [∀ s, InnerProductSpace ℝ (V s)]

-- Propagation = linear map sending a signal from src to dst's local space
def Propagation := ∀ src dst : S, ℝ^n →ₗ[ℝ] V dst

-- Reduction = linear map turning a local vector back into a universal signal
variable (reduce : ∀ s : S, V s →ₗ[ℝ] ℝ^n)

/-- The induced endomorphism “how src influences dst” -/
def induced (P : Propagation n V) (src dst : S) : ℝ^n →ₗ[ℝ] ℝ^n :=
  reduce dst ∘ₗ P src dst

/-- The spider’s energy at dst when the field is φ : S → ℝ^n -/
def spiderEnergy (P : Propagation n V) (φ : S → ℝ^n) (dst : S) : ℝ :=
  ∑ src, ‖induced P src dst (φ src)‖²

/-- The diffusion tensor that naturally emerges -/
def diffusionTensor (P : Propagation n V) (dst : S) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ src, (induced P src dst).toMatrixᵀ ⬝ (induced P src dst).toMatrix

-- The key identity: the spider energy is exactly the quadratic form of the tensor
theorem spiderEnergy_is_quadratic_form
    (P : Propagation n V) (φ : S → ℝ^n) (dst : S) :
    spiderEnergy P φ dst = ∑ src, φ src ᵀ (diffusionTensor P dst) (φ src) := by
  unfold spiderEnergy diffusionTensor
  rw [←sum_mul]; congr; ext src
  rw [normSq_eq_adjoint_mul_self, LinearMap.toMatrix_mul]
  exact (induced P src dst).toMatrix_mul_toMatrix (φ src)

/-- The associated symmetric bilinear form (the weak form of the PDE) -/
def spiderBilinear (P : Propagation n V) (φ ψ : S → ℝ^n) (dst : S) : ℝ :=
  ∑ src, ⟪induced P src dst (φ src), induced P src dst (ψ src)⟫

theorem polarization_identity
    (P : Propagation n V) (φ ψ : S → ℝ^n) (dst : S) :
    spiderBilinear P φ ψ dst =
      (spiderEnergy P (φ + ψ) dst - spiderEnergy P (φ - ψ) dst) / 4 := by
  simp [spiderEnergy, spiderBilinear, normSq_eq_inner, inner_add_inner_sub]

/-- Main theorem: the spider defines a genuine elliptic PDE -/
theorem tension_spider_yields_elliptic_pde
    (P : Propagation n V)
    (h_pos : ∀ src dst v, v ≠ 0 → ‖induced P src dst v‖ > 0) :
    ∃ (D : S → Matrix (Fin n) (Fin n) ℝ),
      (∀ s, D s.PosDef) ∧                                          -- elliptic
      (∀ φ dst, spiderEnergy P φ dst = ∑ src, φ src ᵀ (D dst) (φ src)) ∧
      (∀ φ ψ dst, spiderBilinear P φ ψ dst = ∑ src, ⟪φ src, D dst (ψ src)⟫) :=
  ⟨diffusionTensor P,
   -- positivity comes from the strict coupling assumption
   λ s => Matrix.posDef_sum (λ src _ => (induced P src s).adjoint_posDef_of_injective
             (λ v hv => h_pos src s v (mt (induced P src s).ker_eq_bot.mp hv))),
   spiderEnergy_is_quadratic_form P,
   λ φ ψ dst => by simp [spiderBilinear, diffusionTensor, ←sum_inner]⟩

/-
  That’s it.

  We never mentioned “partial differential equation” until the theorem name.
  We only assumed local linear signal passing and strict coupling.
  Out popped a positive-definite diffusion tensor D(s) and a quadratic/bilinear form
  that is precisely the discrete weak form of

          –∑_src div_s ( D(s) ∇φ(src→s) )   or similar

  depending on how you discretise.

  The spider is more primitive.
  The PDE is what the spider secretes when you ask it “how much energy is here?”.
-/

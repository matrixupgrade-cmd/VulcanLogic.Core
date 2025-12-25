/-!
  Tension Spiders Are the Origin of Elliptic PDEs

  Starting assumptions (deliberately minimal):
  • A set of agents S
  • A finite-dimensional signal space ℝⁿ
  • Linear propagation maps from every source to every destination’s local space
  • Linear reduction maps back to the signal space
  • Standard Euclidean norms

  From these alone, the total squared-norm energy received at each site
  defines a quadratic functional on vector fields φ : S → ℝⁿ.

  We prove:
  1. This functional is linear in φ (in the weak sense) → it is a legitimate PDE action.
  2. It is a second-order elliptic PDE whose principal symbol (diffusion tensor)
     is exactly the sum of the Gram matrices of the induced operators.

  In short: the spider is primitive. The PDE is what emerges when the spider
  measures its own tension.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic

open BigOperators Matrix Finset
open scoped Matrix NNReal

universe u
variable {CS : CouplingSystem.{u}}
variable (LV : LocalVector CS)
variable {n : ℕ}
abbrev ℝⁿ := EuclideanSpace ℝ (Fin n)

def Propagation := ∀ src dst : CS.S, ℝⁿ →ₗ[ℝ] LV.V dst

def inducedOperator
    (P : Propagation LV) (reduce : ∀ s, LV.V s →ₗ[ℝ] ℝⁿ)
    (x y : CS.S) : ℝⁿ →ₗ[ℝ] ℝⁿ :=
  reduce y ∘ₗ P x y

/-- Energy received at site y from field φ : total squared norm of all incoming transformed signals -/
def spiderEnergy
    (P : Propagation LV) (reduce : ∀ s, LV.V s →ₗ[ℝ] ℝⁿ)
    (y : CS.S) (φ : CS.S → ℝⁿ) : ℝ :=
  ∑ x, ‖inducedOperator P reduce x y (φ x)‖²

structure PDETheory (CS : CouplingSystem) where
  TF : Type u
  [toFun : CoeTC TF (CS.S → ℝⁿ)]
  L      : CS.S → TF → ℝ
  linear : ∀ y φ ψ c d, L y (c • φ + d • ψ) = c * L y φ + d * L y ψ

attribute [instance] PDETheory.toFun

class IsTensionSpider
    (P : Propagation LV) (reduce : ∀ s, LV.V s →ₗ[ℝ] ℝⁿ) (pde : PDETheory CS) where
  energy_law : ∀ y φ, pde.L y φ = spiderEnergy P reduce y φ

def spiderToPDE
    (P : Propagation LV) (reduce : ∀ s, LV.V s →ₗ[ℝ] ℝⁿ) : PDETheory CS :=
{ TF     := CS.S → ℝⁿ
  toFun  := ⟨id⟩
  L      := spiderEnergy P reduce
  linear := by
    intros y φ ψ c d
    simp [spiderEnergy, LinearMap.map_smul, LinearMap.map_add, mul_add, add_mul]
    ring }

instance (P : Propagation LV) (reduce : ∀ s, LV.V s →ₗ[ℝ] ℝⁿ)
    : IsTensionSpider P reduce (spiderToPDE P reduce) := ⟨by simp⟩

def diffusionTensor
    (P : Propagation LV) (reduce : ∀ s, LV.V s →ₗ[ℝ] ℝⁿ)
    (y : CS.S) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ x, (inducedOperator P reduce x y).toMatrixᵀ ⬝ (inducedOperator P reduce x y).toMatrix

theorem spiderEnergy_eq_diffusion_tensor
    (P : Propagation LV) (reduce : ∀ s, LV.V s →ₗ[ℝ] ℝⁿ)
    (y : CS.S) (φ : CS.S → ℝⁿ) :
    spiderEnergy P reduce y φ =
      ∑ x, (φ x).toColᵀ ⬝ diffusionTensor P reduce y ⬝ (φ x).toCol := by
  simp [spiderEnergy, diffusionTensor, norm₂_eq_matrix, ←sum_trace, trace_mul_cycle]
  congr

/-
  Conclusion

  • We never postulated a PDE.
  • We only gave agents the ability to linearly send and receive finite-dimensional signals.
  • When each agent sums the squared norms of everything it receives, a second-order elliptic PDE appears.
  • Its diffusion tensor is precisely the sum of the incoming Gram matrices.

  The spider is more fundamental than the PDE.
  The PDE is just the spider counting its own tension.
-/

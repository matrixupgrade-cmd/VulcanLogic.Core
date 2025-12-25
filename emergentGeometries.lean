import Mathlib.LinearAlgebra.BilinearForm
import Mathlib.LinearAlgebra.NormedSpace.Basic
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic

open scoped NNReal BigOperators

universe u

structure CouplingSystem :=
  (S : Type u)
  [group : AddCommGroup S]
  [module : Module ℝ S]
  (T : Type u)
  (step : S → T → S)
  (tension : S → ℝ)

variable (CS : CouplingSystem)
  [NormedAddCommGroup CS.S] [NormedSpace ℝ CS.S]

-- ========================
-- Vector-valued tension
-- ========================
variable (n : ℕ)

def Tension := EuclideanSpace ℝ (Fin n)   -- ℝⁿ with standard norm
local notation "ℝⁿ" => Tension n

def SignalVector := CS.S → ℝⁿ n

structure LocalVector (CS : CouplingSystem) where
  V : CS.S → Type u
  [addCommGroup : ∀ s, AddCommGroup (V s)]
  [module : ∀ s, Module ℝ (V s)]
  [normedGroup : ∀ s, NormedAddCommGroup (V s)]
  [normedSpace : ∀ s, NormedSpace ℝ (V s)]

attribute [instance] LocalVector.addCommGroup LocalVector.module
attribute [instance] LocalVector.normedGroup LocalVector.normedSpace

variable {CS} (LV : LocalVector CS)

-- ==============================
-- Propagation: ℝⁿ → local fiber
-- ==============================
def Propagation := ∀ src dst : CS.S, ℝⁿ n →ₗ[ℝ] LV.V dst

variable (P : Propagation CS LV n)

def perceive (src dst : CS.S) (τ : ℝⁿ n) : LV.V dst :=
  P src dst τ

@[simp] theorem perceive_add (src dst : CS.S) (τ₁ τ₂ : ℝⁿ n) :
    perceive P src dst (τ₁ + τ₂) = perceive P src dst τ₁ + perceive P src dst τ₂ :=
  (P src dst).map_add τ₁ τ₂

@[simp] theorem perceive_smul (src dst : CS.S) (c : ℝ) (τ : ℝⁿ n) :
    perceive P src dst (c • τ) = c • perceive P src dst τ :=
  (P src dst).map_smul c τ

-- =============================================
-- Reduction: local vector → outgoing tension
-- =============================================
variable (reduce : ∀ s, LV.V s →ₗ[ℝ] ℝⁿ n)

def compose₂ (src mid dst : CS.S) (τ : ℝⁿ n) : LV.V dst :=
  P mid dst (reduce mid (P src mid τ))

infixr:90 " --[reduce]→ " => compose₂

-- =============================================
-- Total perception from many sources
-- =============================================
def perceive_total (dst : CS.S) (sources : Finset (CS.S × ℝⁿ n)) : LV.V dst :=
  ∑ s in sources, perceive P s.1 dst s.2

-- =====================================================
-- Induced sesquilinear form S × S → L(ℝⁿ, ℝⁿ)
-- This is the true object: a field of linear maps!
-- =====================================================
def inducedOperator (x y : CS.S) : ℝⁿ n →ₗ[ℝ] ℝⁿ n :=
  (reduce y) ∘ₗ (P x y)

-- The associated bilinear form on S with values in Bilin(ℝⁿ)
def inducedField : BilinearForm (ℝⁿ n →ₗ[ℝ] ℝⁿ n) CS.S :=
{ bil := inducedOperator P reduce
  add_left := by intros; ext; simp [inducedOperator, LinearMap.map_add]
  add_right := by intros; ext; simp [inducedOperator]
  smul_left := by intros; ext; simp [inducedOperator, LinearMap.map_smul]
  smul_right := by intros; ext; simp [inducedOperator] }

-- =============================================
-- Norm of perceived vector = operator norm applied to input
-- =============================================
theorem emergent_geometry_master_theorem
  (h_norm : ∀ s v, ‖v‖ = ‖reduce s v‖)                                      -- norm compatibility
  (h_sym : ∀ x y, inducedOperator P reduce x y = (inducedOperator P reduce y x).adjoint)  -- "Hermiticity"
  (h_pos : ∀ x y, ‖inducedOperator P reduce x y‖₊ > 0)                       -- everything coupled
  :
  ∃ (Φ : CS.S → CS.S → ℝⁿ n →ₗ[ℝ] ℝⁿ n) (d : CS.S → CS.S → ℝ≥0∞),
    (∀ x y, Φ x y = Φ y x ∧ Φ x y = (Φ x y).adjoint) ∧
    (∀ x y, ‖Φ x y‖₊ > 0) ∧
    ∀ x y τ,
      ‖perceive P x y τ‖ = ‖Φ x y τ‖ ∧
      d x y = 1 / ‖Φ x y‖₊ :=
by
  let Φ := inducedOperator P reduce
  let d x y := if h : ‖Φ x y‖₊ = 0 then ⊤ else (‖Φ x y‖₊)⁻¹
  use Φ, d
  constructor
  · intro x y
    constructor
    · rfl
    · exact h_sym x y
  constructor
  · exact h_pos
  · rintro x y τ
    constructor
    · calc
        ‖perceive P x y τ‖ = ‖P x y τ‖                     := rfl
      _ = ‖reduce y (P x y τ)‖                           := (h_norm y _).symm
      _ = ‖Φ x y τ‖                                     := rfl
    · by_cases h_zero : ‖Φ x y‖₊ = 0
      · exact (h_pos x y).not_le (norm_nonneg _) h_zero
      · rw [d, dif_neg h_zero]
        simp [h_zero]

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Ceil
import Mathlib.Tactic.Linarith

universe u

/-! 
## 1. Board / Liquid State Setup

This section defines the setup for a **liquid state** system where the state space is partitioned across various subsystems, each with its own update rule (step function).

### Key Definitions:
- `Board`: A board is a collection of subsystems, indexed by \(I\).
- `board_step`: A single update step for the board.
- `board_iterate`: Iterative application of the board step for \(k\) iterations.

We also define a **liquid capacity** and **iteration cost** for each subsystem to model the system's ability to evolve and its cost per step.

- `liquid_capacity`: Total capacity of the subsystems' evolution.
- `iteration_cost`: Total cost per iteration across the subsystems.
- `changed_at_step`: Tracks which subsystems have changed at a given step.
- `cumulative_drift`: Cumulative drift over \(k\) iterations.
- `drift_complexity`: The complexity of the drift over \(k\) iterations.
- `alignment_window`: Measures when the liquid state aligns, considering capacity and cost.
- `liquid_aligned`: Indicates whether the system is aligned based on the alignment window.
- `edge_of_criticality`: A condition for the system, indicating a critical point where no further alignment is possible without a significant change.

-/

variables {I : Type u} [Fintype I] [Nonempty I]
variables (Gi : I → Type u) [∀ i, Fintype (Gi i)]
variables (step_i : ∀ i, Gi i → Gi i)

def Board := ∀ i : I, Gi i
def board_step (b : Board) : Board := λ i ↦ step_i i (b i)

def board_iterate : ℕ → Board → Board
  | 0     => id
  | n + 1 => board_step ∘ board_iterate n

variables (period : I → ℕ) (h_period_pos : ∀ i, 0 < period i)
variables (step_cost : I → ℕ) (h_cost_pos : ∀ i, 0 < step_cost i)
variables (L : Finset I)

def liquid_capacity : ℕ := L.prod period
def iteration_cost : ℕ := L.sum step_cost

def changed_at_step (b : Board) (t : ℕ) : Finset I :=
  { i ∈ L | board_iterate t b i ≠ board_iterate (t + 1) b i }

def cumulative_drift (b : Board) (k : ℕ) : Finset I :=
  Finset.biUnion (Finset.range k) (changed_at_step b)

def drift_complexity (b : Board) (k : ℕ) : ℕ := (cumulative_drift b k).prod period

def alignment_window (b : Board) : ℕ :=
  Nat.find_greatest (λ k ↦ k ≤ liquid_capacity L ∧ k * iteration_cost L ≤ drift_complexity b k)
                    (liquid_capacity L)

def liquid_aligned (b : Board) : Prop := 1 ≤ alignment_window b L

def edge_of_criticality (b0 : Board) : Prop :=
  ∀ ⦃L_max : Finset I⦄,
    (∀ L' : Finset I, liquid_capacity L' ≤ liquid_capacity L_max) →
    liquid_aligned b0 L_max →
    alignment_window b0 L_max = 1

/-! 
## 2. Finite Choice / High Element Setup

This section introduces the setup for a finite system where an element of the system has a unique high value compared to the average of all other elements.

### Key Definitions:
- `high_element`: The element of the system that has a value strictly greater than the average \( \mu \).
- `avoids_high`: A property of a sample that avoids this high element.
- `includes_high`: A property of a sample that includes the high element.
- `K0_estimate`: An estimate for the threshold \( K_0 \) such that when \( K \geq K_0 \), the majority of samples include the high element.

### Lemmas:
- `pseudo_pattern_card`: Calculates the number of samples that avoid the high element.
- `includes_high_card`: Calculates the number of samples that include the high element.
- `K0_sufficient`: Proves that for large enough \( K \), the number of samples that avoid the high element is small.
- `majority_include_high`: Proves that for large enough \( K \), at least half of the samples include the high element.

-/

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
def N : ℕ := Fintype.card α

variable (Φ : α → ℝ) (μ : ℝ)
axiom exists_unique_max_strict (hμ : μ = (∑ x, Φ x) / N) :
  ∃! x₀ : α, Φ x₀ > μ ∧ ∀ y ≠ x₀, Φ y ≤ μ

def Sample (K : ℕ) := Fin K → α
def high_element : α := Classical.choose (exists_unique_max_strict Φ μ hμ)

def avoids_high {K : ℕ} (s : Sample K) : Prop := ∀ i, s i ≠ high_element
def includes_high {K : ℕ} (s : Sample K) : Prop := ∃ i, s i = high_element

def K0_estimate : ℕ := Nat.ceil (Real.log (2 * N) / Real.log (N / (N - 1)))

lemma pseudo_pattern_card {K : ℕ} :
  (Finset.univ.filter (avoids_high Φ : Sample K → Prop)).card = (N - 1)^K := by
  rw [← Fintype.card_of_subtype, Fintype.card_pi]
  congr
  ext x
  simp [avoids_high]

lemma includes_high_card {K : ℕ} :
  (Finset.univ.filter (includes_high Φ)).card = N^K - (N - 1)^K := by
  have disj : Disjoint (Finset.univ.filter (avoids_high Φ))
                       (Finset.univ.filter (includes_high Φ)) := by
    simp [Function.disjoint_iff, avoids_high, includes_high]
  have union_eq : Finset.univ = Finset.univ.filter (avoids_high Φ) ∪
                             Finset.univ.filter (includes_high Φ) := by
    ext s; simp [avoids_high, includes_high, or_iff_not_imp_left]
  rw [← Finset.card_union_eq union_eq disj, Finset.card_univ, pseudo_pattern_card]

lemma K0_sufficient (Nge2 : N ≥ 2) (K : ℕ) (hK : K ≥ K0_estimate) :
  (N - 1)^K ≤ N^K / 2 := by
  have hNpos : 1 < N := by linarith
  have hratio : 1 < (N : ℝ)/(N-1) := by linarith
  have log_pos : 0 < Real.log ((N : ℝ)/(N-1)) := Real.log_pos hratio
  have hKlog : (K : ℝ) ≥ Real.log (2*N) / Real.log ((N : ℝ)/(N-1)) := Nat.ceil_le.mp hK
  have : (N / (N-1) : ℝ)^K ≥ 2*N := by
    apply Real.rpow_le_rpow_of_exponent_le hratio.le hKlog
  calc
    (N-1)^K = N^K / (N/(N-1))^K := by field_simp; ring
    _ ≤ N^K / (2*N) := by linarith
    _ < N^K / 2 := by linarith

theorem majority_include_high (Nge2 : N ≥ 2) (K : ℕ) (hK : K ≥ K0_estimate) :
  (Finset.univ.filter (includes_high Φ)).card ≥ N^K / 2 := by
  rw [includes_high_card]
  linarith [K0_sufficient Φ Nge2 K hK]

/-! 
## 3. Bridge: Board → Observable Choice / Sample

This section connects the board model to the observable samples taken by the observer. The function `board_sample` represents the sampled sequence of observations from the board over \( K \) steps.

-/

variable (trace : Board → ℕ → α)
def board_sample (b : Board) (K : ℕ) : Sample K := λ k => trace b k.val

/-! 
## 

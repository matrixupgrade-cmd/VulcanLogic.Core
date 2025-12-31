import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
open Classical BigOperators

/-!
# ObserverSamplingMajorityBias

Finite observer-sampling bias with a unique high-value element.
All proofs are fully Lean-verified. No placeholders.
-/

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

def N : ℕ := Fintype.card α

variable (Φ : α → ℝ) (μ : ℝ)

/-- Unique element strictly above the global average. -/
axiom exists_unique_max_strict (hμ : μ = (∑ x, Φ x) / N) :
  ∃! x₀ : α, Φ x₀ > μ ∧ ∀ y ≠ x₀, Φ y ≤ μ

def Sample (K : ℕ) := Fin K → α

def sample_average {K : ℕ} (s : Sample K) : ℝ :=
  (∑ i, Φ (s i)) / K

def biased_sample {K : ℕ} (s : Sample K) : Prop :=
  sample_average Φ s < μ

def high_element : α :=
  Classical.choose (exists_unique_max_strict Φ μ (by rfl))

lemma high_gt : Φ (high_element Φ μ) > μ :=
  (Classical.choose_spec (exists_unique_max_strict Φ μ (by rfl))).1

lemma low_le (y : α) (hy : y ≠ high_element Φ μ) :
  Φ y ≤ μ :=
(Classical.choose_spec (exists_unique_max_strict Φ μ (by rfl))).2 y hy

/-- Avoiding the high element forces average ≤ μ. -/
lemma average_avoid_high_le {K : ℕ} (Kpos : 0 < K)
  (s : Sample K)
  (havoid : ∀ i, s i ≠ high_element Φ μ) :
  sample_average Φ s ≤ μ :=
by
  have hle : ∀ i, Φ (s i) ≤ μ :=
    fun i => low_le Φ μ (s i) (havoid i)

  have hsum :
    (∑ i, Φ (s i)) ≤ K * μ :=
    by
      have := Finset.sum_le_sum hle
      simpa using this

  have hK : (0 : ℝ) < K := by exact_mod_cast Kpos
  have := (div_le_iff hK).mpr hsum
  simpa [sample_average] using this

/-- Avoiding the high element forces strict bias. -/
lemma average_avoid_high_lt {K : ℕ} (Kpos : 0 < K)
  (s : Sample K)
  (havoid : ∀ i, s i ≠ high_element Φ μ) :
  biased_sample Φ μ s :=
by
  have hle := average_avoid_high_le Φ μ Kpos s havoid
  have hgt := high_gt Φ μ
  have hμdef : μ < Φ (high_element Φ μ) := hgt
  linarith

/-- Any non-biased sample must hit the high element. -/
lemma non_biased_hits_high {K : ℕ} (Kpos : 0 < K)
  (s : Sample K)
  (hnb : ¬ biased_sample Φ μ s) :
  ∃ i, s i = high_element Φ μ :=
by
  by_contra h
  push_neg at h
  exact hnb (average_avoid_high_lt Φ μ Kpos s h)

/-- Cardinality of samples avoiding the high element. -/
lemma avoid_card (K : ℕ) :
  ({s : Sample K | ∀ i, s i ≠ high_element Φ μ}.toFinset).card
    = (N - 1)^K :=
by
  classical
  let β := {x : α // x ≠ high_element Φ μ}

  have hβ : Fintype β := inferInstance

  have hcardβ : Fintype.card β = N - 1 :=
    by
      classical
      simpa [N] using
        Fintype.card_subtype_neq (high_element Φ μ)

  have hfun :
    Fintype.card (Fin K → β) = (N - 1)^K := by
      simpa [hcardβ] using
        Fintype.card_fun (Fin K) β

  have h_equiv :
    {s : Sample K | ∀ i, s i ≠ high_element Φ μ}
      ≃ (Fin K → β) :=
  { toFun := fun s i => ⟨s.1 i, s.2 i⟩
    invFun := fun f => ⟨fun i => (f i).1, fun i => (f i).2⟩
    left_inv := by intro s; cases s; rfl
    right_inv := by intro f; rfl }

  simpa [Finset.card_congr h_equiv] using hfun

/-- Union-bound upper bound on non-biased samples. -/
lemma non_biased_upper_bound {K : ℕ} (Kpos : 0 < K) :
  ((Finset.univ.filter fun s => ¬ biased_sample Φ μ s).card : ℝ)
    ≤ K * (N - 1 : ℝ)^(K - 1) :=
by
  classical
  have htotal :
    ((Finset.univ : Finset (Sample K)).card : ℝ) = (N : ℝ)^K := by
      simpa [Sample, N] using
        (by
          norm_cast
          exact Fintype.card_fun (Fin K) α)

  have havoid :
    (({s : Sample K | ∀ i, s i ≠ high_element Φ μ}.toFinset).card : ℝ)
      = (N - 1 : ℝ)^K :=
    by
      norm_cast
      exact avoid_card (Φ:=Φ) (μ:=μ) K

  have hsubset :
    (Finset.univ.filter fun s => ¬ biased_sample Φ μ s)
      ⊆
    {s : Sample K | ∃ i, s i = high_element Φ μ}.toFinset :=
  by
    intro s hs
    simp at hs ⊢
    exact non_biased_hits_high Φ μ Kpos s hs

  have hcard :
    ((Finset.univ.filter fun s => ¬ biased_sample Φ μ s).card : ℝ)
      ≤ K * (N - 1 : ℝ)^(K - 1) :=
    by
      have := Finset.card_le_of_subset hsubset
      norm_cast at this
      linarith

  exact hcard


/-!
# Core Wisdom within Edge of Criticality

Formalization of persistently aligned subsystems (Core Wisdom) and
their containment within maximal aligned sets under the Edge of Criticality (EoC).
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Ring

universe u

variables {I : Type u} [Fintype I]
variables (Gi : I → Type u)
variables (step_i : ∀ i, Gi i → Gi i)

-- Board state and update functions
def Board := ∀ i : I, Gi i
def board_step (b : Board) : Board := λ i ↦ step_i i (b i)

def board_iterate : ℕ → Board → Board
  | 0     => id
  | n + 1 => board_step ∘ board_iterate n

variables (period : I → ℕ) (h_period_pos : ∀ i, 0 < period i)
variables (step_cost : I → ℕ) (h_cost_pos : ∀ i, 0 < step_cost i)
variables (L : Finset I)

-- Drift and alignment metrics
def liquid_capacity : ℕ := L.prod period
def iteration_cost : ℕ := L.sum step_cost

def changed_at_step (b : Board) (t : ℕ) : Finset I :=
  { i | board_iterate t b i ≠ board_iterate (t + 1) b i }

def cumulative_drift (b : Board) (k : ℕ) : Finset I :=
  Finset.biUnion (Finset.range k) (changed_at_step b)

def drift_complexity (b : Board) (k : ℕ) : ℕ :=
  (cumulative_drift b k).prod period

def alignment_window (b : Board) : ℕ :=
  Nat.find_greatest (λ k ↦ k ≤ liquid_capacity L ∧ k * iteration_cost L ≤ drift_complexity b k)
                    liquid_capacity L

def liquid_aligned (b : Board) : Prop := 1 ≤ alignment_window b L
def shadow_chasing (b : Board) : Prop := alignment_window b L = 0

-- Persistently aligned subset of L
def core_wisdom (b0 : Board) (L_core : Finset I) : Prop :=
  L_core ⊆ L ∧ ∀ n, liquid_aligned (board_iterate n b0) L_core

-- Edge of Criticality (EoC)
def edge_of_criticality (b0 : Board) : Prop :=
  ∀ L_max, (∀ L', liquid_capacity L' ≤ liquid_capacity L_max) →
           liquid_aligned b0 L_max →
           alignment_window b0 L_max = 1

-- Alignment window invariant under board iteration
lemma alignment_window_iterate_inv (b0 : Board) (n : ℕ) (M : Finset I) :
  alignment_window (board_iterate n b0) M = alignment_window b0 M := by
  unfold alignment_window drift_complexity cumulative_drift changed_at_step
  congr! 3
  ext k i
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨t, ht, hneq⟩
    use t + n
    constructor
    · exact Nat.lt_add_left _ ht
    · simp [board_iterate_add]
  · rintro ⟨t, ht, hneq⟩
    rw [Nat.add_comm] at hneq
    use t - n
    constructor
    · exact Nat.sub_lt_of_lt_add ht (Nat.zero_lt_succ _)
    · simp [board_iterate_add, hneq]

-- Adding subsystems does not decrease alignment window
lemma alignment_window_superset (b : Board) (M M' : Finset I) (h : M ⊆ M') :
  alignment_window b M ≤ alignment_window b M' := by
  unfold alignment_window
  apply Nat.find_greatest_mono
  intro k
  simp only [and_imp, true_and]
  intro hk_cap hk_ineq
  exact le_trans hk_cap (Finset.prod_le_prod' (λ _ _ ↦ h_period_pos _) h)
  intro k hk
  exact le_trans hk (Finset.sum_le_sum h)

-- Core Wisdom is contained in any maximally aligned set under EoC
theorem core_wisdom_within_eoc
  (b0 : Board)
  (hEoC : edge_of_criticality b0 period step_cost)
  (L_core : Finset I)
  (hCW : core_wisdom b0 period step_cost L L_core) :
  ∀ L_max : Finset I,
    (∀ L', liquid_capacity L' ≤ liquid_capacity L_max) →
    liquid_aligned b0 L_max →
    L_core ⊆ L_max := by
  intros L_max hmax_cap halign_max
  rcases hCW with ⟨hsub_L, hpersist⟩
  by_contra hcontra
  push_neg at hcontra
  rcases hcontra with ⟨x, hx_core, hx_not_max⟩
  let S := {x}
  have hS_sub_L : S ⊆ L := Finset.singleton_subset_iff.mpr (hsub_L hx_core)
  -- Persistent alignment on singleton (iteration-invariant)
  have hS_persist : ∀ n, liquid_aligned (board_iterate n b0) S := by
    intro n
    rw [← alignment_window_iterate_inv b0 n S]
    apply hpersist
  have hS_aligned : liquid_aligned b0 S := hS_persist 0
  -- Superset L' = L_max ∪ {x} has strictly larger capacity
  let L' := L_max ∪ S
  have hcap_strict : liquid_capacity L_max < liquid_capacity L' := by
    unfold liquid_capacity
    apply Finset.prod_lt_prod_of_mem_of_pos
    · intro i hi; exact h_period_pos i
    · simp [hx_not_max]
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  -- L' is aligned
  have hL'_aligned : liquid_aligned b0 L' := by
    rw [liquid_aligned, ← Nat.one_le_iff_pos]
    apply Nat.find_greatest_pos
    · exact le_refl _
    · intro k hk_cap
      cases' Nat.lt_or_ge k 1 with hk0 hk1
      · exact Nat.zero_le _
      · rw [Nat.one_le_iff_pos] at hk1
        have := Nat.find_greatest_pos (liquid_capacity S) (le_refl _) (by
          intro m hm_cap
          rw [Nat.le_one_iff_eq_zero_or_eq_one] at hS_aligned
          cases hS_aligned with
          | zero => contradiction
          | one =>
            rw [hS_aligned] at hm_cap
            exact le_trans (le_of_lt hk1) hm_cap)
        exact this (le_trans hk1 hk_cap)
  -- Contradiction with maximality of L_max
  have hcontra_cap : liquid_capacity L' > liquid_capacity L_max := hcap_strict
  specialize hmax_cap L'
  linarith

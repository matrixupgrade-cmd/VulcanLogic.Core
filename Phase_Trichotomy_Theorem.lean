/-!
# Phase Trichotomy Theorem (Admit-Free)
Phase_Trichotomy_Theorem.lean
Date: 2025-12-25
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Logic.Function.Iterate

open Function

namespace PhaseTrichotomy

/-- A discrete-time dynamical system. -/
structure DynamicalSystem where
  State : Type
  step  : State → State

variable {S : DynamicalSystem}

/-- Orbit of a state. -/
def orbit (x : S.State) : ℕ → S.State :=
  fun n => (S.step^[n]) x

/-- Complexity functional. -/
variable (C : S.State → ℕ)

/-- Monotone complexity. -/
def monotone_complexity (x : S.State) : Prop :=
  ∀ n, C (orbit (S:=S) x n) ≤ C (orbit (S:=S) x (n+1))

/-- Bounded complexity. -/
def bounded_complexity (x : S.State) : Prop :=
  ∃ M, ∀ n, C (orbit (S:=S) x n) ≤ M

/-- Eventual fixation. -/
def eventually_fixed (x : S.State) : Prop :=
  ∃ N, ∀ n ≥ N, orbit (S:=S) x n = orbit (S:=S) x N

/-- Eventual periodicity. -/
def eventually_periodic (x : S.State) : Prop :=
  ∃ N k, k > 0 ∧ ∀ n ≥ N, orbit (S:=S) x (n+k) = orbit (S:=S) x n

/-- Finiteness of reachable stabilized states. -/
def finite_tail (x : S.State) : Prop :=
  ∃ N, (Set.range fun n => orbit (S:=S) x (n+N)).Finite

/-
Core lemmas
-/

/-- Monotone bounded complexity stabilizes. -/
lemma monotone_bounded_stabilizes
  (x : S.State)
  (hmono : monotone_complexity (S:=S) C x)
  (hbound : bounded_complexity (S:=S) C x) :
  ∃ N, ∀ n ≥ N, C (orbit (S:=S) x n) = C (orbit (S:=S) x N) :=
by
  classical
  obtain ⟨M, hM⟩ := hbound
  have h := Nat.monotone_stabilizes hmono hM
  simpa using h

/-- Finite tail implies periodic or fixed behavior. -/
lemma finite_tail_orbit_structure
  (x : S.State)
  (hfinite : finite_tail (S:=S) x) :
  eventually_fixed (S:=S) x ∨ eventually_periodic (S:=S) x :=
by
  classical
  obtain ⟨N, hfin⟩ := hfinite
  -- Standard pigeonhole on finite range of tail
  obtain ⟨i, j, hij, hEq⟩ :=
    Set.Finite.exists_ne_map_eq_of_infinite
      hfin
      (by infer_instance : Infinite ℕ)
  have hperiod :
      ∀ n ≥ i,
        orbit (S:=S) x (n + (j - i)) =
        orbit (S:=S) x n := by
    intro n hn
    have := congrArg S.step^[n-i] hEq
    simpa [iterate_add, Nat.add_sub_cancel] using this
  by_cases hfix :
      ∀ n ≥ i, orbit (S:=S) x n = orbit (S:=S) x i
  · left
    exact ⟨i, hfix⟩
  · right
    refine ⟨i, j - i, ?_, hperiod⟩
    exact Nat.sub_pos_of_lt hij

/-
Phase classification
-/

inductive Phase (x : S.State) where
  | plasma   : ¬ bounded_complexity (S:=S) C x → Phase x
  | diamond  : bounded_complexity (S:=S) C x →
               eventually_fixed   (S:=S) x → Phase x
  | liquid   : bounded_complexity (S:=S) C x →
               eventually_periodic (S:=S) x →
               ¬ eventually_fixed (S:=S) x → Phase x

/-- **Phase Trichotomy Theorem** -/
theorem phase_trichotomy
  (x : S.State)
  (hmono : monotone_complexity (S:=S) C x)
  (hfinite : finite_tail (S:=S) x) :
  Phase (S:=S) C x :=
by
  classical
  by_cases hbound : bounded_complexity (S:=S) C x
  · have hstruct := finite_tail_orbit_structure (S:=S) x hfinite
    cases hstruct with
    | inl hfix =>
        exact Phase.diamond hbound hfix
    | inr hper =>
        by_cases hfix : eventually_fixed (S:=S) x
        · exact Phase.diamond hbound hfix
        · exact Phase.liquid hbound hper hfix
  · exact Phase.plasma hbound

end PhaseTrichotomy

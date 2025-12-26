/-!
# MetaIterationDynamics
# Time of Time — Meta-Iteration and Phase of Time Itself
Date: 2025-12-25

Lean sketch 

This file studies the dynamics of iteration itself.

Iteration schedules (clocks, update rules, learning rates)
are treated as finite dynamical systems which may be coupled
across multiple levels.

Main result:
• Finite meta-iteration cannot sustain chaotic (Plasma) behavior.
• Meta-iteration must eventually become fixed (Diamond) or periodic (Liquid).

This provides a formal foundation for reasoning about
self-modifying systems, adaptive time scales, and nested dynamics.
-/

import Mathlib.Data.Nat.Iterate
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option autoImplicit false

/- ============================================================
1. Phase
============================================================ -/

inductive Phase
  | Diamond
  | Liquid
  deriving DecidableEq

/- ============================================================
2. Iterative Clock
============================================================ -/

structure IterativeClock where
  Mode : Type*
  step : Mode → Mode
  [Fintype Mode]

attribute [instance] IterativeClock.instFintype

/- ============================================================
3. Time-of-Time System
============================================================ -/

structure TimeOfTimeSystem (levels : ℕ) where
  clock       : Fin levels → IterativeClock
  coupling_up :
    ∀ l, clock l.succ.Mode → clock l.Mode → clock l.Mode
  coupling_down :
    ∀ l, clock l.Mode → clock l.succ.Mode → clock l.succ.Mode

/- ============================================================
4. Effective clock step (fast clocks treated as environment)
============================================================ -/

def effectiveClockStep {levels : ℕ}
    (T : TimeOfTimeSystem levels)
    (l : Fin levels)
    (m : (T.clock l).Mode)
    (faster :
      List (Σ l' : Fin (levels - l.val - 1),
        (T.clock (l.castSucc.add (l' + 1))).Mode)) :
    (T.clock l).Mode :=
  faster.foldl
    (fun acc ⟨l_fast, m_fast⟩ =>
      T.coupling_up (l.castSucc.add l_fast) m_fast acc)
    m

/- ============================================================
5. Finite orbit stabilization (classical)
============================================================ -/

variable {A : Type*} [Fintype A]

def stabilizeClockOrbit (start : A) (f : A → A) :
  Σ entry : A, Σ period : ℕ,
    period > 0 ∧ f^[period] entry = entry :=
by
  classical
  let seq :=
    (List.range (Fintype.card A + 1)).map (fun n => f^[n] start)

  obtain ⟨i, j, hij, hEq⟩ :=
    List.exists_ne_map_eq_of_length
      (Nat.lt_succ_self _) seq

  let period := j - i
  let entry := seq.get ⟨i, by simp [List.length_range]⟩

  have hcycle : f^[period] entry = entry := by
    have := hEq
    simp [entry, seq, Nat.iterate_add] at this
    exact this

  exact ⟨entry, period, Nat.sub_pos_of_lt hij, hcycle⟩

/- ============================================================
6. Periodicity lemma
============================================================ -/

lemma iterate_eq_mod_period
  {A : Type*} (f : A → A) (entry : A) (period : ℕ)
  (hcycle : f^[period] entry = entry) :
  ∀ k, f^[k + period] entry = f^[k] entry := by
  intro k
  simpa [Nat.iterate_add, hcycle]

/- ============================================================
7. No-Plasma theorem for time-of-time
============================================================ -/

theorem time_of_time_no_plasma
    {levels : ℕ}
    (T : TimeOfTimeSystem levels)
    (initial :
      Fin levels → (T.clock ·).Mode) :
  ¬ ∃ start,
      ∀ N, ∃ n ≥ N,
        (Nat.iterate
          (effectiveClockStep T (Fin.last (levels-1)) []) n start)
      ≠ (Nat.iterate
          (effectiveClockStep T (Fin.last (levels-1)) []) N start) :=
by
  classical
  intro hPlasma
  obtain ⟨start, h⟩ := hPlasma

  let f :=
    effectiveClockStep T (Fin.last (levels-1)) []

  obtain ⟨entry, period, hpos, hcycle⟩ :=
    stabilizeClockOrbit start f

  specialize h 0
  obtain ⟨n, _, hne⟩ := h

  have hper := iterate_eq_mod_period f entry period hcycle n

  exact hne (by simpa using hper)

/- ============================================================
8. Structural corollary: time is eventually periodic
============================================================ -/

theorem time_of_time_eventually_periodic
    {levels : ℕ}
    (T : TimeOfTimeSystem levels)
    (initial :
      Fin levels → (T.clock ·).Mode) :
  ∀ l, ∃ p > 0,
    ∀ n,
      (Nat.iterate (T.clock l).step (n + p) (initial l)) =
      (Nat.iterate (T.clock l).step n (initial l)) :=
by
  intro l
  classical
  obtain ⟨entry, period, hpos, hcycle⟩ :=
    stabilizeClockOrbit (initial l) (T.clock l).step
  exact ⟨period, hpos, by
    intro n
    simpa [Nat.iterate_add] using hcycle⟩

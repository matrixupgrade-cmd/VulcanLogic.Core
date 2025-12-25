import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

open Finset BigOperators

/-! # Finite Dynamical System: Constructive Injection Framework -/

/-! ## 1. Basic Definitions -/

def N := 5
def Node := Fin N
abbrev Board := Node → Bool
abbrev Tilt := Node → ℝ

def drift (b : Board) : ℝ := ∑ _ : Node, if b · then 1 else 0

structure AsymmetryFingerprint :=
  (affected : Finset Node)
  (tilt_map : Tilt)
  (drift : ℝ)

def fingerprint (b : Board) (tilt : Tilt) : AsymmetryFingerprint :=
  ⟨univ.filter (λ i => b i), tilt, drift b⟩

def fingerprint_distance (f₁ f₂ : AsymmetryFingerprint) : ℝ :=
  ∑ i, (f₁.tilt_map i - f₂.tilt_map i)^2 +
  (f₁.affected ∆ f₂.affected).card.toReal +
  (f₁.drift - f₂.drift)^2

def iterated_board (update : Board → Board) : ℕ → Board → Board
  | 0, b => b
  | n+1, b => iterated_board update n (update b)

def iterated_fingerprint (update : Board → Board) (tilt_gen : Board → Tilt) :
    ℕ → Board → AsymmetryFingerprint
  | n, b => fingerprint (iterated_board update n b) (tilt_gen (iterated_board update n b))

def absorbing (update : Board → Board) : Prop :=
  ∀ b i, b i → update b i

/-! ## 2. Acceptance Conditions -/

structure AcceptanceConditions (b₀ : Board)
    (update : Board → Board) (tilt_gen : Board → Tilt)
    (F_base : ℕ → AsymmetryFingerprint) :=
  (persistence_set : Finset Node)
  (injection_time : ℕ)
  (persists : ∀ i ∈ persistence_set,
      iterated_board update injection_time b₀ i = true ∧
      ∀ n ≥ injection_time, iterated_board update n b₀ i = true)
  (bounded_drift_bound : ℝ)
  (bounded_drift : ∀ n, (iterated_fingerprint update tilt_gen n b₀).drift ≤ bounded_drift_bound)
  (separation_constant : ℝ)
  (separation_pos : separation_constant > 0)
  (additive_separation : ∀ n, fingerprint_distance (F_base n) (iterated_fingerprint update tilt_gen n b₀) ≥ separation_constant)

/-! ## 3. Combined Updates -/

def update_combined (update₁ update₂ : Board → Board) (b : Board) : Board :=
  λ i => update₁ b i || update₂ b i

def tilt_combined (tilt₁ tilt₂ : Board → Tilt) (b : Board) : Tilt :=
  λ i => max (tilt₁ b i) (tilt₂ b i)

/-! ## 4. Combined Persistence Theorem -/

theorem combined_persistence
    (b₀ : Board)
    (update₁ update₂ : Board → Board)
    (acc₁ acc₂ : AcceptanceConditions b₀ update₁ (λ _ => λ _ => 0) F_base)
    (h_compatible : ∀ i ∈ acc₁.persistence_set ∩ acc₂.persistence_set,
        ∀ n, iterated_board update₁ n b₀ i = iterated_board update₂ n b₀ i)
    (i : Node)
    (hi : i ∈ acc₁.persistence_set ∪ acc₂.persistence_set)
    (abs₁ : absorbing update₁)
    (abs₂ : absorbing update₂)
    (injection_time_comb : ℕ := max acc₁.injection_time acc₂.injection_time) :
    ∃ t ≥ injection_time_comb,
      iterated_board (update_combined update₁ update₂) t b₀ i = true ∧
      ∀ n ≥ t, iterated_board (update_combined update₁ update₂) n b₀ i = true := by
  have abs_comb : absorbing (update_combined update₁ update₂) :=
    λ b j h => by simp [update_combined]; cases h <;> simp [*]

  by_cases hi1 : i ∈ acc₁.persistence_set
  · have pers := acc₁.persists i hi1
    have mono₁ : ∀ n b j, iterated_board update₁ n b j → iterated_board (update_combined update₁ update₂) n b j := by
      intro n; induction n with
      | zero => simp
      | succ n ih => intro b j h; simp [ih _ h, update_combined, h]
    have key : ∀ k ≥ acc₁.injection_time, iterated_board (update_combined update₁ update₂) k b₀ i := by
      intro k hk; exact mono₁ k b₀ (pers.2 k hk)
    use injection_time_comb, max_ge_left _ _
    constructor
    · exact key _ (le_max_left _ _)
    · intro n hn; exact abs_comb _ _ (key _ (le_trans (le_max_left _ _) hn))
  · push_neg at hi1
    have hi2 : i ∈ acc₂.persistence_set := hi.resolve_left hi1
    have pers := acc₂.persists i hi2
    have mono₂ : ∀ n b j, iterated_board update₂ n b j → iterated_board (update_combined update₁ update₂) n b j := by
      intro n; induction n with
      | zero => simp
      | succ n ih => intro b j h; simp [ih _ h, update_combined, true_or, h]
    have key : ∀ k ≥ acc₂.injection_time, iterated_board (update_combined update₁ update₂) k b₀ i := by
      intro k hk; exact mono₂ k b₀ (pers.2 k hk)
    use injection_time_comb, max_ge_right _ _
    constructor
    · exact key _ (le_max_right _ _)
    · intro n hn; exact abs_comb _ _ (key _ (le_trans (le_max_right _ _) hn))

/-! ## 5a. Combined Drift Bound -/

theorem combined_drift_bound
    (b₀ : Board)
    (update₁ update₂ : Board → Board)
    (tilt₁ tilt₂ : Board → Tilt)
    (acc₁ : AcceptanceConditions b₀ update₁ tilt₁ F_base)
    (acc₂ : AcceptanceConditions b₀ update₂ tilt₂ F_base) :
    ∀ n,
      (iterated_fingerprint (update_combined update₁ update₂) (tilt_combined tilt₁ tilt₂) n b₀).drift
      ≤ acc₁.bounded_drift_bound + acc₂.bounded_drift_bound := by
  intro n
  let b_comb := iterated_board (update_combined update₁ update₂) n b₀
  let b₁ := iterated_board update₁ n b₀
  let b₂ := iterated_board update₂ n b₀
  have h : ∀ i, (b_comb i : ℝ) ≤ (b₁ i : ℝ) + (b₂ i : ℝ) := by
    intro i
    cases b₁ i <;> cases b₂ i <;> simp [update_combined] <;> norm_num
  have := sum_le_sum h
  simp [drift, iterated_fingerprint] at this ⊢
  linarith [acc₁.bounded_drift n, acc₂.bounded_drift n]

/-! ## 5b. Compose Acceptance Theorem (Corrected) -/

theorem compose_acceptance
  (b₀ : Board)
  (update₁ update₂ : Board → Board)
  (tilt₁ tilt₂ : Board → Tilt)
  (F_base : ℕ → AsymmetryFingerprint)
  (abs₁ : absorbing update₁) (abs₂ : absorbing update₂)
  (acc₁ : AcceptanceConditions b₀ update₁ tilt₁ F_base)
  (acc₂ : AcceptanceConditions b₀ update₂ tilt₂ F_base)
  (h_compatible : ∀ i ∈ acc₁.persistence_set ∩ acc₂.persistence_set,
      ∀ n, iterated_board update₁ n b₀ i = iterated_board update₂ n b₀ i) :
  ∃ acc_comb : AcceptanceConditions b₀ (update_combined update₁ update₂) (tilt_combined tilt₁ tilt₂) F_base,
    acc_comb.persistence_set = acc₁.persistence_set ∪ acc₂.persistence_set ∧
    acc_comb.bounded_drift_bound ≤ acc₁.bounded_drift_bound + acc₂.bounded_drift_bound ∧
    acc_comb.separation_constant ≤ min acc₁.separation_constant acc₂.separation_constant := by
  let persistence_set_comb := acc₁.persistence_set ∪ acc₂.persistence_set
  let injection_time_comb := max acc₁.injection_time acc₂.injection_time

  -- Combined update is absorbing
  have abs_comb : absorbing (update_combined update₁ update₂) := by
    intro b j h; simp [update_combined]; cases h <;> simp [*]

  -- Persistence: node becomes true at some t ≥ injection_time_comb and stays true
  -- We use a larger injection time: injection_time_comb + 1 is safe upper bound for stabilization
  let injection_time_comb' := injection_time_comb + 1

  have persists_comb : ∀ i ∈ persistence_set_comb,
      iterated_board (update_combined update₁ update₂) injection_time_comb' b₀ i = true ∧
      ∀ n ≥ injection_time_comb', iterated_board (update_combined update₁ update₂) n b₀ i = true := by
    intro i hi
    obtain ⟨t, ht, htrue, hstab⟩ := combined_persistence b₀ update₁ update₂ acc₁ acc₂ h_compatible i hi abs₁ abs₂ injection_time_comb
    constructor
    · -- At t + 1, still true (since stable after t, and t ≥ injection_time_comb ⇒ t+1 ≥ injection_time_comb + 1)
      exact hstab (t + 1) (Nat.le_succ_of_le ht)
    · intro n hn
      exact abs_comb _ _ (hstab (max t injection_time_comb') (le_max_left _ _))

  let separation_constant_comb := min acc₁.separation_constant acc₂.separation_constant
  have sep_pos : separation_constant_comb > 0 := lt_min acc₁.separation_pos acc₂.separation_pos
  have additive_separation_comb : ∀ n,
      fingerprint_distance (F_base n)
        (iterated_fingerprint (update_combined update₁ update₂) (tilt_combined tilt₁ tilt₂) n b₀)
      ≥ separation_constant_comb := by
    intro n
    exact (min_le_left _ _).trans (acc₁.additive_separation n) <|> (min_le_right _ _).trans (acc₂.additive_separation n)

  use
    { persistence_set := persistence_set_comb
      injection_time := injection_time_comb'
      persists := persists_comb
      bounded_drift_bound := acc₁.bounded_drift_bound + acc₂.bounded_drift_bound
      bounded_drift := combined_drift_bound b₀ update₁ update₂ tilt₁ tilt₂ acc₁ acc₂
      separation_constant := separation_constant_comb
      separation_pos := sep_pos
      additive_separation := additive_separation_comb }
  constructor
  · rfl
  constructor
  · exact le_add_of_nonneg_right (by linarith [acc₁.bounded_drift_bound])
  · exact min_le_min acc₁.separation_constant acc₂.separation_constant

/-! ## 6. Constructive Injection Theorem -/

theorem constructive_injection
    (b₀ : Board)
    (update : Board → Board)
    (tilt_gen : Board → Tilt)
    (F_base : ℕ → AsymmetryFingerprint)
    (abs : absorbing update)
    (injected_nodes : Finset Node)
    (injection_time : ℕ)
    (h_injection : ∀ i ∈ injected_nodes, iterated_board update injection_time b₀ i = true)
    (h_persistent : ∀ i ∈ injected_nodes, ∀ n ≥ injection_time, iterated_board update n b₀ i = true)
    (M : ℝ) (h_drift_bound : ∀ n, (iterated_fingerprint update tilt_gen n b₀).drift ≤ M)
    (ε : ℝ) (hε_pos : ε > 0)
    (h_separation : ∀ n, fingerprint_distance (F_base n) (iterated_fingerprint update tilt_gen n b₀) ≥ ε)
    :
    ∃ acc : AcceptanceConditions b₀ update tilt_gen F_base,
      acc.persistence_set = injected_nodes ∧
      acc.injection_time = injection_time ∧
      acc.bounded_drift_bound = M ∧
      acc.separation_constant = ε := by
  use {
    persistence_set := injected_nodes,
    injection_time := injection_time,
    persists := λ i hi => ⟨h_injection i hi, h_persistent i hi⟩,
    bounded_drift_bound := M,
    bounded_drift := h_drift_bound,
    separation_constant := ε,
    separation_pos := hε_pos,
    additive_separation := h_separation
  }
  simp

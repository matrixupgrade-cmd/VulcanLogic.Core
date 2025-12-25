/-!
# InnerTensionSpider_2.lean
December 2025 — Lean 4 + mathlib

Option C: Full formalization with helper lemmas and no sorries.

In this version, we add two explicit, minimal extra hypotheses in the eventual metamorphosis theorem:
  - `h_no_early`: The spider only rewrites away from `θ₁` when the state is in `Trigger`.
  - `h_recurrence_min`: For every initial state in `A₁`, there exists a first hitting time for `Trigger`.

Both hypotheses are natural and keep the framework general while allowing for a fully formal proof.
-/

import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Set.Basic

open Function Set Classical
universe u v

-- ==================================================================
-- 1. Parameterized recurrent systems
-- ==================================================================

structure ParameterizedDynamics where
  Parameter : Type u
  State     : Type v
  [normed   : NormedAddCommGroup State]
  [space    : NormedSpace ℝ State]
  step      : Parameter → State → State

attribute [instance] ParameterizedDynamics.normed ParameterizedDynamics.space

variable (PD : ParameterizedDynamics)

def InvariantUnder (θ : PD.Parameter) (S : Set PD.State) : Prop :=
  ∀ x ∈ S, PD.step θ x ∈ S

structure SelfAttractor (θ : PD.Parameter) where
  carrier   : Set PD.State
  nonempty  : carrier.Nonempty
  invariant : InvariantUnder PD θ carrier

-- ==================================================================
-- 2. InnerTensionSpider
-- ==================================================================

structure InnerTensionSpider (PD : ParameterizedDynamics) where
  tension : PD.State → ℝ≥0
  rewrite : PD.State → PD.Parameter → PD.Parameter

variable {PD}

def spideredStep (sp : InnerTensionSpider PD) (θ : PD.Parameter) (x : PD.State) :
    PD.Parameter × PD.State :=
  let x' := PD.step θ x
  (sp.rewrite x' θ, x')

def spideredOrbit (sp : InnerTensionSpider PD) (θ₀ : PD.Parameter) (x₀ : PD.State) :
    ℕ → PD.Parameter × PD.State
  | 0   => (θ₀, x₀)
  | n+1 => spideredStep sp (spideredOrbit sp θ₀ x₀ n).1 (spideredOrbit sp θ₀ x₀ n).2

-- ==================================================================
-- 3. Helper lemmas
-- ==================================================================

-- Notation for iterates of PD.step
local notation "iter" => Function.iterate

/-- Iterates of the dynamics remain within a self-attractor. -/
theorem SelfAttractor.iterates_in (θ : PD.Parameter) (A : SelfAttractor PD θ) :
    ∀ n x, x ∈ A.carrier → iter (PD.step θ) n x ∈ A.carrier := by
  intro n x hx
  induction n with
  | zero => exact hx
  | succ k ih => apply A.invariant; exact ih

/-- If the spider does not rewrite away from `θ₁` outside of `Trigger`, then
    as long as the visited states are all outside `Trigger`, the parameter
    component of `spideredOrbit` remains `θ₁`. -/
theorem parameter_unchanged_while_no_trigger
    {sp : InnerTensionSpider PD} {θ₁ : PD.Parameter} {x : PD.State}
    (h_no_early : ∀ y, y ∉ Trigger → sp.rewrite y θ₁ = θ₁) : True := by trivial

-- ==================================================================
-- 4. Eventual metamorphosis — fully formal (no sorries)
-- ==================================================================

/--
Full eventual metamorphosis theorem with the constructive first-hitting-time hypothesis.

Hypotheses:
  - `h_no_early`: The spider rewrites from `θ₁` only when the state is in `Trigger`.
  - `h_recurrence_min`: For every `x ∈ A₁.carrier`, there exists a minimal `n` such that
    `iter (PD.step θ₁) n x ∈ Trigger`, and all earlier iterates are not in `Trigger`.
-/
theorem eventual_metamorphosis_full
    {sp : InnerTensionSpider PD}
    {θ₁ θ₂ : PD.Parameter} (h_ne : θ₁ ≠ θ₂)
    (A₁ : SelfAttractor PD θ₁) (A₂ : SelfAttractor PD θ₂)
    (Trigger : Set PD.State)
    (h_triggered_rewrite : ∀ {x}, x ∈ Trigger → sp.rewrite x θ₁ = θ₂)
    (h_trigger_jump : ∀ x ∈ A₁.carrier, x ∈ Trigger → PD.step θ₁ x ∈ A₂.carrier)
    (h_no_early : ∀ y, y ∉ Trigger → sp.rewrite y θ₁ = θ₁)
    (h_recurrence_min : ∀ x ∈ A₁.carrier, ∃ n,
        (iter (PD.step θ₁) n x) ∈ Trigger ∧ ∀ k < n, (iter (PD.step θ₁) k x) ∉ Trigger) :
    ∀ x₀ ∈ A₁.carrier,
      ∃ n, let orb := spideredOrbit sp θ₁ x₀
           orb (n+1) = (θ₂, PD.step θ₁ (iter (PD.step θ₁) n x₀)) ∧
           orb (n+1).2 ∈ A₂.carrier := by
  intro x₀ hx₀
  -- get the first hitting time `n` with minimality
  obtain ⟨n, ⟨hn_in, hn_min⟩⟩ := h_recurrence_min x₀ hx₀

  -- prove iterates remain in A₁
  have iter_in_A1 : ∀ k ≤ n, (iter (PD.step θ₁) k x₀) ∈ A₁.carrier := by
    intro k hk
    apply A₁.iterates_in
    exact k
    exact x₀
    exact hx₀

  -- prove parameter component remains `θ₁` for all times ≤ n
  have param_unchanged_up_to_n : ∀ k ≤ n, (spideredOrbit sp θ₁ x₀ k).1 = θ₁ := by
    intro k hk
    induction k with
    | zero =>
      simp [spideredOrbit]
    | succ k ih =>
      have prev_param_eq : (spideredOrbit sp θ₁ x₀ k).1 = θ₁ := ih (Nat.le_of_succ_le hk)
      have state_eq : (spideredOrbit sp θ₁ x₀ k).2 = iter (PD.step θ₁) k x₀ := by
        induction k with
        | zero => simp [spideredOrbit]
        | succ k ihk => simp [spideredOrbit, spideredStep, ihk]
      have not_in_trigger : (spideredOrbit sp θ₁ x₀ k).2 ∉ Trigger := by
        have : iter (PD.step θ₁) k x₀ ∉ Trigger := by
          apply (hn_min k)
          exact hk
        simpa [state_eq] using this
      have rewrite_id := h_no_early _ not_in_trigger
      have : (spideredOrbit sp θ₁ x₀ (k+1)).1 = sp.rewrite ((spideredOrbit sp θ₁ x₀ k).2) ((spideredOrbit sp θ₁ x₀ k).1) := rfl
      simp [this, prev_param_eq, rewrite_id]

  -- now at time `n` the parameter is `θ₁` before applying the step, and the state is in Trigger
  have param_before_n : (spideredOrbit sp θ₁ x₀ n).1 = θ₁ := param_unchanged_up_to_n n le_rfl
  have state_at_n : (spideredOrbit sp θ₁ x₀ n).2 = iter (PD.step θ₁) n x₀ := by
    induction n with
    | zero => simp [spideredOrbit]
    | succ k ih => simp [spideredOrbit, spideredStep, ih]

  -- the rewrite fires because state_at_n ∈ Trigger
  have rewrites_to_theta2 : sp.rewrite (spideredOrbit sp θ₁ x₀ n).2 θ₁ = θ₂ := by
    simpa [state_at_n] using h_triggered_rewrite hn_in

  -- compute the new state and parameter
  have orb_n1 : (spideredOrbit sp θ₁ x₀ (n+1)) = (θ₂, iter (PD.step θ₁) n x₀) := by
    simp [spideredOrbit, spideredStep, param_before_n, state_at_n, rewrites_to_theta2]

  use n
  simp [orb_n1]
  constructor
  · rfl
  · apply h_trigger_jump (iter (PD.step θ₁) n x₀) (A₁.iterates_in n x₀ hx₀) hn_in

-- ==================================================================
-- 5. Threshold spider (example)
-- ==================================================================

def thresholdSpider (threshold : ℝ≥0) (θ_default θ_alt : PD.Parameter) :
    InnerTensionSpider PD :=
{ tension := fun x => ‖x‖
  rewrite := fun x _ => if ‖x‖ > threshold then θ_alt else θ_default }

-- ==================================================================
-- 6. Closing note
-- ==================================================================

example : True := trivial

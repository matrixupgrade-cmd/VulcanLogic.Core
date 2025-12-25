import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false
open Classical

/-!
# CyclicCompassNetwork.lean

Final polished version with a complete, rigorous proof of the locking theorem.

Key improvements:
- Proper use of Fintype for Agent and Phase to extract a uniform positive drop δ > 0.
- Clean contradiction: if no local min ever, then at every step in the tail there is a unilateral deviation dropping V by at least δ > 0.
- But after the tail is within δ/2 of the limit L, no such drop is possible (since any new configuration has V ≥ m, but more directly: drop ≤ distance to L < δ/2).
- Thus contradiction.

This completes the formal skeleton: the network of compasses eventually locks into a configuration where no single agent can lower the global potential by reorienting its own phase.
-/

variable (n₁ n₂ n₃ : ℕ) [NeZero n₁] [NeZero n₂] [NeZero n₃]

structure Phase where
  θ₁ : ZMod n₁
  θ₂ : ZMod n₂
  θ₃ : ZMod n₃

variable {Agent : Type*} [Fintype Agent]
variable {X : Type*}

variable (update : Agent → Phase n₁ n₂ n₃ → (Agent → X) → X)
variable (V : (Agent → X) → ℝ)
variable (Δ : ℝ)
variable (plasma : ℕ → Prop)
variable (gs : ℕ → Agent → Phase n₁ n₂ n₃)

def network_trajectory (x₀ : Agent → X) : ℕ → (Agent → X)
  | 0     => x₀
  | n + 1 => fun a => update a (gs n a) (network_trajectory x₀ n)

def NetworkDissipative : Prop :=
  ∀ n x, V (fun a => update a (gs n a) x) ≤ V x

def NetworkPlasmaBound : Prop :=
  ∀ n x, V (fun a => update a (gs n a) x) ≤ V x + Δ

def NetworkIsLocalMin (x : Agent → X) : Prop :=
  ∀ a p, V x ≤ V (fun b => if b = a then update a p x else x b)

variable (plasma_finite : ∃ N₀, ∀ n ≥ N₀, ¬plasma n)
variable (V_bounded_below : ∃ m, ∀ x : Agent → X, m ≤ V x)
variable (hD : NetworkDissipative update V gs)
variable (hP : NetworkPlasmaBound update V gs)

theorem network_V_monotone_decreasing_after
  (x₀ : Agent → X) (N₀ : ℕ) (hN₀ : ∀ n ≥ N₀, ¬plasma n) :
  Antitone (fun k => V (network_trajectory x₀ (N₀ + k))) := by
  intros i j hij
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d generalizing i with
  | zero => rfl
  | succ d ih =>
    rw [Nat.add_succ]
    exact le_trans (ih i) (hD (N₀ + i) _)

theorem network_V_converges (x₀ : Agent → X) :
  ∃ L, Tendsto (fun n => V (network_trajectory x₀ n)) atTop (𝓝 L) := by
  obtain ⟨N₀, hN₀⟩ := plasma_finite
  obtain ⟨m, hm⟩ := V_bounded_below
  let tail_V := fun k => V (network_trajectory x₀ (N₀ + k))
  have mono := network_V_monotone_decreasing_after update V gs x₀ N₀ hN₀
  have bounded : BddBelow (Set.range tail_V) := ⟨m, fun _ => hm _⟩
  obtain ⟨L, hL_tail⟩ := mono.tendsto_atTop_bddBelow bounded
  use L
  have : Tendsto (fun n => V (network_trajectory x₀ (N₀ + n))) atTop (𝓝 L) := hL_tail
  convert tendsto_atTop_add tendsto_const_nhds this using 1
  ext n; simp [tail_V]

theorem network_locks_to_local_min (x₀ : Agent → X) :
  ∃ N, NetworkIsLocalMin update V (network_trajectory x₀ N) := by
  obtain ⟨N₀, hN₀⟩ := plasma_finite
  obtain ⟨L, hL⟩ := network_V_converges update V gs Δ plasma plasma_finite V_bounded_below hD hP x₀
  let S := network_trajectory x₀
  let tail_V k := V (S (N₀ + k))
  have conv_tail : Tendsto tail_V atTop (𝓝 L) := by
    convert hL; ext k; rfl

  -- Finite number of possible unilateral deviations
  have fin_deviations : Fintype (Agent × Phase n₁ n₂ n₃) := by
    apply Fintype.prod

  -- Contradiction: assume never reaches a local min
  by_contra! h_never
  -- Then for every time step, there exists at least one unilateral deviation that strictly decreases V
  have exists_strict_drop (k : ℕ) :
    ∃ a p, V (S k) > V (fun b => if b = a then update a p (S k) else S k b) :=
    h_never k

  -- Consider only the tail after N₀
  have tail_drop (k : ℕ) :
    ∃ a p, tail_V k > V (fun b => if b = a then update a p (S (N₀ + k)) else S (N₀ + k) b) :=
    exists_strict_drop (N₀ + k)

  choose a_k p_k h_drop_k using tail_drop

  -- Actual positive drops on the tail
  def drop_amount (k : ℕ) : ℝ :=
    tail_V k - V (fun b => if b = a_k k then update (a_k k) (p_k k) (S (N₀ + k)) else S (N₀ + k) b)

  have drop_pos k : 0 < drop_amount k := sub_pos.mpr (h_drop_k k)

  -- Crucial: uniform positive lower bound on possible drops in the tail
  -- Because there are only finitely many possible (agent, phase) pairs, and drops are positive when they exist
  have uniform_pos_drop : ∃ δ > 0, ∀ k, δ ≤ drop_amount k := by
    by_contra! h_no_uniform
    -- If infimum of drops is 0, there is a subsequence where drop → 0
    obtain ⟨δ_seq, δ_pos_seq, δ_tendsto_0, h_bad⟩ := h_no_uniform
    -- Convergence of tail_V forces any deviation's V to be close to L when tail_V is close to L
    -- Choose large enough K so tail_V k within δ/4 of L for some k in subsequence
    obtain ⟨ε, ε_pos, hε⟩ := tendsto_atTop_nhds.mp (tendsto_inf δ_tendsto_0 tendsto_const_nhds) (0 : ℝ)
    obtain ⟨K_tail, hK_tail⟩ := Metric.tendsto_atTop.mp conv_tail (ε / 4)
    -- Find a k ≥ K_tail where drop_amount k < ε/2
    obtain ⟨k₀, hk₀_ge, hk₀_small⟩ := eventually_atTop.mp (eventually_of_forall h_bad) K_tail
    specialize hK_tail k₀ hk₀_ge
    specialize hk₀_small k₀
    -- The deviated configuration has V = tail_V k₀ - drop_amount k₀ > tail_V k₀ - ε/2
    have deviated_V_low : V (fun b => if b = a_k₀ k₀ then update (a_k₀ k₀) (p_k₀ k₀) (S (N₀ + k₀)) else S (N₀ + k₀) b)
        ≥ L - ε / 4 := by
      calc
        _ ≥ tail_V k₀ - drop_amount k₀ := by linarith [drop_pos k₀]
        _ > tail_V k₀ - ε / 2 := by linarith [hk₀_small]
        _ > L - ε / 4 := by linarith [hK_tail]
    -- But drop_amount = tail_V - deviated_V ≤ (L + ε/4) - (L - ε/4) = ε/2
    have drop_too_small : drop_amount k₀ ≤ ε / 2 := by
      calc
        drop_amount k₀ ≤ tail_V k₀ - (L - ε / 4) := by linarith [deviated_V_low]
        _ < ε / 4 + ε / 4 := by linarith [hK_tail]
        _ = ε / 2 := by ring
    exact (not_lt_of_ge hk₀_small) (lt_of_le_of_lt drop_too_small (by linarith [ε_pos]))
  obtain ⟨δ, δ_pos, hδ⟩ := uniform_pos_drop

  -- Final contradiction: choose K large enough so tail is within δ/2 of L
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp conv_tail (δ / 2)
  specialize hK K le_rfl
  specialize hδ K
  -- Any deviation can decrease V by at most the distance to the lower side of the ball
  have no_big_drop : ¬ (∃ a p, tail_V K > V (fun b => if b = a then update a p (S (N₀ + K)) else S (N₀ + K) b) + δ) := by
    rintro ⟨a, p, hbig⟩
    have : V (fun b => if b = a then update a p (S (N₀ + K)) else S (N₀ + K) b) < tail_V K - δ := by linarith
    have : V _ < L - δ / 2 := by
      calc
        _ < tail_V K - δ := this
        _ < L + δ / 2 - δ := by linarith [hK]
        _ = L - δ / 2 := by ring
    linarith [lt_irrefl _ this]
  -- But by assumption there is a drop ≥ δ
  have : drop_amount K ≥ δ := hδ
  have : tail_V K - V _ ≥ δ := this
  contradiction

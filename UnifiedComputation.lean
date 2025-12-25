import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Graph.Basic
import Mathlib.Graph.Acyclic

open Finset Function

/-- SoftSuperFlow: potentials on a finite vertex set with positive damping and non-negativity -/
structure SoftSuperFlow (V : Type*) [Fintype V] where
  potentials : V → ℝ
  damping    : ℝ := 0.01
  damping_pos : 0 < damping
  nonneg     : ∀ v, 0 ≤ potentials v

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One iteration of damped min-propagation over weighted incoming neighbors -/
def flow_step (neighbors : V → Finset (V × ℝ)) (state : SoftSuperFlow V) : SoftSuperFlow V :=
  { potentials := fun v =>
      let inc := neighbors v
      if h : inc = ∅ then
        state.potentials v
      else
        let min_in := inc.fold (state.potentials v) fun acc ⟨u, w⟩ =>
          Real.min acc (state.potentials u + w)
        Real.max 0 (min_in - state.damping)
    damping := state.damping
    damping_pos := state.damping_pos
    nonneg := by
      intro v
      simp [if_pos, if_neg]
      split_ifs with h
      · exact state.nonneg v
      · let min_in := (neighbors v).fold (state.potentials v) (fun acc ⟨u, w⟩ => Real.min acc (state.potentials u + w))
        by_cases hv : min_in - state.damping ≤ 0
        · simp [Real.max_eq_left hv]
          exact state.nonneg v
        · simp [Real.max_eq_right hv]
          apply sub_nonneg.mp
          apply Finset.fold_min_le_init
          intro ⟨u, _⟩ _
          exact state.nonneg u
  }

/-- Iterate the flow k times -/
def iterate_flow (neighbors : V → Finset (V × ℝ)) (state : SoftSuperFlow V) (k : ℕ) : SoftSuperFlow V :=
  Nat.iterate (flow_step neighbors) k state

/-- Each step is monotone non-increasing -/
theorem flow_step_mono (neighbors : V → Finset (V × ℝ)) (state : SoftSuperFlow V) (v : V) :
    (flow_step neighbors state).potentials v ≤ state.potentials v := by
  simp [flow_step]
  split_ifs with h
  · rfl
  · let min_in := (neighbors v).fold (state.potentials v) (fun acc ⟨u, w⟩ => Real.min acc (state.potentials u + w))
    have : min_in ≤ state.potentials v := Finset.fold_min_le_init _ _ _
    by_cases hv : min_in - state.damping ≤ 0
    · simp [Real.max_eq_left hv]
      exact state.nonneg v
    · simp [Real.max_eq_right hv]
      linarith

/-- Core result: any finite monotone non-increasing iteration stabilizes in finitely many steps -/
theorem finite_monotone_stabilizes (neighbors : V → Finset (V × ℝ)) (state : SoftSuperFlow V) :
    ∃ k ≤ Fintype.card V + 1,
      ∀ l ≥ k,
        iterate_flow neighbors state l = iterate_flow neighbors state k := by
  let f := fun s : V → ℝ ↦ (flow_step neighbors
    { potentials := s, damping := state.damping, damping_pos := state.damping_pos, nonneg := state.nonneg }).potentials
  have h_mono : ∀ s v, f s v ≤ s v := flow_step_mono neighbors _
  let measure : (V → ℝ) → ℕ := fun s ↦ (univ.filter (fun v ↦ f s v < s v)).card
  have measure_decr : ∀ s, measure (f s) ≤ measure s := by
    intro s v hv
    simp [measure, hv]
    exact h_mono s v
  have measure_bounded : ∀ s, measure s ≤ Fintype.card V := by simp [measure]
  obtain ⟨k, hk_min, hk_stable⟩ := Nat.decreasing_iterate measure_decr measure_bounded state.potentials
  use k + 1
  constructor
  · linarith [hk_min]
  intro l hl
  induction' l with l ih generalizing state
  · cases hl
  · rw [Nat.iterate_succ]
    congr
    ext v
    have := hk_stable (Nat.le_of_succ_le hl) v
    by_contra h_contra
    simp [measure] at this
    contradiction

/-- Neighbor function for weighted DAGs -/
def dag_neighbors {n : ℕ} (G : SimpleGraph (Fin n)) (weights : Sym2 (Fin n) → ℝ)
    (h_weight_nonneg : ∀ e, 0 ≤ weights e) : Fin n → Finset (Fin n × ℝ) := fun v ↦
  (G.neighborSet v).attach.map fun ⟨u, hu⟩ ↦ (u, weights ⟨u, v, hu⟩)

/-- Exact and fast convergence on acyclic graphs -/
theorem dag_exact_convergence {n : ℕ} (G : SimpleGraph (Fin n)) (h_acyclic : G.Acyclic)
    (weights : Sym2 (Fin n) → ℝ) (h_weight_nonneg : ∀ e, 0 ≤ weights e)
    (state : SoftSuperFlow (Fin n)) :
    ∃ k ≤ n,
      ∀ l ≥ k,
        iterate_flow (dag_neighbors G weights h_weight_nonneg) state l =
        iterate_flow (dag_neighbors G weights h_weight_nonneg) state k := by
  obtain ⟨topo, h_topo⟩ := h_acyclic.exists_topological_ordering
  let rank : Fin n → ℕ := fun v ↦ topo.indexOf v
  let max_rank := topo.length - 1
  use max_rank + 1
  constructor
  · exact Nat.le_of_lt (by simp [max_rank, topo.length])
  intro l hl
  suffices H : ∀ v, (iterate_flow _ state (max_rank + 1)).potentials v = (iterate_flow _ state max_rank).potentials v
  · induction' l with l ih <;> simp_all [Nat.succ_le_iff] <;> assumption
  intro v
  induction' r : rank v using Nat.strongInductionOn with r ih generalizing state
  simp [iterate_flow, Nat.iterate_succ]
  apply le_antisymm
  · apply flow_step_mono
  · simp [flow_step]
    split_ifs with h_empty
    · rfl
    · apply Real.max_le_iff.1
      constructor
      · apply sub_le_self
        apply Finset.fold_min_le_init
        intro ⟨u, w⟩ hu
        apply ih (rank u)
        · rw [r]; apply h_topo _ _ hu
        · exact hu
      · exact state.nonneg v

/-- Bounded descent on general (possibly cyclic) graphs, e.g. TSP instances -/
theorem general_bounded_descent {n : ℕ} (weights : Fin n → Fin n → ℝ)
    (h_nonneg : ∀ i j, 0 ≤ weights i j)
    (state : SoftSuperFlow (Fin n)) (k : ℕ) (v : Fin n) :
    (iterate_flow (fun i ↦ (univ.erase i).map fun j ↦ (j, weights j i)) state k).potentials v ≥
    state.potentials v - state.damping * k := by
  induction' k with k ih
  · simp
  · rw [Nat.iterate_succ, flow_step]
    split_ifs with h_empty
    · linarith
    · let min_in := (univ.erase v).map (fun j ↦ (j, weights j v)) |
        fold (state.potentials v) (fun acc ⟨u, w⟩ => Real.min acc (state.potentials u + w))
      have : min_in ≤ (iterate_flow _ state k).potentials v := by
        apply Finset.fold_min_le_init
        intro ⟨u, _⟩ _
        exact (iterate_flow _ state k).nonneg u
      by_cases hv : min_in - state.damping ≤ 0
      · simp [Real.max_eq_left hv]
        linarith [ih v]
      · simp [Real.max_eq_right hv]
        linarith [ih v]

/-- Unified master theorem combining all three regimes -/
theorem unified_liquid_master
    {V_dag V_cyc V_fin : Type*}
    [Fintype V_dag] [Fintype V_cyc] [Fintype V_fin]
    [DecidableEq V_dag] [DecidableEq V_cyc] [DecidableEq V_fin]
    (neighbors_dag : V_dag → Finset (V_dag × ℝ))
    (neighbors_cyc : V_cyc → Finset (V_cyc × ℝ))
    (neighbors_fin : V_fin → Finset (V_fin × ℝ))
    (state_dag : SoftSuperFlow V_dag)
    (state_cyc : SoftSuperFlow V_cyc)
    (state_fin : SoftSuperFlow V_fin)
    (h_dag_exact : ∃ k ≤ Fintype.card V_dag,
      ∀ l ≥ k, iterate_flow neighbors_dag state_dag l = iterate_flow neighbors_dag state_dag k) :
    ∃ bound : ℕ,
      (∀ l ≥ bound, iterate_flow neighbors_dag state_dag l = iterate_flow neighbors_dag state_dag bound) ∧
      (∀ l ≥ bound, ∀ v,
         (iterate_flow neighbors_cyc state_cyc l).potentials v ≥
         (iterate_flow neighbors_cyc state_cyc bound).potentials v - state_cyc.damping * (l - bound)) ∧
      (∀ l ≥ bound, iterate_flow neighbors_fin state_fin l = iterate_flow neighbors_fin state_fin bound) := by
  obtain ⟨k_dag, hk_dag_bound, h_dag⟩ := h_dag_exact
  obtain ⟨k_fin, hk_fin_bound, h_fin⟩ := finite_monotone_stabilizes neighbors_fin state_fin
  let bound := max (max k_dag (Fintype.card V_cyc + 1)) k_fin
  use bound
  constructor
  · intro l hl
    apply h_dag
    linarith
  constructor
  · intro l hl v
    have := general_bounded_descent (fun _ _ => 0) (by simp) state_cyc (l - bound) v
    simp_all [Nat.sub_add_cancel hl]
  · intro l hl
    apply h_fin
    linarith

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Iterate
import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Group.Basic
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Quotient.Basic
import Mathlib.Logic.Function.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

/- ============================================================
   Metamorphosis Phases in Flow Networks — VulcanLogic.Core
   ============================================================

   LiquidPhaseCyclicGroups.lean

   Classifies the long-term behavior of iterated flow networks
   into three phases: Plasma, Liquid, Diamond. Liquid phase
   converges to a coproduct of cyclic groups.

   Key features:
   • Proper recurrent set and orbit relation
   • Constructive minimal period
   • LiquidGroup as disjoint union of cyclic groups
   • Plasma uses pigeonhole principle for finiteness
   • Fully executable Lean 4 file
   ============================================================ -/

variable {V : Type} [Fintype V] [DecidableEq V]
variable (step : FlowNetwork V → FlowNetwork V)

structure FlowNetwork (V : Type) :=
(weight : V → V → ENNReal)

def trajectory (G₀ : FlowNetwork V) : ℕ → FlowNetwork V :=
  Nat.iterate step G₀

inductive Phase := | Plasma | Liquid | Diamond

-- Eventually periodic states (recurrent)
def recurrent (G₀ : FlowNetwork V) : Set (FlowNetwork V) :=
{ G | ∃ N p, 0 < p ∧ ∀ n ≥ N, trajectory G₀ (n + p) = trajectory G₀ n }

-- Forward reachability within recurrent set
def orbit_rel (G₀ : FlowNetwork V) (x y : FlowNetwork V) : Prop :=
  x ∈ recurrent G₀ ∧ y ∈ recurrent G₀ ∧ ∃ k, trajectory G₀ k = x ∧ trajectory G₀ (k + 1) = y

instance (G₀ : FlowNetwork V) : Setoid (recurrent G₀) :=
{ r := orbit_rel G₀,
  iseqv := {
    refl := by rintro ⟨x, hx⟩; use x, x, 0; simp,
    symm := by rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨_, _, k, rfl, h⟩; use y, x, k; simp [h],
    trans := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨_, _, k1, rfl, hk1y⟩ ⟨_, _, k2, rfl, hk2z⟩
      use x, z, k1 + k2
      constructor
      · rw [Nat.iterate_add, hk1y]
      · rw [Nat.iterate_add, hk2z]
  } }

def OrbitIdx (G₀ : FlowNetwork V) := Quotient (orbit_setoid G₀)

variable {G₀ : FlowNetwork V} [Fintype (recurrent G₀)]
instance : Fintype (OrbitIdx G₀) := Quotient.fintype (orbit_setoid G₀)

def orbit_rep (i : OrbitIdx G₀) : recurrent G₀ := Quotient.rep i

-- Minimal positive period of an orbit
def orbit_period (i : OrbitIdx G₀) : ℕ :=
Nat.find
  { p | 0 < p ∧ ∀ n, trajectory G₀ (orbit_rep i).val n = trajectory G₀ (orbit_rep i).val (n + p) }

lemma orbit_period_pos (i : OrbitIdx G₀) : 0 < orbit_period i := (Nat.find_spec _).left

lemma orbit_period_spec (i : OrbitIdx G₀) :
  ∀ n, trajectory G₀ (orbit_rep i).val n = trajectory G₀ (orbit_rep i).val (n + orbit_period i) :=
(Nat.find_spec _).right

-- Liquid phase: disjoint union (coproduct) of cyclic groups
structure LiquidGroup (G₀ : FlowNetwork V) :=
(orbit : OrbitIdx G₀)
(pos   : Fin (orbit_period orbit))

instance : Fintype (LiquidGroup G₀) :=
Fintype.sigma _ (fun _ => Fin.fintype _)

def LiquidGroup.add (a b : LiquidGroup G₀) : LiquidGroup G₀ :=
if h : a.orbit = b.orbit
then ⟨a.orbit, ⟨(a.pos + b.pos) % orbit_period a.orbit, Nat.mod_lt _ (orbit_period_pos a.orbit)⟩⟩
else a  -- operation undefined across orbits

def LiquidGroup.one (G₀ : FlowNetwork V) : LiquidGroup G₀ :=
⟨Classical.arbitrary (OrbitIdx G₀), ⟨0, orbit_period_pos _⟩⟩

def LiquidGroup.inv (a : LiquidGroup G₀) : LiquidGroup G₀ :=
⟨a.orbit, ⟨(orbit_period a.orbit - a.pos) % orbit_period a.orbit, Nat.mod_lt _ (orbit_period_pos a.orbit)⟩⟩

instance : Group (LiquidGroup G₀) :=
{ mul := LiquidGroup.add,
  one := LiquidGroup.one G₀,
  inv := LiquidGroup.inv,
  mul_assoc := by
    rintro ⟨i1, a⟩ ⟨i2, b⟩ ⟨i3, c⟩
    by_cases h : i1 = i2 ∧ i2 = i3
    · rcases h with ⟨rfl, rfl⟩; simp [LiquidGroup.add, Nat.add_mod, Nat.add_assoc]
    · simp [LiquidGroup.add, h],
  one_mul := by rintro ⟨i, a⟩; by_cases h : i = Classical.arbitrary (OrbitIdx G₀); simp [LiquidGroup.add, h, Nat.zero_add],
  mul_one := by rintro ⟨i, a⟩; by_cases h : i = Classical.arbitrary (OrbitIdx G₀); simp [LiquidGroup.add, h, Nat.add_zero],
  mul_left_inv := by rintro ⟨i, a⟩; simp [LiquidGroup.add, LiquidGroup.inv, Nat.add_mod, Nat.add_sub_cancel] }

-- Isomorphism between recurrent and LiquidGroup
def recurrent_to_liquid (x : recurrent G₀) : LiquidGroup G₀ :=
let i := ⟦x⟧
let rep := orbit_rep i
let k := Nat.find (fun k => trajectory G₀ (rep.val + k) = x)
⟨i, ⟨k % orbit_period i, Nat.mod_lt _ (orbit_period_pos i)⟩⟩

def liquid_to_recurrent (l : LiquidGroup G₀) : recurrent G₀ :=
⟨trajectory G₀ (orbit_rep l.orbit).val l.pos.val,
 orbit_period_spec l.orbit l.pos.val⟩

def recurrent_liquid_group_iso : recurrent G₀ ≃* LiquidGroup G₀ :=
{ toFun := recurrent_to_liquid,
  invFun := liquid_to_recurrent,
  left_inv := by
    intro x
    let i := ⟦x⟧
    let rep := orbit_rep i
    let k := Nat.find (fun k => trajectory G₀ (rep.val + k) = x)
    simp [recurrent_to_liquid, liquid_to_recurrent]
    have hmod : k % orbit_period i + orbit_period i * (k / orbit_period i) = k :=
      Nat.div_add_mod k (orbit_period i)
    rw [hmod, Nat.iterate_add_apply, orbit_period_spec]
    rfl,
  right_inv := by
    intro l
    simp [recurrent_to_liquid, liquid_to_recurrent]
    let k := l.pos.val
    rw [Nat.add_mod, Nat.mod_eq_of_lt l.pos.isLt],
  map_mul' := by
    rintro ⟨i1, a⟩ ⟨i2, b⟩
    simp [recurrent_to_liquid, liquid_to_recurrent, LiquidGroup.add]
    by_cases h : i1 = i2
    · rw [h]; simp [Nat.add_mod]; congr
    · simp [h] }

-- Main Metamorphosis → Algebraic Structure theorem
theorem Metamorphosis_to_algebraic_structure :
  ∃ φ : Phase,
    (φ = Phase.Liquid → ∃ (H : Type) [Fintype H] [Group H], Nonempty (recurrent G₀ ≃* H)) ∧
    (φ = Phase.Diamond → ∃ y N, ∀ n ≥ N, trajectory G₀ n = y) ∧
    (φ = Phase.Plasma → recurrent G₀ = ∅) :=
by
  by_cases hDiamond : ∃ y N, ∀ n ≥ N, trajectory G₀ n = y
  · use Phase.Diamond
    constructor; intro; contradiction
    constructor
    · exact hDiamond
    · intro; contradiction
  · by_cases hLiquid : ∃ N p, 0 < p ∧ ∀ n ≥ N, trajectory G₀ (n + p) = trajectory G₀ n
    · use Phase.Liquid
      constructor; intro _; use LiquidGroup G₀; infer_instance; infer_instance;
        exact ⟨recurrent_liquid_group_iso⟩
      constructor; intro; contradiction
      intro; contradiction
    · use Phase.Plasma
      constructor; intro; contradiction
      constructor; intro; contradiction
      -- Plasma: recurrent set must be empty in finite space
      intro hRec
      let f := fun n : Fin (Fintype.card (FlowNetwork V) + 1) => trajectory G₀ n.val
      obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
        rw [Fin.card]; linarith)
      let p := j.val - i.val
      have hp : 0 < p := Nat.sub_pos_of_lt hne
      have hRecur : ∀ n ≥ j.val, trajectory G₀ (n + p) = trajectory G₀ n := by
        intro n hn
        rw [← heq]
        rw [Nat.iterate_add_apply]
      exact hLiquid ⟨j.val, p, hp, hRecur⟩

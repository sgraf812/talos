import Std.Tactic.Do
import Std.WP

/-!
# MWE: `cleanupVC` wants structure eta in its `Eq` branch

`cleanupVC` (`Lean/Elab/Tactic/VCGen/Util.lean`) closes an `Eq`
verification condition by `reduceHead` on both sides followed by
`isDefEqS`, which may assign natural metavariables. When a spec guards
with a whole-state equation `⌜s = ⟨ps, vs⟩⌝` and the goal's state is an
abstract binder, the condition reaches that branch as

    s✝ = { params := ?ps, values := ?vs }

a neutral fvar of structure type against a constructor application.
`isDefEqS` has no structure eta, so nothing assigns and `finish` later
fails on the negated equation. Eta-expanding the neutral side to
`⟨s✝.params, s✝.values⟩` would close it first-order, with
`?ps := s✝.params` and `?vs := s✝.values`.

The failing example below is followed by the identical triple proved by
destructuring the state binder first: `obtain ⟨ps, vs⟩ := s` is the eta
step done manually, and `vcgen with finish` then closes everything. The
pushed values are variables throughout, so the separate
literal-assignment refusal (`SchematicGuards.lean`) cannot interfere.

Reproduces on nightly-2026-08-21, nightly-2026-09-16 and v4.35.0-rc2.
-/

open Std.WP Lean.Order
set_option mvcgen.warning false
set_option experimental.vcgen true

inductive Val where | i32 (n : UInt32)
inductive Instr where | push (v : Val) | add
structure Frame where
  params : List Val := []
  values : List Val := []
def run : List Instr → Frame → Option Frame
  | [], s => some s
  | .push v :: p, s => run p { s with values := v :: s.values }
  | .add :: p, s => match s.values with
    | .i32 a :: .i32 b :: vs => run p { s with values := .i32 (a + b) :: vs }
    | _ => none

abbrev Assn := Frame → Prop
structure Code where prog : List Instr
instance : WP Code Unit Assn (Unit → Assn) where
  wpTrans c := ⟨fun Q E s => match run c.prog s with
    | some s' => Q () s'
    | none => ∀ s', E () s'⟩
  wp_trans_monotone c := by
    intro Q Q' E E' hE hQ s h
    have h' : (match run c.prog s with
      | some s' => Q () s' | none => ∀ s', E () s') := h
    show (match run c.prog s with
      | some s' => Q' () s' | none => ∀ s', E' () s')
    cases hr : run c.prog s <;> rw [hr] at h'
    · exact fun s' => hE () s' (h' s')
    · exact hQ () _ h'

private theorem Triple.of_imp {c : Code} {pre : Assn} {Q : Unit → Assn}
    {E : Unit → Assn} (h : ∀ s, pre s →
      (match run c.prog s with
        | some s' => Q () s' | none => ∀ s', E () s')) :
    Triple c pre Q E := ⟨fun s hp => h s hp⟩

@[spec] theorem Spec.nil {Q : Unit → Assn} {E} :
    Triple (⟨[]⟩ : Code) (Q ()) Q E :=
  Triple.of_imp fun s h => by simpa [run] using h

@[spec] theorem Spec.cons {i j : Instr} {q : List Instr} {Q : Unit → Assn} {E} :
    Triple (⟨i :: j :: q⟩ : Code)
      (Std.WP.wp (⟨[i]⟩ : Code) (fun _ => Std.WP.wp (⟨j :: q⟩ : Code) Q E) E)
      Q E :=
  Triple.of_imp fun s h => by
    have h' : (match run [i] s with
      | some s' => (match run (j :: q) s' with
          | some s'' => Q () s'' | none => ∀ s', E () s')
      | none => ∀ s', E () s') := h
    cases i with
    | push v => simpa [run] using h'
    | add =>
      simp only [run] at h' ⊢
      rcases s with ⟨ps, _ | ⟨⟨a⟩, _ | ⟨⟨b⟩, vs⟩⟩⟩ <;> simp at h' ⊢ <;> assumption

/-- Guard-form `push`: the guard meets the raw entry state. -/
@[spec] theorem Spec.push {v : Val} {ps vs : List Val} {Q : Unit → Assn} {E} :
    Triple (⟨[.push v]⟩ : Code)
      (fun s => (⌜s = ⟨ps, vs⟩⌝ : Prop) ⊓ Q () ⟨ps, v :: vs⟩) Q E :=
  Triple.of_imp fun s h => by
    simp only [meet_prop_eq_and, ofProp_prop_eq] at h
    obtain ⟨rfl, hq⟩ := h
    simpa [run] using hq

@[spec] theorem Spec.add {ps : List Val} {a b : UInt32} {vs : List Val}
    {Q : Unit → Assn} {E} :
    Triple (⟨[.add]⟩ : Code)
      (fun s => (⌜s = ⟨ps, .i32 a :: .i32 b :: vs⟩⌝ : Prop) ⊓
        Q () ⟨ps, .i32 (a + b) :: vs⟩) Q E :=
  Triple.of_imp fun s h => by
    simp only [meet_prop_eq_and, ofProp_prop_eq] at h
    obtain ⟨rfl, hq⟩ := h
    simpa [run] using hq

/-! Fails: the first `push` guard is `s✝ = { params := ?ps, values := ?vs }`
and nothing assigns. -/
example (x y : UInt32) : ⦃ fun s => s.params = [] ∧ s.values = [] ⦄
    (⟨[.push (.i32 x), .push (.i32 y), .add]⟩ : Code)
    ⦃ fun _ s => s.params = [] ⦄ := by
  vcgen
  all_goals sorry

/-! Passes: the manual eta step exposes the constructor and every guard
closes by unification. -/
example (x y : UInt32) : ⦃ fun s => s.params = [] ∧ s.values = [] ⦄
    (⟨[.push (.i32 x), .push (.i32 y), .add]⟩ : Code)
    ⦃ fun _ s => s.params = [] ⦄ := by
  refine ⟨fun s hp => ?_⟩
  obtain ⟨ps, vs⟩ := s
  vcgen with finish

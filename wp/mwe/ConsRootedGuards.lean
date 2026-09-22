import Std.Tactic.Do
import Std.WP

/-!
# MWE: cons-rooted guard equations stop after one assignment

Companion to `SchematicGuards.lean` and `CleanupVCEta.lean`. Here the
`push` spec is total (a record update) and only `add` guards, over the
projection `s.values`. The guard reaches `cleanupVC`'s `Eq` branch
cons-rooted after `reduceHead`,

    .i32 y :: .i32 x :: s✝.values = .i32 ?a :: .i32 ?b :: ?vs

and unification assigns `?a := y`, then stops: the plain fvar assignment
`?b := x` and the tail `?vs := s✝.values` never happen. No literals are
involved, so this is a different cell from the literal-refusal pair in
`SchematicGuards.lean`: an equation whose both sides are constructor
applications is not descended past the first argument, while the same
chain nested inside an `mk`-rooted whole-state equation unifies in full.

Together the three files span the measured matrix: mk-rooted symbolic
closes; mk-rooted literal refuses; cons-rooted stops after one level;
neutral-vs-mk needs structure eta.

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

@[spec] theorem Spec.push {v : Val} {Q : Unit → Assn} {E} :
    Triple (⟨[.push v]⟩ : Code)
      (fun s => Q () { s with values := v :: s.values }) Q E :=
  Triple.of_imp fun s h => by simpa [run] using h

@[spec] theorem Spec.add {a b : UInt32} {vs : List Val}
    {Q : Unit → Assn} {E} :
    Triple (⟨[.add]⟩ : Code)
      (fun s => (⌜s.values = .i32 a :: .i32 b :: vs⌝ : Prop) ⊓
        Q () { s with values := .i32 (a + b) :: vs }) Q E :=
  Triple.of_imp fun s h => by
    simp only [meet_prop_eq_and, ofProp_prop_eq] at h
    obtain ⟨hv, hq⟩ := h
    simpa [run, hv] using hq

/-! Fails: `?a := y` assigns, then the descent stops. -/
example (x y : UInt32) : ⦃ fun s => s.params = [] ∧ s.values = [] ⦄
    (⟨[.push (.i32 x), .push (.i32 y), .add]⟩ : Code)
    ⦃ fun _ s => s.params = [] ⦄ := by
  vcgen
  all_goals sorry

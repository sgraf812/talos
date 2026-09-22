import Std.Tactic.Do
import Std.WP

/-!
# MWE: schematic guard preconditions under `vcgen with finish`

A spec for a partial instruction states its stack shape as a schematic
guard `⌜s = frame-pattern⌝ ⊓ continuation`. Whether the guard's
metavariables get assigned depends on conditions a spec author cannot
see. The two adjacent examples at the bottom differ in ONE token, the
symbolic `b` versus the literal `2` in the pushed values:

* `⦃ s = ⟨[.i32 a], rest⟩ ⦄ [.push b, .push 3, .add] ⦃ … ⦄` closes,
  with every metavariable assigned, including the abstract tail `rest`.
* `⦃ s = ⟨[], rest⟩ ⦄ [.push 2, .push 3, .add] ⦃ … ⦄` leaves the guard's
  metavariables unassigned and `finish` fails on
  `¬ ⟨[], .i32 3 :: .i32 2 :: rest⟩ = ⟨?ps, .i32 ?a :: .i32 ?b :: ?vs⟩`.

Further cells measured with this machine:

* With a single state argument (`Assn := Frame → Prop`) both examples
  close. With `Frame → Nat → Prop` (guarded state first) the symbolic
  example closes.
* A guard over the projection `s.values` instead of the whole `s` never
  assigns its metavariables, at any arity (`OneState.addProj` in an
  earlier revision); whole-state guards with explicit `Frame.mk`
  continuations are the only reliable spec shape found.
* The same goals reached through a bare `wp`-application (substituting
  the entry equation before `vcgen`) close in configurations where the
  `Triple` route fails.

Reproduces on nightly-2026-08-21, nightly-2026-09-16 and v4.35.0-rc2.

One more finding needs a one-line change to reproduce and is kept out of
the compiled file: marking a recursive definition `@[reducible]` and
using it in a spec's guard makes spec application fail with
`Failed to construct rule SpecProof.global …`, and printing that error
panics with `PANIC … loose bvar in expression` in `whnfEasyCases`.
Reproduce by adding a `lookupS`-style recursive read to a guard and
marking it reducible.
-/

open Std.WP Lean.Order
set_option mvcgen.warning false
set_option experimental.vcgen true

inductive Val where | i32 (n : UInt32)
inductive Instr where | push (v : UInt32) | add
structure Frame where
  params : List Val := []
  values : List Val := []
def run : List Instr → Frame → Option Frame
  | [], s => some s
  | .push n :: p, s => run p { s with values := .i32 n :: s.values }
  | .add :: p, s => match s.values with
    | .i32 a :: .i32 b :: vs => run p { s with values := .i32 (a + b) :: vs }
    | _ => none

namespace TwoState

abbrev Assn := Nat → Frame → Prop
structure Code where prog : List Instr
instance : WP Code Unit Assn (Unit → Assn) where
  wpTrans c := ⟨fun Q E m s => match run c.prog s with
    | some s' => Q () m s'
    | none => ∀ m' s', E () m' s'⟩
  wp_trans_monotone c := by
    intro Q Q' E E' hE hQ m s h
    have h' : (match run c.prog s with
      | some s' => Q () m s' | none => ∀ m' s', E () m' s') := h
    show (match run c.prog s with
      | some s' => Q' () m s' | none => ∀ m' s', E' () m' s')
    cases hr : run c.prog s <;> rw [hr] at h'
    · exact fun m' s' => hE () m' s' (h' m' s')
    · exact hQ () _ _ h'

private theorem Triple.of_imp {c : Code} {pre : Assn} {Q : Unit → Assn}
    {E : Unit → Assn} (h : ∀ m s, pre m s →
      (match run c.prog s with
        | some s' => Q () m s' | none => ∀ m' s', E () m' s')) :
    Triple c pre Q E := ⟨fun m s hp => h m s hp⟩

@[spec] theorem Spec.nil {Q : Unit → Assn} {E} :
    Triple (⟨[]⟩ : Code) (Q ()) Q E :=
  Triple.of_imp fun m s h => by simpa [run] using h

@[spec] theorem Spec.cons {i j : Instr} {q : List Instr} {Q : Unit → Assn} {E} :
    Triple (⟨i :: j :: q⟩ : Code)
      (Std.WP.wp (⟨[i]⟩ : Code) (fun _ => Std.WP.wp (⟨j :: q⟩ : Code) Q E) E)
      Q E :=
  Triple.of_imp fun m s h => by
    have h' : (match run [i] s with
      | some s' => (match run (j :: q) s' with
          | some s'' => Q () m s'' | none => ∀ m' s', E () m' s')
      | none => ∀ m' s', E () m' s') := h
    cases i with
    | push n => simpa [run] using h'
    | add =>
      simp only [run] at h' ⊢
      rcases s with ⟨ps, _ | ⟨⟨a⟩, _ | ⟨⟨b⟩, vs⟩⟩⟩ <;> simp at h' ⊢ <;> assumption

@[spec] theorem Spec.push {n : UInt32} {Q : Unit → Assn} {E} :
    Triple (⟨[.push n]⟩ : Code)
      (fun m s => Q () m { s with values := .i32 n :: s.values }) Q E :=
  Triple.of_imp fun m s h => by simpa [run] using h

@[spec] theorem Spec.add {ps : List Val} {a b : UInt32} {vs : List Val}
    {Q : Unit → Assn} {E} :
    Triple (⟨[.add]⟩ : Code)
      (fun m s => (⌜s = ⟨ps, .i32 a :: .i32 b :: vs⟩⌝ : Prop) ⊓
        Q () m ⟨ps, .i32 (a + b) :: vs⟩) Q E :=
  Triple.of_imp fun m s h => by
    simp only [meet_prop_eq_and, ofProp_prop_eq] at h
    obtain ⟨rfl, hq⟩ := h
    simpa [run] using hq

example (a b : UInt32) (rest : List Val) :
    ⦃ fun _ s => s = ⟨[.i32 a], rest⟩ ⦄
    (⟨[.push b, .push 3, .add]⟩ : Code)
    ⦃ fun _ _ s => s.values = .i32 (3 + b) :: rest ⦄ := by
  vcgen with finish

/-! Fails: the literal program leaves the guard metavariables unassigned. -/
example (rest : List Val) :
    ⦃ fun _ s => s = ⟨[], rest⟩ ⦄
    (⟨[.push 2, .push 3, .add]⟩ : Code)
    ⦃ fun _ _ s => s.values = .i32 5 :: rest ⦄ := by
  vcgen
  all_goals sorry

end TwoState

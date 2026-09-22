import Std.Tactic.Do
import Std.WP

/-!
# MWE: an assertion-position matcher never reduces

A total (fuel-free) stack machine with a two-channel `Std.WP.WP` instance:
`done` feeds the normal postcondition, `break_`/`fail` feed an
`Exit → Assn` exception channel.

`Spec.blk` reindexes the break channel with a match on `Exit`. After
`Spec.br` fires inside a block, the entailment's right-hand side is that
match applied to the constructor `Exit.break_ 0`:

    ⊤ ⊑ (match Exit.break_ 0 with
          | .break_ 0 => wp ⟨rest⟩ Q E
          | .break_ (n + 1) => E (.break_ n)
          | .fail => E .fail) s

The matcher is never iota-reduced in assertion position, so decomposition
stops and the continuation `wp` survives into a verification condition that
`finish` cannot prove. A two-level match (`match e with | .break_ n =>
match n with …`) behaves the same. Reproduces on nightly-2026-08-21, nightly-2026-09-16 and v4.35.0-rc2.
-/

open Std.WP Lean.Order
set_option mvcgen.warning false

inductive Instr where
  | push (n : Nat)
  | add
  | br (depth : Nat)
  | blk (body : List Instr)

abbrev Stack := List Nat

inductive Out where
  | done (s : Stack)
  | break_ (depth : Nat) (s : Stack)
  | fail

def run : List Instr → Stack → Out
  | [], s => .done s
  | .push n :: p, s => run p (n :: s)
  | .add :: p, a :: b :: s => run p ((a + b) :: s)
  | .add :: _, _ => .fail
  | .br n :: _, s => .break_ n s
  | .blk body :: p, s =>
    match run body s with
    | .done s' => run p s'
    | .break_ 0 s' => run p s'
    | .break_ (n + 1) s' => .break_ n s'
    | .fail => .fail

theorem run_cons (i : Instr) (p : List Instr) (s : Stack) :
    run (i :: p) s =
      match run [i] s with
      | .done s' => run p s'
      | o => o := by
  cases i with
  | push n => simp [run]
  | add => rcases s with _ | ⟨a, _ | ⟨b, s⟩⟩ <;> simp [run]
  | br n => simp [run]
  | blk body =>
    cases hr : run body s with
    | done s' => simp [run, hr]
    | break_ n s' => cases n <;> simp [run, hr]
    | fail => simp [run, hr]

abbrev Assn := Stack → Prop

inductive Exit where
  | break_ (depth : Nat)
  | fail

abbrev EAssn := Exit → Assn

@[simp] def outPost (Q : Assn) (E : EAssn) : Out → Prop
  | .done s => Q s
  | .break_ n s => E (.break_ n) s
  | .fail => ∀ s, E .fail s

structure Code where
  prog : List Instr

instance : WP Code Unit Assn EAssn where
  wpTrans c := ⟨fun Q E s => outPost (Q ()) E (run c.prog s)⟩
  wp_trans_monotone c := by
    intro Q Q' E E' hE hQ s h
    have h' : outPost (Q ()) E (run c.prog s) := h
    show outPost (Q' ()) E' (run c.prog s)
    cases hr : run c.prog s <;> rw [hr] at h'
    · exact hQ () _ h'
    · exact hE _ _ h'
    · exact fun s' => hE _ s' (h' s')

theorem wp_apply (c : Code) (Q : Unit → Assn) (E : EAssn) (s : Stack) :
    Std.WP.wp c Q E s = outPost (Q ()) E (run c.prog s) := rfl

private theorem Triple.of_imp {c : Code} {pre : Assn} {Q : Unit → Assn}
    {E : EAssn} (h : ∀ s, pre s → outPost (Q ()) E (run c.prog s)) :
    Triple c pre Q E :=
  ⟨fun s hp => h s hp⟩

/-! ## Structural and instruction specs -/

@[spec] theorem Spec.nil {Q : Unit → Assn} {E : EAssn} :
    Triple (⟨[]⟩ : Code) (Q ()) Q E :=
  Triple.of_imp fun s h => by simpa [run] using h

@[spec] theorem Spec.cons {i : Instr} {j : Instr} {q : List Instr}
    {Q : Unit → Assn} {E : EAssn} :
    Triple (⟨i :: j :: q⟩ : Code)
      (Std.WP.wp (⟨[i]⟩ : Code) (fun _ => Std.WP.wp (⟨j :: q⟩ : Code) Q E) E)
      Q E :=
  Triple.of_imp fun s h => by
    rw [run_cons]
    rw [wp_apply] at h
    cases hr : run [i] s <;> rw [hr] at h
    · exact h
    · exact h
    · exact h

@[spec] theorem Spec.push {n : Nat} {Q : Unit → Assn} {E : EAssn} :
    Triple (⟨[.push n]⟩ : Code) (fun s => Q () (n :: s)) Q E :=
  Triple.of_imp fun s h => by simpa [run] using h

/-- The guard-form spec of the partial `add`: schematic `a b vs`. -/
@[spec] theorem Spec.add {a b : Nat} {vs : Stack} {Q : Unit → Assn} {E : EAssn} :
    Triple (⟨[.add]⟩ : Code)
      (fun s => (⌜s = a :: b :: vs⌝ : Prop) ⊓ Q () ((a + b) :: vs))
      Q E :=
  Triple.of_imp fun s h => by
    simp only [meet_prop_eq_and, ofProp_prop_eq] at h
    obtain ⟨rfl, hq⟩ := h
    simpa [run] using hq

@[spec] theorem Spec.br {n : Nat} {Q : Unit → Assn} {E : EAssn} :
    Triple (⟨[.br n]⟩ : Code) (fun s => E (.break_ n) s) Q E :=
  Triple.of_imp fun s h => by simpa [run] using h

/-- The block spec: epost surgery reindexing the break channel. -/
@[spec] theorem Spec.blk {body : List Instr} {Q : Unit → Assn} {E : EAssn} :
    Triple (⟨[.blk body]⟩ : Code)
      (Std.WP.wp (⟨body⟩ : Code) Q
        (fun e => match e with
          | .break_ 0 => Q ()
          | .break_ (n + 1) => E (.break_ n)
          | .fail => E .fail))
      Q E :=
  Triple.of_imp fun s h => by
    rw [wp_apply] at h
    simp only [run]
    cases hr : run body s <;> rw [hr] at h
    · simpa [run] using h
    · next n s' => cases n <;> simpa [run] using h
    · exact h

/-! ## Contrast: the same chain without a block closes -/

example : ⦃ fun s => s = [] ⦄ (⟨[.push 2, .push 3, .add]⟩ : Code)
    ⦃ fun _ s => s = [5] ⦄ := by
  vcgen with finish

/-! ## The failure: `br` through `blk`

Decomposition applies `Spec.cons`, `Spec.blk`, `Spec.cons`, `Spec.push` and
`Spec.br`, then stops at the unreduced matcher. The one verification
condition contains `wp ⟨[.push 1, .add]⟩ …` and `finish` fails on it. -/

example : ⦃ fun s => s = [] ⦄ (⟨[.blk [.push 7, .br 0], .push 1, .add]⟩ : Code)
    ⦃ fun _ s => s = [8] ⦄ := by
  vcgen
  all_goals sorry

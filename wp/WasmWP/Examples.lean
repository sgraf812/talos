import WasmWP.Call
import WasmWP.Block

set_option experimental.vcgen true

/-!
# End-to-end demos

A two-function module: `add2` sums its arguments, `addTwice` computes
`(a + b) + b` through a call to `add2`. Each function gets three
declarations:

* `<f>_body` is folded into `<f>_terminates`: the calling-convention triple
  of the body, by `vcgen with finish`.
* `<f>_terminates`: the public fuel-free spec, through
  `TerminatesWith.of_triple`.
* `Spec.call_<f>`: the `@[spec]` contract of `[.call i]`, the object other
  programs compose with.

`addTwice_terminates` steps through `Spec.call_add2`, so `addTwice` is
verified against `add2`'s contract, never its body. The final example is a
client program composing `Spec.call_addTwice` the same way.
-/

namespace Wasm.Demo

open Std.WP Lean.Order Wasm

set_option mvcgen.warning false

/-- `add2 (a, b) = a + b`. -/
def add2 : Function :=
  { params := [.i32, .i32], results := [.i32],
    body := [.localGet 0, .localGet 1, .add] }

/-- `addTwice (a, b) = (a + b) + b`, through `add2`. -/
def addTwice : Function :=
  { params := [.i32, .i32], results := [.i32],
    body := [.localGet 0, .localGet 1, .call 1, .localGet 1, .add] }

def m : Module := { funcs := [addTwice, add2] }

/-! ## Straight-line code -/

example (env : HostEnv U) (st : Store U) :
    ⦃ fun st' s => st' = st ∧ s.values = [] ⦄
      (⟨m, env, [.const 2, .const 3, .add]⟩ : Code)
      ⦃ fun _ st' s => st' = st ∧ s.values = [.i32 5] ⦄ := by
  vcgen with finish

/-! ## `add2` -/

theorem add2_terminates (env : HostEnv U) (st : Store U) (a b : UInt32)
    (rest : List Value) :
    TerminatesWith env m 1 st (.i32 b :: .i32 a :: rest)
      (fun st' vs => st' = st ∧ vs = .i32 (a + b) :: rest) := by
  wp_body add2
  vcgen with finish

/-- The contract of `[.call 1]`: what callers of `add2` compose with. -/
@[spec] theorem Spec.call_add2 {env : HostEnv U}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => (⌜s.values[0]! = .i32 s.values[0]!.asI32 ∧
          s.values[1]! = .i32 s.values[1]!.asI32 ∧ 2 ≤ s.values.length⌝ : Prop) ⊓
        Q () st { s with
          values := .i32 (s.values[1]!.asI32 + s.values[0]!.asI32)
            :: s.values.drop 2 } ⦄
      (⟨m, env, [.call 1]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  simp only [meet_prop_eq_and, ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, h1, hlen⟩, hq⟩ := hpre
  rcases hv : s.values with _ | ⟨v0, _ | ⟨v1, vs⟩⟩ <;> rw [hv] at hlen h0 h1 hq
  · simp at hlen
  · simp at hlen
  · simp only [getElem!_cons_zero, getElem!_cons_one, drop_two_cons] at h0 h1 hq
    have hv' : s.values = .i32 v0.asI32 :: .i32 v1.asI32 :: vs := by
      rw [hv, ← h0, ← h1]
    refine Triple.le_wp
      (Spec.call_tw (Post := fun st' vs2 =>
        st' = st ∧ vs2 = .i32 (v1.asI32 + v0.asI32) :: vs))
      st s ⟨hv' ▸ add2_terminates env st v1.asI32 v0.asI32 vs, ?_⟩
    rintro st' vs2 ⟨rfl, rfl⟩
    simpa [hv] using hq

/-! ## `addTwice`, against `add2`'s contract -/

theorem addTwice_terminates (env : HostEnv U) (st : Store U) (a b : UInt32)
    (rest : List Value) :
    TerminatesWith env m 0 st (.i32 b :: .i32 a :: rest)
      (fun st' vs => st' = st ∧ vs = .i32 (a + b + b) :: rest) := by
  wp_body addTwice
  vcgen with finish

/-- The compositional spec of a call to `addTwice`. -/
@[spec] theorem Spec.call_addTwice {env : HostEnv U}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => (⌜s.values[0]! = .i32 s.values[0]!.asI32 ∧
          s.values[1]! = .i32 s.values[1]!.asI32 ∧ 2 ≤ s.values.length⌝ : Prop) ⊓
        Q () st { s with
          values := .i32 (s.values[1]!.asI32 + s.values[0]!.asI32
              + s.values[0]!.asI32)
            :: s.values.drop 2 } ⦄
      (⟨m, env, [.call 0]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  simp only [meet_prop_eq_and, ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, h1, hlen⟩, hq⟩ := hpre
  rcases hv : s.values with _ | ⟨v0, _ | ⟨v1, vs⟩⟩ <;> rw [hv] at hlen h0 h1 hq
  · simp at hlen
  · simp at hlen
  · simp only [getElem!_cons_zero, getElem!_cons_one, drop_two_cons] at h0 h1 hq
    have hv' : s.values = .i32 v0.asI32 :: .i32 v1.asI32 :: vs := by
      rw [hv, ← h0, ← h1]
    refine Triple.le_wp
      (Spec.call_tw (Post := fun st' vs2 =>
        st' = st ∧ vs2 = .i32 (v1.asI32 + v0.asI32 + v0.asI32) :: vs))
      st s ⟨hv' ▸ addTwice_terminates env st v1.asI32 v0.asI32 vs, ?_⟩
    rintro st' vs2 ⟨rfl, rfl⟩
    simpa [hv] using hq

/-- A client program composing `addTwice` through its contract. -/
example (env : HostEnv U) (st : Store U) :
    ⦃ fun st' s => st' = st ∧ s.values = [] ⦄
      (⟨m, env, [.const 10, .const 20, .call 0, .const 1, .add]⟩ : Code)
      ⦃ fun _ st' s => st' = st ∧ s.values = [.i32 51] ⦄ := by
  vcgen with finish

end Wasm.Demo

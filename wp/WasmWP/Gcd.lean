import WasmWP.Loop
import WasmWP.Block
import WasmWP.Call

set_option mvcgen.warning false
set_option experimental.vcgen true

/-!
# Euclid's gcd

The classic Wasm gcd: a `loop` whose body is a `block` that exits when
`b = 0` and otherwise rotates `(a, b) ← (b, a % b)` through the scratch
local and restarts the loop with `br 1`. One `vcgen` call verifies the
function: `Spec.loop` comes from the spec table, the invariant and the
variant come from the `invariants` alternatives, and `finish` closes
every verification condition.
-/

namespace Wasm.GcdDemo

open Std.WP Lean.Order Wasm

def gcdF : Function :=
  { params := [.i32, .i32], results := [.i32], locals := [.i32],
    body := [
      .loop 0 0 [
        .block 0 0 [
          .localGet 1, .eqz, .br_if 0,
          .localGet 0, .localGet 1, .remU, .localSet 2,
          .localGet 1, .localSet 0,
          .localGet 2, .localSet 1,
          .br 1]],
      .localGet 0] }

def m : Module := { funcs := [gcdF] }

@[grind =] theorem gcd_step (a b : Nat) : Nat.gcd b (a % b) = Nat.gcd a b := by
  rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]

theorem gcd_zero (a : Nat) : Nat.gcd a 0 = a := Nat.gcd_zero_right a

grind_pattern gcd_zero => Nat.gcd a 0

attribute [local grind =] UInt32.toNat_mod UInt32.ofNat_toNat

theorem toNat_mod_lt (a : UInt32) {b : UInt32} (h : b ≠ 0) :
    a.toNat % b.toNat < b.toNat := by
  refine Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => h ?_)
  exact UInt32.toNat_inj.mp (by simpa using h0)

grind_pattern toNat_mod_lt => a.toNat % b.toNat

/-! The spine computation lemmas join grind's normalization set for this
file: `finish` evaluates ground state terms in its simp phase, where a
rewrite is free. The linking lemmas (`Option.get!_some'`,
`Value.asI32_i32`) stay out: a norm rule trivializes and discards the
E-matching instances that link a symbolic term to its value
(lean4#11498), and those lemmas produce exactly such instances. -/
attribute [local grind norm] Wasm.Locals.get_mk Wasm.Locals.set?_mk
  Wasm.Locals.params_mk Wasm.Locals.locals_mk Wasm.Locals.values_mk
  Wasm.getElem!_cons_zero Wasm.getElem!_cons_one Wasm.head!_cons
  Wasm.drop_one_cons Wasm.drop_two_cons
  List.getElem?_cons_zero List.getElem?_cons_succ
  List.cons_append List.nil_append List.length_cons List.length_nil
  List.tail_cons List.set_cons_zero List.set_cons_succ List.take_zero
  List.drop_zero List.take_succ_cons List.drop_succ_cons List.take_nil
  List.drop_nil

set_option maxHeartbeats 800000 in
theorem gcd_terminates (env : HostEnv U) (st : Store U) (a b : UInt32) :
    TerminatesWith env m 0 st [.i32 b, .i32 a]
      (fun st' vs =>
        st' = st ∧ vs = [.i32 (UInt32.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  wp_body gcdF
  vcgen invariants
    | inv1 =>
        fun st' s =>
          match s with
          | ⟨[.i32 a', .i32 b'], [.i32 t], []⟩ =>
              st' = st ∧ Nat.gcd a'.toNat b'.toNat = Nat.gcd a.toNat b.toNat
          | _ => False
    | inv2 => fun _ s => s.params[1]!.asI32.toNat
  with finish

end Wasm.GcdDemo

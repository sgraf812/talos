import Interpreter.Wasm.Spec.Defs
-- TODO(flip): `import Interpreter.Wasm.Host.Universal` and set `U := Universal.State`.
-- Blocked on nightly-2026-08-21: the two `decreasing_by` scripts at
-- SmallStep.lean:6617/6771 (`simp [firstMemOpDepth, isMemOp] <;> assumption`)
-- leave `(if (match a with | .memOp .. => true | _ => false) = true then 1 else 0) = 0`
-- with `isMemOp a = false` in context; nightly `simp` unfolds `isMemOp` in the
-- goal but not the hypothesis, and `Host.Universal` imports `SmallStep` via
-- `Host.Random`.
import Std.WP

/-!
# `Std.WP.WP` instance for the Wasm interpreter

`Code` packages a deep-embedded `Program` with the module and host environment
it runs in. The instance interprets a `Code` by the fuel-free weakest
precondition over `exec`: some fuel bound suffices, and every larger fuel
computes the same continuation.

The two postcondition channels split `Continuation`:

* `Fallthrough` feeds the normal postcondition `Assn`.
* Every other continuation feeds the exception postcondition `EAssn`, indexed
  by the state-stripped payload `Exit`. A state component the continuation
  drops (locals at `Return`/`Trap`/`ReturnCall`, everything at `Invalid`) is
  demonically quantified: the arm must hold at every value, so specs can
  constrain exactly the recorded data.
* `OutOfFuel` maps to `False`, so provable triples state total correctness.
-/

namespace Wasm

open Std.WP Lean.Order

/-- The verification host state: the universal host serves every module. -/
abbrev U := Unit -- TODO(flip): `Universal.State`, see the import note above.

/-- A Wasm program packaged with its execution context. -/
structure Code where
  module : Module
  env : HostEnv U := {}
  prog : Program

/-- A non-`Fallthrough` exit of a Wasm computation, state stripped. -/
inductive Exit where
  | Break      (depth : Nat)
  | Throwing   (tag : Nat) (args : List Value)
  | Return     (vs : List Value)
  | Trap       (msg : String)
  | ReturnCall (id : Nat) (vs : List Value)
  | Invalid    (msg : String)

/-- Assertions over the interpreter state. -/
abbrev Assn := Store U → Locals → Prop

/-- Exception postconditions, one assertion per exit payload. -/
abbrev EAssn := Exit → Assn

/-- Judge a continuation by a normal postcondition `Q` and an exception
postcondition `epost`. Arms apply at the state the continuation records;
a dropped component is universally quantified. -/
@[simp] def contPost (Q : Assn) (epost : EAssn) : Continuation U → Prop
  | .Fallthrough st s     => Q st s
  | .Break n st s         => epost (.Break n) st s
  | .Throwing t as st s   => epost (.Throwing t as) st s
  | .Return st vs         => ∀ s, epost (.Return vs) st s
  | .Trap st msg          => ∀ s, epost (.Trap msg) st s
  | .ReturnCall id st vs  => ∀ s, epost (.ReturnCall id vs) st s
  | .Invalid msg          => ∀ st s, epost (.Invalid msg) st s
  | .OutOfFuel            => False

theorem contPost_mono {Q Q' : Assn} {epost epost' : EAssn}
    (hQ : ∀ st s, Q st s → Q' st s)
    (hE : ∀ e st s, epost e st s → epost' e st s) :
    ∀ k, contPost Q epost k → contPost Q' epost' k := by
  intro k h
  cases k <;> simp_all <;> intros <;> solve_by_elim

/-- Fuel-free weakest precondition of a `Code` against a continuation
predicate: some fuel bound suffices, and every larger fuel agrees. -/
def Code.wp (c : Code) (P : Continuation U → Prop)
    (st : Store U) (s : Locals) : Prop :=
  ∃ N, ∀ fuel ≥ N, P (exec fuel c.module st s c.prog c.env)

theorem Code.wp_mono {c : Code} {P P' : Continuation U → Prop}
    (h : ∀ k, P k → P' k) {st : Store U} {s : Locals}
    (hwp : c.wp P st s) : c.wp P' st s := by
  obtain ⟨N, hN⟩ := hwp
  exact ⟨N, fun fuel hf => h _ (hN fuel hf)⟩

/-- If `exec` computes `k` at every fuel, `Code.wp` is `P k`. -/
theorem Code.wp_of_const {c : Code} {st : Store U} {s : Locals}
    {k : Continuation U}
    (heq : ∀ fuel, exec fuel c.module st s c.prog c.env = k)
    (P : Continuation U → Prop) : c.wp P st s ↔ P k := by
  constructor
  · rintro ⟨N, hN⟩; have := hN N (Nat.le_refl N); rwa [heq] at this
  · exact fun h => ⟨0, fun fuel _ => heq fuel ▸ h⟩

/-- If `exec` computes `k` at every successor fuel, `Code.wp` is `P k`.
Every fuel-constant instruction satisfies the hypothesis, since `execOne`
returns `OutOfFuel` only at fuel `0`. -/
theorem Code.wp_of_const_succ {c : Code} {st : Store U} {s : Locals}
    {k : Continuation U}
    (heq : ∀ fuel, exec (fuel + 1) c.module st s c.prog c.env = k)
    (P : Continuation U → Prop) : c.wp P st s ↔ P k := by
  constructor
  · rintro ⟨N, hN⟩; have := hN (N + 1) (Nat.le_succ N)
    rwa [heq] at this
  · refine fun h => ⟨1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le hf
    rw [Nat.add_comm, heq]; exact h

instance : WP Code Unit Assn EAssn where
  wpTrans c := ⟨fun Q epost => c.wp (contPost (Q ()) epost)⟩
  wp_trans_monotone c := by
    intro Q Q' epost epost' hE hQ st s h
    exact Code.wp_mono
      (contPost_mono (fun st s => hQ () st s) (fun e st s => hE e st s)) h

/-- `Std.WP.wp` of a `Code`, unfolded to the fuel-free `Code.wp`. The `rfl`
bridge behind the per-instruction equations. -/
theorem wp_apply (c : Code) (Q : Unit → Assn) (epost : EAssn) :
    Std.WP.wp c Q epost = c.wp (contPost (Q ()) epost) := rfl

end Wasm

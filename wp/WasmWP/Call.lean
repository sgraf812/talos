import WasmWP.Spec

/-!
# Function calls and the `TerminatesWith` bridge

`Spec.call_tw` steps a `.call` singleton through a callee's fuel-free
`TerminatesWith` contract. `TerminatesWith.of_triple` closes the loop: a
triple on a function body, stated against the standard calling convention,
yields the function's public fuel-free spec. Fuel appears in neither
statement; both proofs thread it through `run_fuel_mono`.
-/

namespace Wasm

open Std.WP Lean.Order

/-- Step a direct call through the callee's total-correctness contract:
the precondition carries the contract at the current stack and the
postcondition obligation for every contractual result. -/
theorem Spec.call_tw {m : Module} {env : HostEnv U} {id : Nat}
    {Q : Unit → Assn} {epost : EAssn} {Post : Store U → List Value → Prop} :
    ⦃ fun st s => TerminatesWith env m id st s.values Post ∧
        ∀ st' vs, Post st' vs → Q () st' { s with values := vs } ⦄
      (⟨m, env, [.call id]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  obtain ⟨htw, hpost⟩ := hpre
  rw [wp_apply]
  obtain ⟨N, hN⟩ := htw
  obtain ⟨vs, st', hrun, hP⟩ := hN N (Nat.le_refl N)
  have hne : run N m id st s.values env ≠ .OutOfFuel := by
    rw [hrun]; intro h; cases h
  refine ⟨N + 1, fun fuel hf => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hle : N ≤ f := by omega
  rw [exec_call_cons, run_fuel_mono hle hne, hrun]
  dsimp only
  rw [exec_nil]
  exact hpost st' vs hP

/-- The public fuel-free spec of a function, from a triple on its body.
The triple's postconditions state the calling convention: `Fallthrough`,
`Return` and `Break 0` exits become `.Success` with the top
`f.results.length` values prepended to the caller remainder. Every other
exit is excluded, so the derived spec asserts a clean total run. -/
theorem TerminatesWith.of_triple {m : Module} {env : HostEnv U} {id : Nat}
    {f : Function} {P : Store U → List Value → Prop} {args : List Value}
    (hImp : m.imports[id]? = none)
    (hf : m.funcs[id - m.imports.length]? = some f)
    (st : Store U)
    (h : Std.WP.wp (⟨m, env, f.body⟩ : Code)
      (fun _ st' s' =>
        P st' (s'.values.take f.results.length ++ args.drop f.numParams))
      (fun e => match e with
        | .Return vs => fun st' _ =>
            P st' (vs.take f.results.length ++ args.drop f.numParams)
        | .Break 0 => fun st' s' =>
            P st' (s'.values.take f.results.length ++ args.drop f.numParams)
        | _ => fun _ _ => False)
      st (f.toLocals (args.take f.numParams).reverse)) :
    TerminatesWith env m id st args P := by
  have hwp := h
  rw [wp_apply] at hwp
  obtain ⟨N, hN⟩ := hwp
  refine ⟨N, fun fuel hfuel => ?_⟩
  have hc := hN fuel hfuel
  rw [run_eq hImp]
  simp only [hf]
  cases hexec : exec fuel m st (f.toLocals (args.take f.numParams).reverse)
      f.body env with
  | Fallthrough st' s' => rw [hexec] at hc; exact ⟨_, _, rfl, hc⟩
  | Return st' vs => rw [hexec] at hc; exact ⟨_, _, rfl, hc default⟩
  | Break n st' s' =>
    rw [hexec] at hc
    cases n with
    | zero => exact ⟨_, _, rfl, hc⟩
    | succ k => exact hc.elim
  | Trap st' msg => rw [hexec] at hc; exact (hc default).elim
  | Invalid msg => rw [hexec] at hc; exact (hc st default).elim
  | OutOfFuel => rw [hexec] at hc; exact hc.elim
  | ReturnCall id' st' vs => rw [hexec] at hc; exact (hc default).elim
  | Throwing tag targs st' s' => rw [hexec] at hc; exact hc.elim

/-- Reduces a `TerminatesWith` goal to the weakest precondition of the
function's body. `wp_body f` applies `TerminatesWith.of_triple` for the
function `f` and evaluates the calling convention, so the entry locals
`f.toLocals (args.take f.numParams).reverse` and the result arity become
explicit lists. The remaining goal is a `wp` application on `f.body`,
ready for `vcgen`. -/
macro "wp_body" f:ident : tactic =>
  `(tactic|
    (refine TerminatesWith.of_triple (f := $f) rfl rfl _ ?_
     simp only [$f:ident, Function.toLocals, Function.numParams,
       List.length_cons, List.length_nil, List.take, List.reverse_cons,
       List.reverse_nil, List.nil_append, List.cons_append, List.map,
       List.drop, ValueType.zero]))

end Wasm

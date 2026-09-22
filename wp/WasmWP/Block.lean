import WasmWP.Spec

/-!
# Structured control: `block` and `br`

`wp_block_eq` states the block law as epost surgery: entering a block
reindexes the break channel. Depth `0` exits the block into the normal
postcondition at the trimmed stack, depth `n + 1` becomes depth `n`
outside, and every other exit forwards through the uniform
`Exit → Assn` channel unchanged.
-/

namespace Wasm

open Std.WP Lean.Order

theorem wp_block_eq {m : Module} {env : HostEnv U} {ps rs : Nat}
    {body : Program} {Q : Unit → Assn} {epost : EAssn} {st : Store U}
    {s : Locals} :
    Std.WP.wp (⟨m, env, [.block ps rs body]⟩ : Code) Q epost st s ↔
      Std.WP.wp (⟨m, env, body⟩ : Code)
        (fun _ st' s' => Q () st' { s' with values := s'.values.take rs ++ s.values.drop ps })
        (fun e => match e with
          | .Break n => match n with
            | 0 => fun st' s' => Q () st' { s' with values := s'.values.take rs ++ s.values.drop ps }
            | n + 1 => epost (.Break n)
          | e => epost e)
        st s := by
  simp only [wp_apply, Code.wp]
  have hcase : ∀ fuel,
      contPost (Q ()) epost
          (exec (fuel + 1) m st s [.block ps rs body] env)
        = contPost (fun st' s' => Q () st' { s' with values := s'.values.take rs ++ s.values.drop ps })
            (fun e => match e with
              | .Break n => match n with
                | 0 => fun st' s' =>
                    Q () st' { s' with values := s'.values.take rs ++ s.values.drop ps }
                | n + 1 => epost (.Break n)
              | e => epost e)
            (exec fuel m st s body env) := by
    intro fuel
    rw [exec_block_cons]
    cases exec fuel m st s body env with
    | Fallthrough st' s' => simp [exec_nil]
    | Break n st' s' => cases n <;> simp [exec_nil]
    | Return st' vs => rfl
    | Trap st' msg => rfl
    | Invalid msg => rfl
    | OutOfFuel => rfl
    | ReturnCall id st' vs => rfl
    | Throwing t as st' s' => rfl
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun fuel hf => ?_⟩
    rw [← hcase fuel]
    exact hN (fuel + 1) (by omega)
  · rintro ⟨N, hN⟩
    refine ⟨N + 1, fun fuel hf => ?_⟩
    cases fuel with
    | zero => omega
    | succ f => rw [hcase f]; exact hN f (by omega)

@[spec] theorem Spec.block {m : Module} {env : HostEnv U} {ps rs : Nat}
    {body : Program} {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => Std.WP.wp (⟨m, env, body⟩ : Code)
        (fun _ st' s' => Q () st' { s' with values := s'.values.take rs ++ s.values.drop ps })
        (fun e => match e with
          | .Break n => match n with
            | 0 => fun st' s' => Q () st' { s' with values := s'.values.take rs ++ s.values.drop ps }
            | n + 1 => epost (.Break n)
          | e => epost e)
        st s ⦄
      (⟨m, env, [.block ps rs body]⟩ : Code)
      ⦃ Q; epost ⦄ :=
  Triple.of_wp_iff fun _ _ h => wp_block_eq.mpr h

@[simp, grind =] theorem wp_br_eq {m : Module} {env : HostEnv U} {n : Nat}
    {Q : Unit → Assn} {epost : EAssn} {st : Store U} {s : Locals} :
    Std.WP.wp (⟨m, env, [.br n]⟩ : Code) Q epost st s ↔
      epost (.Break n) st s := by
  rw [wp_apply]
  exact Code.wp_of_const_succ (k := .Break n st s)
    (fun fuel => by rw [exec_singleton]; simp [execOne.eq_def]) _

@[spec] theorem Spec.br {m : Module} {env : HostEnv U} {n : Nat}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => epost (.Break n) st s ⦄
      (⟨m, env, [.br n]⟩ : Code)
      ⦃ Q; epost ⦄ :=
  Triple.of_wp_iff fun _ _ h => wp_br_eq.mpr h

end Wasm

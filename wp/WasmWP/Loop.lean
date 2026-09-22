import WasmWP.Spec

/-!
# The loop rule

`Spec.loop` proves a `.loop` triple from an invariant and a variant: the
body, started anywhere the invariant holds, either falls through to the
loop's continuation, re-enters through `Break 0` with the invariant
restored and the variant strictly smaller, or exits through the
surrounding exception channel. Totality comes from strong induction on
the variant; the fuel bookkeeping stays inside this proof.
-/

namespace Wasm

open Std.WP Lean.Order

theorem execOne_loop {m : Module} {env : HostEnv U} {st : Store U}
    {s : Locals} {ps rs : Nat} {body : Program} {f : Nat} :
    execOne (f + 1) m st s (.loop ps rs body) env =
      match exec f m st s body env with
      | .Fallthrough st' s' =>
          .Fallthrough st'
            { s' with values := s'.values.take rs ++ s.values.drop ps }
      | .Break 0 st' s' =>
          execOne f m st'
            { s' with values := s'.values.take ps ++ s.values.drop ps }
            (.loop ps rs body) env
      | .Break (k + 1) st' s' => .Break k st' s'
      | k => k := by
  rw [execOne.eq_def]
  cases hk : exec f m st s body env with
  | Fallthrough st' s' => simp [hk]
  | Break n st' s' => cases n <;> simp [hk]
  | Return st' vs => simp [hk]
  | Trap st' msg => simp [hk]
  | Invalid msg => simp [hk]
  | OutOfFuel => simp [hk]
  | ReturnCall id st' vs => simp [hk]
  | Throwing t as st' s' => simp [hk]

/-- The termination measure of a loop. -/
@[spec_invariant_type] def LoopVariant : Type := Store U → Locals → Nat

/-- The invariant of a loop. -/
@[spec_invariant_type] def LoopInvariant : Type := Assn

@[spec] theorem Spec.loop {m : Module} {env : HostEnv U} {ps rs : Nat}
    {body : Program} {Q : Unit → Assn} {epost : EAssn}
    (var : LoopVariant) (inv : LoopInvariant)
    (step : ∀ st₀ s₀, inv st₀ s₀ →
      Std.WP.wp (⟨m, env, body⟩ : Code)
        (fun _ st' s' =>
          Q () st' { s' with values := s'.values.take rs ++ s₀.values.drop ps })
        (fun e => match e with
          | .Break 0 => fun st' s' =>
              inv st'
                { s' with values := s'.values.take ps ++ s₀.values.drop ps } ∧
              var st'
                { s' with values := s'.values.take ps ++ s₀.values.drop ps }
                < var st₀ s₀
          | .Break (n + 1) => epost (.Break n)
          | e => epost e)
        st₀ s₀) :
    ⦃ fun st s => inv st s ⦄
      (⟨m, env, [.loop ps rs body]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hI => ?_
  rw [wp_apply]
  suffices key : ∀ n st s, inv st s → var st s = n →
      (⟨m, env, [.loop ps rs body]⟩ : Code).wp (contPost (Q ()) epost) st s from
    key _ st s hI rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro st s hI hn
    have hstep := step st s hI
    rw [wp_apply] at hstep
    obtain ⟨Nb, hNb⟩ := hstep
    have hcb := hNb Nb (Nat.le_refl Nb)
    have hne : exec Nb m st s body env ≠ .OutOfFuel := by
      intro h; rw [h] at hcb; exact hcb
    have hstable : ∀ f ≥ Nb, exec f m st s body env = exec Nb m st s body env :=
      fun f hf => exec_fuel_mono hf hne
    cases hk : exec Nb m st s body env with
    | Fallthrough st' s' =>
      rw [hk] at hcb
      refine ⟨Nb + 1, fun fuel hf => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [exec_singleton, execOne_loop, hstable f (by omega), hk]
      exact hcb
    | Break k st' s' =>
      cases k with
      | zero =>
        rw [hk] at hcb
        obtain ⟨hI', hlt⟩ := hcb
        obtain ⟨Nl, hNl⟩ := IH _ (hn ▸ hlt) st'
          { s' with values := s'.values.take ps ++ s.values.drop ps } hI' rfl
        refine ⟨Nb + Nl + 1, fun fuel hf => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        rw [exec_singleton, execOne_loop, hstable f (by omega), hk]
        dsimp only
        rw [← exec_singleton]
        exact hNl f (by omega)
      | succ k =>
        rw [hk] at hcb
        refine ⟨Nb + 1, fun fuel hf => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        rw [exec_singleton, execOne_loop, hstable f (by omega), hk]
        exact hcb
    | Return st' vs =>
      rw [hk] at hcb
      refine ⟨Nb + 1, fun fuel hf => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [exec_singleton, execOne_loop, hstable f (by omega), hk]
      exact hcb
    | Trap st' msg =>
      rw [hk] at hcb
      refine ⟨Nb + 1, fun fuel hf => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [exec_singleton, execOne_loop, hstable f (by omega), hk]
      exact hcb
    | Invalid msg =>
      rw [hk] at hcb
      refine ⟨Nb + 1, fun fuel hf => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [exec_singleton, execOne_loop, hstable f (by omega), hk]
      exact hcb
    | OutOfFuel => exact absurd hk hne
    | ReturnCall id st' vs =>
      rw [hk] at hcb
      refine ⟨Nb + 1, fun fuel hf => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [exec_singleton, execOne_loop, hstable f (by omega), hk]
      exact hcb
    | Throwing t as st' s' =>
      rw [hk] at hcb
      refine ⟨Nb + 1, fun fuel hf => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [exec_singleton, execOne_loop, hstable f (by omega), hk]
      exact hcb

end Wasm

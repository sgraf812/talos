import WasmWP.Basic
import Std.Tactic.Do

/-!
# Program equations and specification lemmas

The `wp` of a `Code` follows the program structure:

* `wp_nil_eq`: the empty program is `pure`.
* `wp_cons_eq`: a cons sequences the head singleton with the tail, at the same
  exception postcondition. The proof stabilizes the head's fuel with
  `execOne_fuel_mono`.

Two lemma families sit on top:

* One `@[simp]` `wp_<instr>_eq` equation per instruction, mirroring the
  `execOne` arm exactly, including the `Invalid` exits. Together with
  `wp_cons₂_eq` they compute a residual `wp` away, the way `wp_run` does in
  the pinned tree.
* One `@[spec]` `Spec.<instr>` triple per instruction for `vcgen`, in
  total style: reads are `s.values[i]!`, `Value.asI32`, `Locals.get` and
  `Locals.set?`, continuations are record updates, and an instruction's
  partiality is one closed `⌜…⌝` guard. Nothing is schematic, so every
  verification condition is metavariable-free and `finish` computes it.
-/

namespace Wasm

open Std.WP Lean.Order

set_option mvcgen.warning false

/-! ## `exec` on `[]`, `[i]` and `i :: p` -/

theorem exec_nil {fuel : Nat} {m : Module} {env : HostEnv U}
    {st : Store U} {s : Locals} :
    exec fuel m st s [] env = .Fallthrough st s := by
  simp [exec]

theorem exec_cons {fuel : Nat} {m : Module} {env : HostEnv U}
    {st : Store U} {s : Locals} {i : Instruction} {p : Program} :
    exec fuel m st s (i :: p) env =
      match execOne fuel m st s i env with
      | .Fallthrough st' s' => exec fuel m st' s' p env
      | k => k := by
  cases h : execOne fuel m st s i env <;> simp [exec, h]

theorem exec_singleton {fuel : Nat} {m : Module} {env : HostEnv U}
    {st : Store U} {s : Locals} {i : Instruction} :
    exec fuel m st s [i] env = execOne fuel m st s i env := by
  rw [exec_cons]
  cases h : execOne fuel m st s i env
  case Fallthrough => simp [exec_nil]
  all_goals rfl

/-! ## Sequencing equations -/

@[simp, grind =] theorem wp_nil_eq {m : Module} {env : HostEnv U} {Q : Unit → Assn}
    {epost : EAssn} {st : Store U} {s : Locals} :
    Std.WP.wp (⟨m, env, []⟩ : Code) Q epost st s ↔ Q () st s := by
  rw [wp_apply]
  exact Code.wp_of_const (k := .Fallthrough st s) (fun fuel => exec_nil) _

/-- Sequencing: a cons runs the head singleton and continues with the tail at
the head's fallthrough state. Both programs share the exception
postcondition, since `exec` forwards every non-`Fallthrough` continuation of
the head unchanged. -/
theorem wp_cons_eq {m : Module} {env : HostEnv U} {i : Instruction}
    {p : Program} {Q : Unit → Assn} {epost : EAssn} {st : Store U} {s : Locals} :
    Std.WP.wp (⟨m, env, i :: p⟩ : Code) Q epost st s ↔
      Std.WP.wp (⟨m, env, [i]⟩ : Code)
        (fun _ => Std.WP.wp (⟨m, env, p⟩ : Code) Q epost) epost st s := by
  simp only [wp_apply, Code.wp]
  by_cases hdec : ∃ N₀, execOne N₀ m st s i env ≠ .OutOfFuel
  · obtain ⟨N₀, hN₀⟩ := hdec
    have hstable : ∀ fuel ≥ N₀, execOne fuel m st s i env = execOne N₀ m st s i env :=
      fun fuel hf => execOne_fuel_mono hf hN₀
    cases hk : execOne N₀ m st s i env with
    | Fallthrough st₁ s₁ =>
      constructor
      · rintro ⟨N, hN⟩
        refine ⟨N₀, fun fuel hf => ?_⟩
        rw [exec_singleton, hstable fuel hf, hk]
        refine ⟨N + N₀, fun fuel₂ hf₂ => ?_⟩
        have h1 := hN fuel₂ (by omega)
        rwa [exec_cons, hstable fuel₂ (by omega), hk] at h1
      · rintro ⟨N, hN⟩
        have h1 := hN (N + N₀) (by omega)
        rw [exec_singleton, hstable (N + N₀) (by omega), hk] at h1
        obtain ⟨N₂, hN₂⟩ := h1
        refine ⟨N₂ + N₀, fun fuel hf => ?_⟩
        rw [exec_cons, hstable fuel (by omega), hk]
        exact hN₂ fuel (by omega)
    | OutOfFuel => exact absurd hk hN₀
    | Break n st' s' =>
      constructor
      · rintro ⟨N, hN⟩
        refine ⟨N₀, fun fuel hf => ?_⟩
        rw [exec_singleton, hstable fuel hf, hk]
        have h1 := hN (N + N₀) (by omega)
        rwa [exec_cons, hstable (N + N₀) (by omega), hk] at h1
      · rintro ⟨N, hN⟩
        refine ⟨N + N₀, fun fuel hf => ?_⟩
        rw [exec_cons, hstable fuel (by omega), hk]
        have h1 := hN fuel (by omega)
        rwa [exec_singleton, hstable fuel (by omega), hk] at h1
    | Return st' vs =>
      constructor
      · rintro ⟨N, hN⟩
        refine ⟨N₀, fun fuel hf => ?_⟩
        rw [exec_singleton, hstable fuel hf, hk]
        have h1 := hN (N + N₀) (by omega)
        rwa [exec_cons, hstable (N + N₀) (by omega), hk] at h1
      · rintro ⟨N, hN⟩
        refine ⟨N + N₀, fun fuel hf => ?_⟩
        rw [exec_cons, hstable fuel (by omega), hk]
        have h1 := hN fuel (by omega)
        rwa [exec_singleton, hstable fuel (by omega), hk] at h1
    | Trap st' msg =>
      constructor
      · rintro ⟨N, hN⟩
        refine ⟨N₀, fun fuel hf => ?_⟩
        rw [exec_singleton, hstable fuel hf, hk]
        have h1 := hN (N + N₀) (by omega)
        rwa [exec_cons, hstable (N + N₀) (by omega), hk] at h1
      · rintro ⟨N, hN⟩
        refine ⟨N + N₀, fun fuel hf => ?_⟩
        rw [exec_cons, hstable fuel (by omega), hk]
        have h1 := hN fuel (by omega)
        rwa [exec_singleton, hstable fuel (by omega), hk] at h1
    | Invalid msg =>
      constructor
      · rintro ⟨N, hN⟩
        refine ⟨N₀, fun fuel hf => ?_⟩
        rw [exec_singleton, hstable fuel hf, hk]
        have h1 := hN (N + N₀) (by omega)
        rwa [exec_cons, hstable (N + N₀) (by omega), hk] at h1
      · rintro ⟨N, hN⟩
        refine ⟨N + N₀, fun fuel hf => ?_⟩
        rw [exec_cons, hstable fuel (by omega), hk]
        have h1 := hN fuel (by omega)
        rwa [exec_singleton, hstable fuel (by omega), hk] at h1
    | ReturnCall id st' vs =>
      constructor
      · rintro ⟨N, hN⟩
        refine ⟨N₀, fun fuel hf => ?_⟩
        rw [exec_singleton, hstable fuel hf, hk]
        have h1 := hN (N + N₀) (by omega)
        rwa [exec_cons, hstable (N + N₀) (by omega), hk] at h1
      · rintro ⟨N, hN⟩
        refine ⟨N + N₀, fun fuel hf => ?_⟩
        rw [exec_cons, hstable fuel (by omega), hk]
        have h1 := hN fuel (by omega)
        rwa [exec_singleton, hstable fuel (by omega), hk] at h1
    | Throwing t as st' s' =>
      constructor
      · rintro ⟨N, hN⟩
        refine ⟨N₀, fun fuel hf => ?_⟩
        rw [exec_singleton, hstable fuel hf, hk]
        have h1 := hN (N + N₀) (by omega)
        rwa [exec_cons, hstable (N + N₀) (by omega), hk] at h1
      · rintro ⟨N, hN⟩
        refine ⟨N + N₀, fun fuel hf => ?_⟩
        rw [exec_cons, hstable fuel (by omega), hk]
        have h1 := hN fuel (by omega)
        rwa [exec_singleton, hstable fuel (by omega), hk] at h1
  · have hall : ∀ N₀, execOne N₀ m st s i env = .OutOfFuel :=
      fun N₀ => Classical.byContradiction fun h => hdec ⟨N₀, h⟩
    constructor <;> rintro ⟨N, hN⟩ <;> exfalso
    · have h1 := hN N (Nat.le_refl N)
      rw [exec_cons, hall N] at h1
      exact h1
    · have h1 := hN N (Nat.le_refl N)
      rw [exec_singleton, hall N] at h1
      exact h1

/-- The two-cons restriction of `wp_cons_eq`. A singleton is a cons of `[]`,
so the unrestricted equation rewrites itself; this form keeps `simp`
terminating and lets singletons hit the instruction equations. -/
@[simp, grind =] theorem wp_cons₂_eq {m : Module} {env : HostEnv U} {i j : Instruction}
    {q : Program} {Q : Unit → Assn} {epost : EAssn} {st : Store U} {s : Locals} :
    Std.WP.wp (⟨m, env, i :: j :: q⟩ : Code) Q epost st s ↔
      Std.WP.wp (⟨m, env, [i]⟩ : Code)
        (fun _ => Std.WP.wp (⟨m, env, j :: q⟩ : Code) Q epost) epost st s :=
  wp_cons_eq

/-! ## Triples -/

theorem Triple.of_wp_iff {c : Code} {pre : Assn} {Q : Unit → Assn} {epost : EAssn}
    (h : ∀ st s, pre st s → Std.WP.wp c Q epost st s) :
    Triple c pre Q epost := by
  refine Triple.iff.mpr ?_
  intro st s hpre
  exact h st s hpre

@[spec] theorem Spec.nil {m : Module} {env : HostEnv U} {Q : Unit → Assn}
    {epost : EAssn} :
    Triple (⟨m, env, []⟩ : Code) (Q ()) Q epost :=
  Triple.of_wp_iff fun _ _ h => wp_nil_eq.mpr h

@[spec] theorem Spec.cons {m : Module} {env : HostEnv U} {i j : Instruction}
    {q : Program} {Q : Unit → Assn} {epost : EAssn} :
    ⦃ Std.WP.wp (⟨m, env, [i]⟩ : Code)
        (fun _ => Std.WP.wp (⟨m, env, j :: q⟩ : Code) Q epost) epost ⦄
      (⟨m, env, i :: j :: q⟩ : Code)
      ⦃ Q; epost ⦄ :=
  Triple.of_wp_iff fun _ _ h => wp_cons_eq.mpr h

/-! ## Frame and stack computation lemmas

The spec layer states reads with total functions: `s.values[i]!`,
`Value.asI32`, `Locals.get`, `Locals.set?`. The lemmas here let `grind`
compute them over cons-shaped frames when it discharges the
verification conditions. -/

@[simp] theorem Locals.params_mk {ps ls vs : List Value} :
    (Locals.mk ps ls vs).params = ps := rfl

@[simp] theorem Locals.locals_mk {ps ls vs : List Value} :
    (Locals.mk ps ls vs).locals = ls := rfl

@[simp] theorem Locals.values_mk {ps ls vs : List Value} :
    (Locals.mk ps ls vs).values = vs := rfl

@[simp, grind =] theorem Option.get!_some' {α} [Inhabited α] (v : α) :
    (some v).get! = v := rfl

/-- The payload of an `i32`; every other value reads as `0`. -/
def Value.asI32 : Value → UInt32
  | .i32 n => n
  | _ => 0

@[simp, grind =] theorem Value.asI32_i32 (n : UInt32) :
    (Value.i32 n).asI32 = n := rfl

@[simp, grind =] theorem getElem!_cons_zero {α} [Inhabited α] (v : α)
    (vs : List α) : (v :: vs)[0]! = v := by simp

@[simp, grind =] theorem getElem!_cons_one {α} [Inhabited α] (v w : α)
    (vs : List α) : (v :: w :: vs)[1]! = w := by simp

@[simp, grind =] theorem head!_cons {α} [Inhabited α] (v : α) (vs : List α) :
    (v :: vs).head! = v := rfl

@[simp, grind =] theorem drop_one_cons {α} (v : α) (vs : List α) :
    (v :: vs).drop 1 = vs := rfl

@[simp, grind =] theorem drop_two_cons {α} (v w : α) (vs : List α) :
    (v :: w :: vs).drop 2 = vs := rfl

@[simp, grind =] theorem Locals.get_cons_zero {v : Value} {ps ls vs : List Value} :
    Locals.get ⟨v :: ps, ls, vs⟩ 0 = some v := by
  simp [Locals.get]

@[simp, grind =] theorem Locals.get_cons_succ {v : Value} {ps ls vs : List Value}
    {n : Nat} :
    Locals.get ⟨v :: ps, ls, vs⟩ (n + 1) = Locals.get ⟨ps, ls, vs⟩ n := by
  simp only [Locals.get, List.length_cons]
  by_cases h1 : n < ps.length
  · simp [h1, Nat.succ_lt_succ h1]
  · have h2 : ¬ n + 1 < ps.length + 1 := by omega
    simp only [h1, h2, ite_false]
    by_cases h3 : n < ps.length + ls.length
    · have h4 : n + 1 < ps.length + 1 + ls.length := by omega
      simp [h3, h4, Nat.succ_sub_succ]
    · have h4 : ¬ n + 1 < ps.length + 1 + ls.length := by omega
      simp [h3, h4]

@[simp, grind =] theorem Locals.get_nil {ls vs : List Value} {n : Nat} :
    Locals.get ⟨[], ls, vs⟩ n = ls[n]? := by
  simp only [Locals.get, List.length_nil, Nat.not_lt_zero, ite_false,
    Nat.zero_add, Nat.sub_zero]
  by_cases h : n < ls.length
  · simp [h]
  · simp only [h, ite_false]
    exact (List.getElem?_eq_none (by omega)).symm

@[simp, grind =] theorem Locals.get_mk {ps ls vs : List Value} {n : Nat} :
    Locals.get ⟨ps, ls, vs⟩ n = (ps ++ ls)[n]? := by
  simp only [Locals.get]
  by_cases h1 : n < ps.length
  · simp [h1, List.getElem?_append_left h1]
  · simp only [h1, ite_false]
    by_cases h2 : n < ps.length + ls.length
    · rw [List.getElem?_append_right (by omega)]
      simp [h2]
    · rw [List.getElem?_append_right (by omega)]
      have : ls.length ≤ n - ps.length := by omega
      simp [h2, List.getElem?_eq_none this]

@[grind =] theorem Locals.set?_mk {ps ls vs : List Value} {n : Nat} {v : Value} :
    Locals.set? ⟨ps, ls, vs⟩ n v =
      if n < ps.length then some ⟨ps.set n v, ls, vs⟩
      else if n < ps.length + ls.length then
        some ⟨ps, ls.set (n - ps.length) v, vs⟩
      else none := rfl

@[simp, grind =] theorem Locals.set?_cons_zero {p v : Value}
    {ps ls vs : List Value} :
    Locals.set? ⟨p :: ps, ls, vs⟩ 0 v = some ⟨v :: ps, ls, vs⟩ := by
  simp [Locals.set?]

@[simp, grind =] theorem Locals.set?_cons_succ {p v : Value}
    {ps ls vs : List Value} {n : Nat} :
    Locals.set? ⟨p :: ps, ls, vs⟩ (n + 1) v =
      (Locals.set? ⟨ps, ls, vs⟩ n v).map
        fun s' => ⟨p :: s'.params, s'.locals, s'.values⟩ := by
  simp only [Locals.set?, List.length_cons]
  by_cases h1 : n < ps.length
  · simp [h1, Nat.succ_lt_succ h1]
  · have h2 : ¬ n + 1 < ps.length + 1 := by omega
    simp only [h1, h2, ite_false]
    by_cases h3 : n < ps.length + ls.length
    · have h4 : n + 1 < ps.length + 1 + ls.length := by omega
      simp [h3, h4, Nat.succ_sub_succ]
    · have h4 : ¬ n + 1 < ps.length + 1 + ls.length := by omega
      simp [h3, h4]

@[simp, grind =] theorem Locals.set?_nil_cons_succ {l v : Value}
    {ls vs : List Value} {n : Nat} :
    Locals.set? ⟨[], l :: ls, vs⟩ (n + 1) v =
      (Locals.set? ⟨[], ls, vs⟩ n v).map
        fun s' => ⟨[], l :: s'.locals, s'.values⟩ := by
  simp only [Locals.set?, List.length_nil, List.length_cons, Nat.not_lt_zero,
    ite_false, Nat.zero_add, Nat.sub_zero]
  by_cases h : n < ls.length
  · simp [Nat.succ_lt_succ h, h]
  · have h2 : ¬ n + 1 < ls.length + 1 := by omega
    simp [h, h2]

/-! ## `gen` bridges

The same computations, keyed on a hypothesis equation and tagged
`@[grind gen]`. Their E-matching instances are implications stated at
the graph term, so a `grind norm` rule cannot trivialize them
(lean4#11498): the bridge evaluates a term over a symbolic state that a
hypothesis equates to a literal. Each bridge keys on the `Locals.mk` or
constructor equation, since a gadget rooted in `List.cons` does not
activate from the ambient rule set. -/
section GenBridges

@[grind gen] theorem get_of_eq {s : Locals} {ps ls vs : List Value}
    (h : s = ⟨ps, ls, vs⟩) (n : Nat) : s.get n = (ps ++ ls)[n]? := by
  subst h; exact Locals.get_mk

@[grind gen] theorem set?_of_eq {s : Locals} {ps ls vs : List Value}
    (h : s = ⟨ps, ls, vs⟩) (n : Nat) (v : Value) :
    s.set? n v = Locals.set? ⟨ps, ls, vs⟩ n v := by subst h; rfl

@[grind gen] theorem params_of_eq {s : Locals} {ps ls vs : List Value}
    (h : s = ⟨ps, ls, vs⟩) : s.params = ps := by subst h; rfl

@[grind gen] theorem locals_of_eq {s : Locals} {ps ls vs : List Value}
    (h : s = ⟨ps, ls, vs⟩) : s.locals = ls := by subst h; rfl

@[grind gen] theorem values_of_eq {s : Locals} {ps ls vs : List Value}
    (h : s = ⟨ps, ls, vs⟩) : s.values = vs := by subst h; rfl

@[grind gen] theorem append_locals_of_eq {s : Locals} {ps ls vs : List Value}
    (h : s = ⟨ps, ls, vs⟩) : s.params ++ s.locals = ps ++ ls := by
  subst h; rfl

@[grind gen] theorem appended_get?_of_eq {s : Locals} {ps ls vs : List Value}
    (h : s = ⟨ps, ls, vs⟩) (n : Nat) :
    (s.params ++ s.locals)[n]? = (ps ++ ls)[n]? := by subst h; rfl

@[grind gen] theorem params_len_of_eq {s : Locals} {ps ls vs : List Value}
    (h : s = ⟨ps, ls, vs⟩) : s.params.length = ps.length := by subst h; rfl

@[grind gen] theorem locals_len_of_eq {s : Locals} {ps ls vs : List Value}
    (h : s = ⟨ps, ls, vs⟩) : s.locals.length = ls.length := by subst h; rfl

@[grind gen] theorem values_len_of_eq {s : Locals} {ps ls vs : List Value}
    (h : s = ⟨ps, ls, vs⟩) : s.values.length = vs.length := by subst h; rfl

@[grind gen] theorem get!_of_eq {α} [Inhabited α] {o : Option α} {v : α}
    (h : o = some v) : o.get! = v := by subst h; rfl

@[grind gen] theorem isSome_of_eq {α} {o : Option α} {v : α}
    (h : o = some v) : o.isSome = true := by subst h; rfl

@[grind gen] theorem asI32_of_eq {v : Value} {n : UInt32}
    (h : v = .i32 n) : v.asI32 = n := by subst h; rfl

/-! The cons-keyed bridges activate where a cons literal is visible in
the goal; the `Locals`-keyed bridges above cover the positions where it
is not. -/

@[grind gen] theorem append_of_eq {α} {xs : List α} {a : α} {l : List α}
    (h : xs = a :: l) (ys : List α) : xs ++ ys = a :: (l ++ ys) := by
  subst h; rfl

@[grind gen] theorem getElem?_zero_of_eq {α} {xs : List α} {a : α}
    {l : List α} (h : xs = a :: l) : xs[0]? = some a := by subst h; rfl

@[grind gen] theorem getElem?_succ_of_eq {α} {xs : List α} {a : α}
    {l : List α} (h : xs = a :: l) (n : Nat) : xs[n + 1]? = l[n]? := by
  subst h; simp

@[grind gen] theorem getElem!_zero_of_eq {α} [Inhabited α] {xs : List α}
    {a : α} {l : List α} (h : xs = a :: l) : xs[0]! = a := by subst h; rfl

@[grind gen] theorem getElem!_succ_of_eq {α} [Inhabited α] {xs : List α}
    {a : α} {l : List α} (h : xs = a :: l) (n : Nat) :
    xs[n + 1]! = l[n]! := by
  subst h; simp [List.getElem!_eq_getElem?_getD]

@[grind gen] theorem head!_of_eq {α} [Inhabited α] {xs : List α} {a : α}
    {l : List α} (h : xs = a :: l) : xs.head! = a := by subst h; rfl

@[grind gen] theorem tail_of_eq {α} {xs : List α} {a : α} {l : List α}
    (h : xs = a :: l) : xs.tail = l := by subst h; rfl

@[grind gen] theorem length_of_eq {α} {xs : List α} {a : α} {l : List α}
    (h : xs = a :: l) : xs.length = l.length + 1 := by subst h; rfl

@[grind gen] theorem length_nil_of_eq {α} {xs : List α}
    (h : xs = ([] : List α)) : xs.length = 0 := by subst h; rfl

@[grind gen] theorem drop_succ_of_eq {α} {xs : List α} {a : α} {l : List α}
    (h : xs = a :: l) (n : Nat) : xs.drop (n + 1) = l.drop n := by
  subst h; rfl

@[grind gen] theorem take_succ_of_eq {α} {xs : List α} {a : α} {l : List α}
    (h : xs = a :: l) (n : Nat) : xs.take (n + 1) = a :: l.take n := by
  subst h; rfl

@[grind gen] theorem set_zero_of_eq {α} {xs : List α} {a : α} {l : List α}
    (h : xs = a :: l) (v : α) : xs.set 0 v = v :: l := by subst h; rfl

@[grind gen] theorem set_succ_of_eq {α} {xs : List α} {a : α} {l : List α}
    (h : xs = a :: l) (n : Nat) (v : α) :
    xs.set (n + 1) v = a :: l.set n v := by
  subst h; rfl

end GenBridges

/-- Weaken the normal postcondition of an applied `wp`. -/
theorem wp_mono_post {c : Code} {Q Q' : Unit → Assn} {epost : EAssn}
    {st : Store U} {s : Locals}
    (h : ∀ st' s', Q () st' s' → Q' () st' s')
    (hwp : Std.WP.wp c Q epost st s) : Std.WP.wp c Q' epost st s := by
  rw [wp_apply] at hwp ⊢
  exact Code.wp_mono
    (contPost_mono (fun st' s' => h st' s') (fun _ _ _ h => h)) hwp

/-! ## Instruction equations

One `@[simp]` equation per fuel-constant instruction, mirroring the
`execOne` arm on the singleton program, including the `Invalid` exits. -/

/-- Prove a singleton-instruction `wp` equation: split the statement's
`match`, then compute `execOne` per branch. -/
macro "wasm_eq" : tactic => `(tactic|
  (rw [wp_apply]
   repeat' split
   all_goals
     first
     | exact Code.wp_of_const_succ (k := .Fallthrough _ _)
         (fun fuel => by rw [exec_singleton]; simp_all [execOne.eq_def]) _
     | exact Code.wp_of_const_succ (k := .Invalid _)
         (fun fuel => by rw [exec_singleton]; simp_all [execOne.eq_def]) _
     | exact Code.wp_of_const_succ (k := .Trap _ _)
         (fun fuel => by rw [exec_singleton]; simp_all [execOne.eq_def]) _
     | exact Code.wp_of_const_succ (k := .Break _ _ _)
         (fun fuel => by rw [exec_singleton]; simp_all [execOne.eq_def]) _))

section Equations

variable {m : Module} {env : HostEnv U} {Q : Unit → Assn} {epost : EAssn}
  {st : Store U} {s : Locals}

@[simp, grind =] theorem wp_const_eq {v : UInt32} :
    Std.WP.wp (⟨m, env, [.const v]⟩ : Code) Q epost st s ↔
      Q () st { s with values := .i32 v :: s.values } := by
  wasm_eq

@[simp, grind =] theorem wp_constI64_eq {v : UInt64} :
    Std.WP.wp (⟨m, env, [.constI64 v]⟩ : Code) Q epost st s ↔
      Q () st { s with values := .i64 v :: s.values } := by
  wasm_eq

@[simp, grind =] theorem wp_add_eq :
    Std.WP.wp (⟨m, env, [.add]⟩ : Code) Q epost st s ↔
      (match s.values with
       | .i32 a :: .i32 b :: vs => Q () st { s with values := .i32 (a + b) :: vs }
       | _ => ∀ st' s', epost (.Invalid "add: ill-shaped operand stack") st' s') := by
  wasm_eq

@[simp, grind =] theorem wp_sub_eq :
    Std.WP.wp (⟨m, env, [.sub]⟩ : Code) Q epost st s ↔
      (match s.values with
       | .i32 a :: .i32 b :: vs => Q () st { s with values := .i32 (b - a) :: vs }
       | _ => ∀ st' s', epost (.Invalid "sub: ill-shaped operand stack") st' s') := by
  wasm_eq

@[simp, grind =] theorem wp_mul_eq :
    Std.WP.wp (⟨m, env, [.mul]⟩ : Code) Q epost st s ↔
      (match s.values with
       | .i32 a :: .i32 b :: vs => Q () st { s with values := .i32 (a * b) :: vs }
       | _ => ∀ st' s', epost (.Invalid "mul: ill-shaped operand stack") st' s') := by
  wasm_eq

@[simp, grind =] theorem wp_eqz_eq :
    Std.WP.wp (⟨m, env, [.eqz]⟩ : Code) Q epost st s ↔
      (match s.values with
       | .i32 a :: vs =>
           Q () st { s with values := .i32 (if a = 0 then 1 else 0) :: vs }
       | _ => ∀ st' s', epost (.Invalid "eqz: ill-shaped operand stack") st' s') := by
  wasm_eq

@[simp, grind =] theorem wp_localGet_eq {n : Nat} :
    Std.WP.wp (⟨m, env, [.localGet n]⟩ : Code) Q epost st s ↔
      (match s.get n with
       | some v => Q () st { s with values := v :: s.values }
       | none => ∀ st' s',
           epost (.Invalid "localGet index out of bounds") st' s') := by
  wasm_eq

@[simp, grind =] theorem wp_localSet_eq {n : Nat} :
    Std.WP.wp (⟨m, env, [.localSet n]⟩ : Code) Q epost st s ↔
      (match s.values with
       | v :: vs => match s.set? n v with
         | some s' => Q () st { s' with values := vs }
         | none => ∀ st' s',
             epost (.Invalid "localSet index out of bounds") st' s'
       | _ => ∀ st' s',
           epost (.Invalid "localSet with empty stack") st' s') := by
  wasm_eq

@[simp, grind =] theorem wp_localTee_eq {n : Nat} :
    Std.WP.wp (⟨m, env, [.localTee n]⟩ : Code) Q epost st s ↔
      (match s.values with
       | v :: _ => match s.set? n v with
         | some s' => Q () st s'
         | none => ∀ st' s',
             epost (.Invalid "localTee index out of bounds") st' s'
       | _ => ∀ st' s',
           epost (.Invalid "localTee with empty stack") st' s') := by
  wasm_eq

@[simp, grind =] theorem wp_remU_eq :
    Std.WP.wp (⟨m, env, [.remU]⟩ : Code) Q epost st s ↔
      (match s.values with
       | .i32 b :: .i32 a :: vs =>
         if b = 0 then ∀ s', epost (.Trap "integer divide by zero") st s'
         else Q () st { s with values := .i32 (a % b) :: vs }
       | _ => ∀ st' s', epost (.Invalid "remU: ill-shaped operand stack") st' s') := by
  wasm_eq

@[simp, grind =] theorem wp_br_if_eq {n : Nat} :
    Std.WP.wp (⟨m, env, [.br_if n]⟩ : Code) Q epost st s ↔
      (match s.values with
       | .i32 c :: vs =>
         if c = 0 then Q () st { s with values := vs }
         else epost (.Break n) st { s with values := vs }
       | _ => ∀ st' s', epost (.Invalid "br_if: ill-shaped operand stack") st' s') := by
  wasm_eq

end Equations

/-! ## Instruction specifications

One `@[spec]` triple per fuel-constant instruction, in total style: reads
are `s.values[i]!`, `Value.asI32`, `Locals.get`, `Locals.set?`; the
partiality of an instruction is one closed `⌜∃ …⌝` guard. Nothing is
schematic, so every verification condition is metavariable-free and
`finish` computes it with the lemmas above. -/

@[spec] theorem Spec.const {m : Module} {env : HostEnv U} {v : UInt32}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => Q () st { s with values := .i32 v :: s.values } ⦄
      (⟨m, env, [.const v]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  rw [wp_const_eq]
  exact hpre

@[spec] theorem Spec.constI64 {m : Module} {env : HostEnv U} {v : UInt64}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => Q () st { s with values := .i64 v :: s.values } ⦄
      (⟨m, env, [.constI64 v]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  rw [wp_constI64_eq]
  exact hpre

@[spec] theorem Spec.add {m : Module} {env : HostEnv U}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => (⌜s.values[0]! = .i32 s.values[0]!.asI32 ∧
          s.values[1]! = .i32 s.values[1]!.asI32 ∧ 2 ≤ s.values.length⌝ : Prop) ⊓
        Q () st { s with
          values := .i32 (s.values[0]!.asI32 + s.values[1]!.asI32)
            :: s.values.drop 2 } ⦄
      (⟨m, env, [.add]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  simp only [meet_prop_eq_and, ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, h1, hlen⟩, hq⟩ := hpre
  rcases hv : s.values with _ | ⟨v0, _ | ⟨v1, vs⟩⟩ <;> rw [hv] at hlen h0 h1 hq
  · simp at hlen
  · simp at hlen
  · rw [wp_add_eq, hv]
    simp only [getElem!_cons_zero, getElem!_cons_one, drop_two_cons] at h0 h1 hq
    rw [h0, h1]
    simpa [← h0, ← h1] using hq

@[spec] theorem Spec.sub {m : Module} {env : HostEnv U}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => (⌜s.values[0]! = .i32 s.values[0]!.asI32 ∧
          s.values[1]! = .i32 s.values[1]!.asI32 ∧ 2 ≤ s.values.length⌝ : Prop) ⊓
        Q () st { s with
          values := .i32 (s.values[1]!.asI32 - s.values[0]!.asI32)
            :: s.values.drop 2 } ⦄
      (⟨m, env, [.sub]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  simp only [meet_prop_eq_and, ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, h1, hlen⟩, hq⟩ := hpre
  rcases hv : s.values with _ | ⟨v0, _ | ⟨v1, vs⟩⟩ <;> rw [hv] at hlen h0 h1 hq
  · simp at hlen
  · simp at hlen
  · rw [wp_sub_eq, hv]
    simp only [getElem!_cons_zero, getElem!_cons_one, drop_two_cons] at h0 h1 hq
    rw [h0, h1]
    simpa [← h0, ← h1] using hq

@[spec] theorem Spec.mul {m : Module} {env : HostEnv U}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => (⌜s.values[0]! = .i32 s.values[0]!.asI32 ∧
          s.values[1]! = .i32 s.values[1]!.asI32 ∧ 2 ≤ s.values.length⌝ : Prop) ⊓
        Q () st { s with
          values := .i32 (s.values[0]!.asI32 * s.values[1]!.asI32)
            :: s.values.drop 2 } ⦄
      (⟨m, env, [.mul]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  simp only [meet_prop_eq_and, ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, h1, hlen⟩, hq⟩ := hpre
  rcases hv : s.values with _ | ⟨v0, _ | ⟨v1, vs⟩⟩ <;> rw [hv] at hlen h0 h1 hq
  · simp at hlen
  · simp at hlen
  · rw [wp_mul_eq, hv]
    simp only [getElem!_cons_zero, getElem!_cons_one, drop_two_cons] at h0 h1 hq
    rw [h0, h1]
    simpa [← h0, ← h1] using hq

@[spec] theorem Spec.eqz {m : Module} {env : HostEnv U}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => (⌜s.values[0]! = .i32 s.values[0]!.asI32 ∧
          1 ≤ s.values.length⌝ : Prop) ⊓
        Q () st { s with
          values := .i32 (if s.values[0]!.asI32 = 0 then 1 else 0)
            :: s.values.drop 1 } ⦄
      (⟨m, env, [.eqz]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  simp only [meet_prop_eq_and, ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, hlen⟩, hq⟩ := hpre
  rcases hv : s.values with _ | ⟨v0, vs⟩ <;> rw [hv] at hlen h0 hq
  · simp at hlen
  · rw [wp_eqz_eq, hv]
    simp only [getElem!_cons_zero, drop_one_cons] at h0 hq
    rw [h0]
    simpa [← h0] using hq

@[spec] theorem Spec.localGet {m : Module} {env : HostEnv U} {n : Nat}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => (⌜(s.get n).isSome = true⌝ : Prop) ⊓
        Q () st { s with values := (s.get n).get! :: s.values } ⦄
      (⟨m, env, [.localGet n]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  simp only [meet_prop_eq_and, ofProp_prop_eq] at hpre
  obtain ⟨hsome, hq⟩ := hpre
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  rw [wp_localGet_eq, hv]
  simp only [hv, Option.get!_some] at hq
  exact hq

@[spec] theorem Spec.localSet {m : Module} {env : HostEnv U} {n : Nat}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => (⌜∃ v vs, s.values = v :: vs⌝ : Prop) ⊓
        (⌜(s.set? n s.values.head!).isSome = true⌝ : Prop) ⊓
        Q () st { (s.set? n s.values.head!).get! with values := s.values.tail } ⦄
      (⟨m, env, [.localSet n]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  simp only [meet_prop_eq_and, ofProp_prop_eq] at hpre
  obtain ⟨⟨⟨v, vs, hv⟩, hsome⟩, hq⟩ := hpre
  obtain ⟨s', hset⟩ := Option.isSome_iff_exists.mp hsome
  rw [wp_localSet_eq, hv]
  dsimp only
  rw [hv, head!_cons] at hset
  rw [hset]
  simp only [hv, head!_cons, hset, Option.get!_some, List.tail_cons] at hq
  exact hq

@[spec] theorem Spec.localTee {m : Module} {env : HostEnv U} {n : Nat}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => (⌜∃ v vs, s.values = v :: vs⌝ : Prop) ⊓
        (⌜(s.set? n s.values.head!).isSome = true⌝ : Prop) ⊓
        Q () st (s.set? n s.values.head!).get! ⦄
      (⟨m, env, [.localTee n]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  simp only [meet_prop_eq_and, ofProp_prop_eq] at hpre
  obtain ⟨⟨⟨v, vs, hv⟩, hsome⟩, hq⟩ := hpre
  obtain ⟨s', hset⟩ := Option.isSome_iff_exists.mp hsome
  rw [wp_localTee_eq, hv]
  dsimp only
  rw [hv, head!_cons] at hset
  rw [hset]
  simp only [hv, head!_cons, hset, Option.get!_some] at hq
  exact hq

@[spec] theorem Spec.remU {m : Module} {env : HostEnv U}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => (⌜s.values[0]! = .i32 s.values[0]!.asI32 ∧
        s.values[1]! = .i32 s.values[1]!.asI32 ∧ 2 ≤ s.values.length ∧
        s.values[0]!.asI32 ≠ 0⌝ : Prop) ⊓
      Q () st { s with
        values := .i32 (s.values[1]!.asI32 % s.values[0]!.asI32)
          :: s.values.drop 2 } ⦄
      (⟨m, env, [.remU]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  simp only [meet_prop_eq_and, ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, h1, hlen, hnz⟩, hq⟩ := hpre
  rcases hv : s.values with _ | ⟨v0, _ | ⟨v1, vs⟩⟩ <;> rw [hv] at hlen h0 h1 hnz hq
  · simp at hlen
  · simp at hlen
  · rw [wp_remU_eq, hv]
    simp only [getElem!_cons_zero, getElem!_cons_one, drop_two_cons] at h0 h1 hnz hq
    rw [h0, h1]
    dsimp only
    rw [ite_eq_right hnz]
    simpa [← h0, ← h1] using hq

@[spec] theorem Spec.br_if {m : Module} {env : HostEnv U} {n : Nat}
    {Q : Unit → Assn} {epost : EAssn} :
    ⦃ fun st s => (⌜s.values[0]! = .i32 s.values[0]!.asI32 ∧
        1 ≤ s.values.length⌝ : Prop) ⊓
      ((⌜s.values[0]!.asI32 ≠ 0⌝ : Prop) ⇨
        epost (.Break n) st { s with values := s.values.drop 1 }) ⊓
      ((⌜s.values[0]!.asI32 = 0⌝ : Prop) ⇨
        Q () st { s with values := s.values.drop 1 }) ⦄
      (⟨m, env, [.br_if n]⟩ : Code)
      ⦃ Q; epost ⦄ := by
  refine Triple.of_wp_iff fun st s hpre => ?_
  simp only [meet_prop_eq_and, ofProp_prop_eq, himp_prop_eq_imp] at hpre
  obtain ⟨⟨⟨h0, hlen⟩, htaken⟩, hfall⟩ := hpre
  rcases hv : s.values with _ | ⟨v0, vs⟩ <;> rw [hv] at hlen h0 htaken hfall
  · simp at hlen
  · rw [wp_br_if_eq, hv]
    simp only [getElem!_cons_zero, drop_one_cons] at h0 htaken hfall
    rw [h0]
    dsimp only
    by_cases hc : v0.asI32 = 0
    · rw [ite_eq_left hc]
      exact hfall hc
    · rw [ite_eq_right hc]
      exact htaken hc

end Wasm

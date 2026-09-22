# wasm-wp: `Std.WP` for a deep embedding

A `Std.WP.WP` instance for the [talos](https://github.com/cajal-technologies/talos)
Wasm interpreter, with program proofs driven by the `vcgen` tactic. The
interpreter is a deep embedding: programs are instruction lists, and the
semantics is a fuel-bounded `exec`. The instance shows that `Std.WP`'s
triple notation, `@[spec]` tables, invariant alternatives and
grind-mode discharge apply to such an embedding, outside `WPMonad`.

The package recompiles the interpreter sources through the `Interpreter`
symlink, so the talos tree itself stays untouched.

## Build

```
lake build
```

Toolchain: `leanprover/lean4:v4.35.0-rc2` (see `lean-toolchain`).

## Tour

| File | Content |
| --- | --- |
| `WasmWP/Basic.lean` | The instance: `Code`, assertions `Store U → Locals → Prop`, exit postconditions `Exit → Assn`, the fuel-free `Code.wp`. |
| `WasmWP/Spec.lean` | The sequencing law, one `wp_<instr>_eq` equation and one `@[spec]` triple per instruction, and the state computation lemmas. |
| `WasmWP/Call.lean` | `Spec.call_tw`, the fuel-free `TerminatesWith.of_triple` bridge, and the `wp_body` prologue tactic. |
| `WasmWP/Block.lean` | `block` and `br`. |
| `WasmWP/Loop.lean` | `Spec.loop` over a `LoopInvariant` and a `LoopVariant`, proved by strong induction on the variant. |
| `WasmWP/Examples.lean` | Straight-line demos and the compositional call chain `add2` → `addTwice` → client. |
| `WasmWP/Gcd.lean` | Euclid's gcd: a loop with invariant and variant, verified end to end. |

Public specs never mention fuel. `TerminatesWith.of_triple` turns a
triple on a function body into the talos-level `TerminatesWith`
statement, and `Spec.call_tw` consumes such a statement at a `call`
site, so verified functions compose as black boxes.

Every verification condition that `vcgen` emits is discharged by
`finish`. One `vcgen` call verifies the gcd function, a loop whose
eleven-instruction body exits through a `block`/`br_if` and rotates the
pair through a scratch local. `Spec.loop` comes from the spec table,
and the invariant and variant come from the alternatives:

```lean
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
```

Two grind disciplines carry the proof, both worked out in
`mwe/NormInstanceDiscard.lean` and `Spec.lean`'s `GenBridges` section.
The spine computation lemmas enter grind's normalization set per proof
file, never globally, and the linking lemmas stay E-matching-only,
because a norm rule discards the E-matching instances that link a
symbolic term to its value (lean4#11498). The `@[grind gen]` bridges
state those computations keyed on a hypothesis equation, so their
instances survive normalization and evaluate terms over a symbolic
state that the invariant equates to a literal.

## `mwe/`: findings

Self-contained files, no talos imports, compiled with a bare `lean` on
the pinned toolchain. Each isolates one engine behavior met during this
development.

| File | Finding |
| --- | --- |
| `MatcherStall.lean` | An assertion-position matcher applied to a constructor is not iota-reduced. |
| `SchematicGuards.lean` | An mk-rooted guard equation assigns symbolic cells and refuses literal ones. |
| `ConsRootedGuards.lean` | A cons-rooted guard equation assigns its first component and stops. |
| `CleanupVCEta.lean` | The trivial-discharge pass lacks structure eta. |
| `NormInstanceDiscard.lean` | A `grind norm` rule cancels E-matching instances of the same equation (lean4#11498, cf. #11990). |

## Limitations

The host state is `Unit`; the `Universal.State` instantiation waits on
a talos fix for `SmallStep`'s termination proofs on current toolchains.
A `@[grind gen]` bridge whose defining hypothesis is a `List.cons`
equation activates only when a cons literal is visible in the goal, so
the bridge set keys the state computations on the `Locals.mk` equation;
`Spec.lean`'s `GenBridges` section documents the pattern.

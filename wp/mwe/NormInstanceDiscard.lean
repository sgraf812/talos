/-!
# A `grind norm` rule cancels E-matching instances of the same equation

One unary function, one equation, both `grind` rule kinds. As an
E-matching rule (`grind =`), `f_zero` proves `example₁`: the pattern
`f 0` matches `f x` through the class `{x, 0}`, the instance `f 0 = 1`
enters the graph, and congruence transports the value to `f x`. As a
normalization rule on top (`grind norm`), the same theorem breaks the
same goal (`example₂`): grind normalizes the instance before asserting
it, the instance's left-hand side `f 0` is a redex of the norm rule, the
instance trivializes to `1 = 1`, and grind discards it. The bridge term
`f 0` never enters the graph, and no rule rewrites `f x` itself, because
`x` is a free variable. The diagnostics show the damage: `f_zero ↦ 1`
fires and leaves no trace, and cutsat exhibits the model `x := 0,
f x := 2`, which violates `f_zero` outright.

The interaction is anti-monotone in general: a norm rule cancels every
E-matching instance whose left-hand side it can evaluate, whether the
instance comes from the same theorem or from any other. Registering a
theorem in both kinds is the total case, where the E-matching side
contributes nothing beyond the norm side. This is the mechanism behind
lean4#11990, where the built-in normalization of `UInt16.toNat 0` plays
the norm role against a user-supplied `grind [UInt16.toNat_zero]`.

`example₃` shows the workaround that issue's reporter found, explained:
generalize the scrutinee to a variable with a defining hypothesis. The
instance is then the implication `x = 0 → f x = 1`, stated at the graph
term. Its left-hand side is no norm redex, the hypothesis discharges
from the e-graph by modus ponens, and the goal closes with the norm
rule still active. Plain `grind =` carries this; the reporter's
`grind gen` is needed only when the defining hypothesis introduces
variables the conclusion misses (`(h : xs = a :: l) : xs.length =
l.length + 1` rejects `grind =`, and `gen` compiles the multipattern
`[length xs, cons a l]` instead). A fix in grind would subsume the
workaround: assert E-matching instances transported to the matched
graph occurrence (`f x = 1` instead of `f 0 = 1`) and normalize
afterwards.

Reproduces on v4.35.0-rc2.
-/

def f (n : Nat) : Nat := n + 1

@[grind =] theorem f_zero : f 0 = 1 := rfl

example (x : Nat) (h : x = 0) : f x = 1 := by grind

attribute [grind norm] f_zero

/--
error: `grind` failed
case grind
x : Nat
h : x = 0
h_1 : ¬f x = 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] x = 0
    [prop] ¬f x = 1
  [eqc] False propositions
    [prop] f x = 1
  [eqc] Equivalence classes
    [eqc] {x, 0}
  [cutsat] Assignment satisfying linear constraints
    [assign] x := 0
    [assign] f x := 2
[grind] Diagnostics
  [ematch] E-matching Diagnostics
    [thm] Theorem Instance Count
      [thm] f_zero ↦ 1
-/
#guard_msgs (error) in
example (x : Nat) (h : x = 0) : f x = 1 := by grind

@[grind =] theorem f_zero' {x : Nat} (h : x = 0) : f x = 1 := by
  subst h; rfl

example (x : Nat) (h : x = 0) : f x = 1 := by grind

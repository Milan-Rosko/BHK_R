# carryless pairing

This subproject develops a constructive, effectivity-oriented pairing function `pi : nat -> nat -> nat` built from a Fibonacci/Zeckendorf substrate. The intended pairing is “carryless” in the sense that two inputs are encoded into disjoint structural bands of a Zeckendorf support and then evaluated; the design goal is a pairing that is injective and admits a computable partial inverse on its range.

## Structure

The development is organized around a semantic spine plus a realization layer.

- `S00__bhkcore.v` provides the minimal constructive core (`nat`, `add`, `mul`) and definitional computation laws.
- `S01__carryless.v` is the semantic entry point. It declares the vocabulary (minimal datatypes, order, list operations), states the interfaces and laws for Fibonacci/rank/Zeckendorf and for pairing/unpairing, and defines only transparent compositions (e.g., `eval`, `pi`) that merely assemble declared operations. It also introduces a `Module Type` contract (`CARRYLESS_SIG`) so realizations can be checked against the semantic surface.
- `R01__carryless_realize.v` is the realization layer. It implements parts of the contract as explicit constructions (Definitions/Fixpoints), and may leave unfinished components as Parameters until they are retired.

## Main objects

Within `S01__carryless.v`:

- Fibonacci interface: `fib_pair`, `fib`, and basic equations (`fib_0`, `fib_1`, `fib_SS`), plus rank and delimiter functions (`r`, `B`) with correctness/monotonicity obligations.
- Zeckendorf interface: `zeck : nat -> support` with decidable structural invariants and the evaluation correctness statement `eval (zeck n) = n`.
- Pairing:
  - `pair_support : nat -> nat -> support`
  - `pi : nat -> nat -> nat := eval (pair_support x y)`
  - `unpair : nat -> option (nat * nat)` (partial inverse, intended total on realized codes)
  - effectivity properties: `unpair_pi`, `unpair_sound`, and injectivity `pi_injective`.

## Reading order

1. `S01__carryless.v` (semantic spine; contract and definitions of `eval`/`pi`)
2. `R01__carryless_realize.v` (realized constructions and proof terms)
3. `S00__bhkcore.v` as needed for the base arithmetic nucleus

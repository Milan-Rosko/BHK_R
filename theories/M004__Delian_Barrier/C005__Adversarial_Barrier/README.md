## C005 — Adversarial Barrier

### Overview

C005 establishes the **Adversarial Barrier** as an impossibility theorem within the BHK framework. Under the BHK reading, the barrier is not a meta-theorem about undecidability but a constructive refutation: assuming a certified separator exists leads directly to an inhabitation of False.

The core mechanism is **flip logic**: an adversarial construction that observes a separator's decision function and intentionally outputs code for the opposite class. When combined with the diagonal device from C003, this creates an impredicative loop where the separator must classify a sentence that references the separator's own output.

The barrier demonstrates that no effective decision procedure can simultaneously:
- (i) **Provide total decisions** (`sigma : nat -> bool`)
- (ii) **Certify those decisions** with formal proofs (`Prov (A n)` or `Prov (B n)`)
- (iii) **Respect semantic disjointness** (via soundness)

### Technical Details

Operationally, C005 provides:

- (i) **Semantic context**

   - `A : nat -> Form` (class A sentence family)
   - `B : nat -> Form` (class B sentence family)
   - `Truth : Form -> Prop` (semantic truth predicate)
   - `Semantic_Disjointness : forall n, Truth (A n) -> Truth (B n) -> False`

- (ii) **Separator interface**

   - `SEPARATOR : Type` (record bundling decision and certification)
   - `sigma : nat -> bool` (decision function)
   - `cert : forall n, if sigma n then Prov (A n) else Prov (B n)` (proof certificates)

- (iii) **Flip logic mechanism**

   - `Flip_Logic : SEPARATOR -> nat -> Form`
   - Defined as: `if S.(sigma) n then B n else A n`
   - Intentionally outputs the opposite class

- (iv) **Main barrier theorem**

   - `Adversarial_Barrier : SEPARATOR -> Soundness -> Disjointness -> (exists d D, ...) -> False`
   - Given separator, soundness, disjointness, and diagonal witness, derive False

- (v) **Mirror instance**

   - Connects to C004 mirror lemma
   - Shows separator acts as MirrorParams regulator
   - Demonstrates AsIF collision via soundness

Downstream use is via the Phase-2 entry points:

`theories/M003__Delian_Barrier/C005__Adversarial_Barrier/P2_T__Barrier.v`
`theories/M003__Delian_Barrier/C005__Adversarial_Barrier/P2_T__Mirror_Instance.v`

These export the barrier theorem and its connection to weak forcing.

### Files

- `theories/M003__Delian_Barrier/C005__Adversarial_Barrier/P1_S__Barrier_Definition.v`

Barrier definition and semantic context. Defines SEPARATOR record, Flip_Logic mechanism, and semantic disjointness conditions.

- `theories/M003__Delian_Barrier/C005__Adversarial_Barrier/P2_R__Barrier_Proof.v`

Barrier proof realization. Implements the constructive refutation: shows that separator + diagonal witness + soundness + disjointness implies False.

- `theories/M003__Delian_Barrier/C005__Adversarial_Barrier/P2_T__Barrier.v`

Main impossibility theorem export. Provides the canonical Adversarial_Barrier theorem for downstream use. This is the recommended entry point for resistance constructions.

- `theories/M003__Delian_Barrier/C005__Adversarial_Barrier/P2_T__Mirror_Instance.v`

Mirror lemma application to barrier. Reinterprets the barrier through C004 mirror lemma, showing how the separator creates an AsIF collision that soundness lifts to a Truth collision.

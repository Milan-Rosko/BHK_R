## C005 — Adversarial Barrier

**1 Overview**

C005 reconstructs the adversarial barrier as a **constructive impossibility result** for uniform class separation. A separator is a concrete device that decides a class and provides an internal certificate of that decision. The barrier shows that if the separator is sound with respect to a semantic truth predicate and the classes are disjoint, then a suitable diagonal construction yields a contradiction.

This development is purely intensional and uses no axioms or `Admitted` in its core barrier proof. The diagonal is supplied as an explicit hypothesis that includes a fixed-point truth equivalence and a truth-tracking link between the diagonal sentence and its code.

### 2 Downstream API

- (i) **Definitions (Phase 1):**

   - `A, B : nat -> ATP_Form` — semantic classes (ground truth).
   - `Truth : ATP_Form -> Prop` — semantic truth predicate.
   - `Semantic_Disjointness` — `forall n, Truth (A n) -> Truth (B n) -> False`.
   - `SEPARATOR` — record bundling `sigma : nat -> bool` and a certificate:
     `if sigma n then ATP_Prov (A n) else ATP_Prov (B n)`.
   - `Flip_Logic` — adversarial template: if classified as A, behave as B (and vice versa).

- (ii) **The barrier theorem (Phase 3):**

   - `Adversarial_Barrier` — if a separator is sound and classes are disjoint, and a diagonal witness exists with truth-tracking equivalences, then `False`.

### 3 Design Discipline

- (i) **Device-first:** Solvability is a concrete `SEPARATOR`, not an abstract predicate.
- (ii) **Truth-tracking diagonal:** The diagonal witness provides:

   - `Truth D <-> Truth (Flip_Logic S d)`
   - `Truth (A d) <-> Truth D` and `Truth (B d) <-> Truth D`

- (iii) **Collision:** Run the separator on `d`; soundness yields `Truth (A d)` or `Truth (B d)`; truth tracking links this to `Truth D`, and the flip forces the opposite class, contradicting disjointness.

### 4 Files

- `P1_S__Barrier_Definition.v` — vocabulary: classes, truth, disjointness, separator, flip.
- `P2_R__Barrier_Proof.v` — constructive barrier proof using truth-tracking diagonal.
- `P3_T__Barrier.v` — stable public surface.
- `P3_T__Mirror_Instance.v` — optional mirror-instance adapter (requires representability assumptions).

## C010 — Solvability Thesis

### Overview

C010 establishes the **Solvability Thesis** refutation as the ultimate reductio argument within the BHK framework. Under the BHK reading, the refutation is not a meta-theorem about undecidability but a constructive proof of triviality: assuming universal solvability (every problem class has a certified separator) leads directly to inhabitation of every proposition.

The core result is the **Domino Effect**: Solvability_Thesis → ∀Q. Q. This demonstrates that computational hardness is not an empirical accident but the structural load-bearing beam preventing logical collapse. Removing hardness by asserting universal solvability causes immediate triviality—not gradual degradation but instantaneous explosion where every proposition becomes provable.

The construction generalizes C009's SAT reduction to arbitrary problem classes, showing that the impossibility structure is universal, not specific to SAT. This completes the repository's central impossibility architecture: hardness is a logical necessity.

### Technical Details

Operationally, C010 provides:

- (i) **Problem class definition**

   - `PROBLEM_CLASS : Type` (record bundling positive/negative classes with semantic interpretation)
   - `A : nat -> Form` (positive class)
   - `B : nat -> Form` (negative class)
   - `Truth : Form -> Prop` (semantic truth predicate)
   - `Disjoint : forall n, Truth (A n) -> Truth (B n) -> False`
   - `Sound : forall phi, Prov phi -> Truth phi`

- (ii) **Separator specification**

   - `SEPARATOR : (nat -> Form) -> (nat -> Form) -> Type`
   - `sigma : nat -> bool` (decision function)
   - `cert : forall n, if sigma n then Prov (A n) else Prov (B n)` (proof certificates)

- (iii) **Solvability thesis statement**

   - `Solvability_Thesis : Prop`
   - Defined as: forall Pb : PROBLEM_CLASS, exists S : SEPARATOR Pb.A Pb.B
   - Asserts every problem class admits certified separation

- (iv) **Triviality theorem**

   - `Thesis_Implies_Triviality : Solvability_Thesis -> forall Q : Prop, Q`
   - Proof path: thesis → SAT solver → hardness conservation → ~REFLEXICA → clash with REFLEXICA axiom → False → ex falso Q

- (v) **Domino effect (normalization)**

   - `The_Domino_Effect : Solvability_Thesis -> forall Q : Prop, Q`
   - Public-facing theorem emphasizing cascade: one universal solver breaks everything
   - Alternative name for triviality result highlighting structural collapse

- (vi) **Correctness property**

   - Requires representability: separators from thesis must be effectively computable (diagonalizable)
   - Bridges abstract existence and computational realizability
   - Without representability, separator might exist abstractly without being formulable in proof system

Downstream use is via the Phase-2 entry point:

`theories/M004__Conservation_of_Hardness/C010__Solvability_Thesis/P2_T__Normalization.v`

This exports the Domino Effect as the terminal impossibility result.

### Files

- `theories/M004__Conservation_of_Hardness/C010__Solvability_Thesis/P1_S__Thesis_Definition.v`

Thesis definition and context. Defines PROBLEM_CLASS record, SEPARATOR specification, and Solvability_Thesis statement. Establishes the abstract framework for universal solvability.

- `theories/M004__Conservation_of_Hardness/C010__Solvability_Thesis/P2_R__Triviality_Proof.v`

Triviality proof realization. Implements Thesis_Implies_Triviality via SAT instantiation and hardness conservation. Shows that thesis → SAT solver → separator → RESIST → ~REFLEXICA → clash → False → ∀Q.

- `theories/M004__Conservation_of_Hardness/C010__Solvability_Thesis/P2_T__Normalization.v`

Domino Effect export. Provides The_Domino_Effect as public theorem, emphasizing that universal solvability causes immediate logical collapse. This is the terminal result of the entire Solvability Theory module and the recommended entry point for philosophical reflection on computational hardness as structural necessity.

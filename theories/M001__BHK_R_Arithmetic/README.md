# M001: BHK_R_Arithmetic

## Overview

M001 establishes the foundational computational nucleus under BHK (Brouwer-Heyting-Kolmogorov) interpretation with recursive discipline (BHK_R), extended with additive arithmetic for proof theory. The essential methodology: *proof is construction*, *computation is the proof engine*.

The module provides:
- (i) Minimal inductive arithmetic core with explicit primitive recursion;
- (ii) Carryless pairing via Zeckendorf representation (Fibonacci-based encoding);
- (iii) Additive Hilbert system with formal provability and coding infrastructure;
- (iv) Phase structure discipline: Realizations (R) -> Semantics (S) -> Theorems (T) -> Axioms/Certificates (A).

## BHK_R Discipline

### BHK Interpretation
- **Proposition = Type**: A proposition is identified with the type of its proofs
- **Proof = Construction**: To prove P is to construct an inhabitant of type P
- **Connectives via Introduction**: Meaning given by introduction forms (functions, pairs, sums)

### The R Extension
BHK_R adds three constraints to standard BHK:
- (i) **Minimal Inductive Core**: No large numeric towers or heavyweight libraries
- (ii) **Explicit Primitive Recursion**: Computation via kernel reduction (beta, iota, zeta, transparent delta)
- (iii) **Fixed Phase Structure**: Disciplined construction sequence (R -> S -> T -> A)

### Phase Structure
```
R (Realization)  : Fixpoint/Definition with explicit proof terms
S (Semantics)    : Package realizations behind minimal interfaces (records)
T (Theorems)     : Entry/exit points for downstream use
A (Axiom)        : Certificates forming recursive loop
```

## Construction Sequence

### C000: BHK_R Foundation
The meaning nucleus: defines arithmetic core (nat, add, mul, recursion) and establishes BHK proof semantics. Repository-wide computational foundation.

**Files:**
- **P0__BHK.v**: Arithmetic nucleus, BHK canonical clauses, computation-as-proof discipline
- **P0__Reflexica.v**: REFLEXICA axiom (arithmetic integrity certificate)

### C001: Carryless Pairing
Bijective nat -> nat * nat encoding via Zeckendorf representation (unique Fibonacci sums). Enables arithmetization of syntax without carry propagation.

**Files:**
- **P1_S__Substrate.v**: Arithmetic preliminaries, parity lemmas
- **P2_R__Carryless.v**: Fibonacci sequence realization
- **P2_S__Carryless.v**: Fibonacci interface, Zeckendorf uniqueness
- **P3_R__Injectivity.v**: Injectivity proofs for pairing components
- **P3_S__Injectivity.v**: Injectivity interface
- **P4_R__Pairing.v**: Pairing realization
- **P4_S__Pairing.v**: CL_PAIR interface, band separation (even/odd indices)
- **P5_T__Carryless_Pairing.v**: Public surface, canonical device export
- **P5_T__Effectivity.v**: Computational witnesses (vm_compute tests)
- **P6_A__Reflexica_Certificate.v**: Inversion law under REFLEXICA axiom

### C002: Additive Hilbert System
Minimal proof kernel (Hilbert system with Imp, Bot) with formal provability predicate. Provides coding infrastructure for arithmetization of syntax.

**Files:**
- **P1_S__Kernel_Spec.v**: Specification of proof kernel interface
- **P2_R__Hilbert_Kernel.v**: Hilbert system realization (K, S combinators, modus ponens)
- **P2_S__Provability_Interface.v**: Provability predicate interface
- **P3_R__Additive_Laws.v**: Additive provability laws realization
- **P3_S__Additive_Theory.v**: Additive theory interface
- **P4_R__Coding_Nucleus.v**: Core coding infrastructure
- **P4_R__Coding_Carryless.v**: Carryless coding realization
- **P4_S__Coding.v**: Coding interface
- **P5_T__Proof_Theory.v**: Public surface for proof theory
- **P6_P__Effectivity.v**: Effectivity witnesses

## Core Devices

### Carryless Pairing Device
```coq

Record CL_PAIR : Type := {
  F : nat -> nat;                    (* Fibonacci sequence *)
  r : nat -> nat;                    (* Rank: first F k > n *)
  B : nat -> nat;                    (* Band offset: 2 * r *)
  Z : nat -> list nat;               (* Zeckendorf support *)

  even_band : nat -> list nat;       (* Even indices (for x) *)
  odd_band : nat -> nat -> list nat; (* Odd indices (for y) *)

  pair : nat -> nat -> nat;          (* Encode (x, y) -> n *)
  unpair : nat -> (nat * nat)        (* Decode n -> (x, y) *)
}.

```

### Hilbert Kernel

```coq

Record Hilbert_Kernel : Type := {
  Formula : Type;
  Imp : Formula -> Formula -> Formula;
  Bot : Formula;

  Proof : Formula -> Type;
  K : forall A B, Proof (Imp A (Imp B A));
  S : forall A B C, Proof (Imp (Imp A (Imp B C)) (Imp (Imp A B) (Imp A C)));
  MP : forall A B, Proof (Imp A B) -> Proof A -> Proof B;
}.

```

### Golden Ratio Connection
Zeckendorf representation grounds encoding in phi = (1+sqrt(5))/2:
- **Fibonacci Growth**: F(n) ~ phi^n/sqrt(5)
- **Worst-Case Entropy**: phi has maximal continued fraction complexity
- **Unique Representation**: Every nat has unique Fibonacci sum (no adjacent Fibonacci numbers)
- **Carryless Property**: Addition of Zeckendorf representations never propagates carries

This binding of syntax to golden ratio arithmetic creates the structural hardness exploited by M002 and M003.

## Key Results

### REFLEXICA (Arithmetic Integrity)
```coq
Axiom REFLEXICA : Arithmetic_Integrity
```
The inversion law: `unpair (pair x y) = (x, y)`. Postulated in P0__Reflexica, derived in M003/C008 via resistance.

### Effectivity Witnesses
```coq
Example pair_roundtrip : unpair (pair 3 5) = (3, 5).
Proof. vm_compute. reflexivity. Qed.
```
All core operations reduce under vm_compute: computation validates proofs.

## Philosophical Stance

M001 implements **constructive formalism**:
- **No Classical Axioms**: No LEM, no choice, no extensionality at foundation
- **Computation Primary**: Definitional equality via reduction, not axiomatic equality
- **Explicit Witnesses**: Every existence proof provides concrete construction
- **Phase Discipline**: Clean separation between realization and interface

The BHK_R methodology is **repository-wide and project-agnostic**: any development can adopt this discipline.

## Design Principles

1. **Kernel Conversion**: Prefer definitional equality discharged by eq_refl
2. **Small Facades**: Records/modules over large signatures to reduce coupling
3. **Sequential Intensionality**: Computation explicit, predictable, observable
4. **Single Canonical Reality**: One effective realization per device (no A/B variants)

## Relationship to M002 and M003

M001 provides the **computational substrate** for the impossibility architecture:
- **Arithmetic Core (C000)**: Foundation for all constructions
- **Carryless Encoding (C001)**: Enables diagonal device (C003) and SAT arithmetization (C009)
- **Proof Theory (C002)**: Foundation for diagonal lemma (C003) and mirror lemma (C004)
- **REFLEXICA**: Target of normalization (C008), key to resistance (C007)
- **Golden Ratio**: Links computational hardness to number-theoretic structure

M001 is the *ground floor*: M002 builds self-reference machinery, M003 builds the impossibility architecture.

## Entry Points

- **For arithmetic foundation:** C000 P0__BHK
- **For encoding/pairing:** C001 P5_T__Carryless_Pairing
- **For effectivity tests:** C001 P5_T__Effectivity
- **For proof theory:** C002 P5_T__Proof_Theory
- **For REFLEXICA axiom:** C000 P0__Reflexica (axiom) or M003/C008 (derivation)

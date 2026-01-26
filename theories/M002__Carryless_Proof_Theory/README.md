# M002: Carryless_Proof_Theory

## Overview

M002 provides the core proof-theoretic machinery for self-reference and weak forcing. Building on M001's arithmetic and proof kernel, this module constructs the diagonal lemma (fixed-point mechanism) and the mirror lemma (weak forcing principle).

The module establishes:
- (i) Self-referential sentences via carryless diagonal construction;
- (ii) Weak forcing: non-refutability implies bounded "as-if" witnesses;
- (iii) Bridge between meta-level epistemology and object-level ontology.

These constructions provide the essential ingredients for M003's barrier theorems and impossibility results.

## Construction Sequence

### C003: Carryless Diagonal Lemma

Fixed-point construction for self-referential sentences using carryless encoding from C001. The diagonal device enables sentences that "talk about themselves" via arithmetization.

**Core Idea:** Given a formula template phi(x) with free variable x, construct a sentence D such that D is provably equivalent to phi(code(D)). The sentence D "says" that phi holds of its own code.

**Files:**
- **P1_S__Syntax.v**: Syntax specification for diagonal construction
- **P2_R__Backend.v**: Backend realization for code manipulation
- **P2_R__Compiler.v**: Compiler from syntax to codes
- **P2_T__Diagonal.v**: Public surface exporting diagonal device

**Key Result:**
```coq
Theorem diagonal_lemma :
  forall phi : Formula -> Formula,
  exists D : Formula,
    Provable (Iff D (phi (code D))).
```

### C004: Mirror Lemma

Weak forcing principle: if a sentence is not refutable, then there exist bounded "as-if" witnesses. This bridges the gap between what cannot be disproved and what can be witnessed.

**Core Idea:** Non-refutability at the meta-level translates to witnessable behavior at the object level, within certain bounds. This is weaker than full forcing but sufficient for barrier constructions.

**Files:**
- **P1_S__Context.v**: Context specification for mirror construction
- **P2_R__Mirror_Core.v**: Core mirror mechanism realization
- **P2_R__Mirror_Transport.v**: Transport lemmas for mirror witnesses
- **P2_S__Mirror_Lemma.v**: Mirror lemma interface
- **P3_S__Recursive_Mirror_Lemma.v**: Recursive extension of mirror lemma
- **P3_T__Weakforcing.v**: Public surface for weak forcing

**Key Result:**
```coq
Theorem mirror_lemma :
  forall phi : Formula,
  ~Refutable phi ->
  exists w : Witness, AsIf phi w.
```

## Architectural Role

M002 serves as the **bridge module** between M001's computational substrate and M003's impossibility theorems:

```
M001 (Arithmetic + Proof Kernel)
         |
         v
    +----+----+
    |         |
  C003      C004
(Diagonal) (Mirror)
    |         |
    +----+----+
         |
         v
M003 (Barriers + Impossibility)
```

- **C003 (Diagonal)** provides the self-reference mechanism needed for barrier constructions
- **C004 (Mirror)** provides the weak forcing needed to extract witnesses from non-refutability

## Dependencies

**Imports from M001:**
- C000: Arithmetic core, BHK semantics
- C001: Carryless pairing for code manipulation
- C002: Hilbert kernel, provability predicate, coding infrastructure

**Exports to M003:**
- Diagonal device for self-referential sentence construction
- Mirror/weak forcing for witness extraction
- Combined machinery for barrier theorem proofs

## Key Concepts

### Self-Reference via Diagonalization

The diagonal lemma shows that any sufficiently expressive system can construct self-referential sentences. This is the technical heart of Godel's incompleteness theorems and the foundation for:
- Godel sentences ("I am not provable")
- Liar-like paradoxes (in semantic settings)
- Fixed-point constructions for barriers

### Weak Forcing

Mirror forcing is a bounded version of classical forcing:
- **Classical Forcing:** Non-refutability implies truth in some model
- **Weak Forcing:** Non-refutability implies "as-if" witnesses within bounds

This weaker principle suffices for barrier constructions while remaining constructively acceptable.

## Design Principles

1. **Carryless Foundation**: All coding uses Zeckendorf representation from C001
2. **Explicit Witnesses**: Mirror witnesses are constructively realizable
3. **Minimal Interface**: Public surfaces export only essential devices
4. **Compositional**: C003 and C004 compose cleanly for M003's needs

## Entry Points

- **For diagonal device:** C003 P2_T__Diagonal
- **For weak forcing:** C004 P3_T__Weakforcing
- **For mirror mechanism:** C004 P2_S__Mirror_Lemma

# M003: General_Insolubility_Theorem

## Overview

M003 searches for isomorphisms between obstructive problems and proof-theoretic phenomena. The essential realization: one must differentiate between a semantic truth notion *solvability* and a constructive discipline, *realizability of solvability*.

The module establishes:
- (i) No universal separator can exist for disjoint problem classes;
- (ii) Computational hardness ≡ arithmetic consistency (isomorphic resources);
- (iii) Solvability Thesis → logical triviality (every proposition provable).

The construction sequence: barrier theorems (C005–C006) → resistance laws (C007–C008). The SAT, solvability, and quintic/cubic modules (C009–C012) now live in M004.

## Construction Sequence

### C005: Adversarial_Barrier

Flip logic impossibility: certified separators (decision + proof certificates) lead to semantic collision via Soundness and Disjointness.

**Core Idea:** A separator that can decide membership in disjoint classes P and Q while providing certificates creates a contradiction when fed self-referential sentences from the diagonal lemma.

**Files:**
- **P1_S__Barrier_Definition.v**: Barrier definition and specification
- **P2_R__Barrier_Proof.v**: Proof realization for adversarial barrier
- **P2_T__Barrier.v**: Public barrier theorem
- **P2_T__Mirror_Instance.v**: Mirror lemma application to barrier

**Key Result:**
```coq
Theorem adversarial_barrier :
  ~(exists S : Separator, Certified S /\ Disjoint (domain S)).
```

### C006: Audit_Barrier

Self-verification impossibility: separators cannot satisfy reflection conditions for provability predicates without proving Bot via Löb's rule.

**Core Idea:** A separator that can "audit itself" (verify its own correctness via reflection) triggers Löb's theorem, leading to proof of contradiction.

**Files:**
- **P1_S__Context.v**: Context for audit barrier
- **P2_R__Audit_Logic.v**: Audit logic realization
- **P2_T__Audit_Barrier.v**: Public audit barrier theorem
- **P2_T__Audit_Adapter.v**: Adapter for audit mechanism

**Key Result:**
```coq
Theorem audit_barrier :
  ~(exists S : Separator, Self_Verifying S).
```

### C007: Resistance_Law

Unified impossibility: COMPUTATIONAL_SEPARATOR (bundles separator + diagonal) → False. Self-contained reductio consuming any purported solver.

**Core Idea:** Combining a separator with the diagonal device creates an immediate contradiction. This is the "resistance law": computational separation resists formalization.

**Files:**
- **P1_S__Separation.v**: Separation specification
- **P2_R__Resistance_Proof.v**: Resistance proof realization
- **P2_T__Resistance.v**: Public resistance theorem

**Key Result:**
```coq
Theorem RESIST : COMPUTATIONAL_SEPARATOR -> False.
```

### C008: Reflexica_Normalization

Derives REFLEXICA (arithmetic integrity) from resistance via double negation elimination. Shows consistency axiom is forced, not arbitrary.

**Core Idea:** The REFLEXICA axiom (pairing inversion law) is not a free assumption but a necessary consequence of the resistance law. Computational hardness implies arithmetic integrity.

**Files:**
- **P1_S__Core_Goal.v**: Core goal specification
- **P2_R__The_Bridge.v**: Bridge from resistance to REFLEXICA
- **P2_T__Reflexica_Derived.v**: REFLEXICA as derived theorem
- **P2_T__Public_Surface.v**: Public surface aggregating C000–C008

**Key Result:**
```coq
Theorem reflexica_normalization :
  ~~Arithmetic_Integrity -> Arithmetic_Integrity.
```

### C009–C012: SAT, Solvability, Quintic, Cubic (Moved)

These modules now live under M004: C009 SAT_Reduction, C010 Solvability_Thesis, C011 Quintic_Hardness, and C012 Cubic_Incompleteness. See M004 for their full descriptions.

## Core Results Summary

### Resistance Law (C007)
```coq
RESIST : COMPUTATIONAL_SEPARATOR → False
```
Any separator bundle leads directly to contradiction.

### Reflexica Normalization (C008)
```coq
~~Arithmetic_Integrity → Arithmetic_Integrity
```
Arithmetic integrity is forced by resistance, not arbitrarily assumed.

## Architectural Pattern

The module follows a **pyramid structure**:

```
M001 (Arithmetic Substrate)
  C000 (BHK core)
  C001 (Carryless Pairing)
  C002 (Additive Hilbert System)
    |
    v
M002 (Proof-Theoretic Machinery)
  C003 (Diagonal Lemma)
  C004 (Mirror Lemma)
    |
    v
M003 (Solvability Theory)
  C005 (Adversarial Barrier)
  C006 (Audit Barrier)
    |
  C007 (Resistance Law) ← unifies C005, C006
    |
  C008 (Reflexica Normalization) ← derives from C007
    |
  M004 (Conservation of Hardness)
    C009–C012 (SAT/Thesis/Quintic/Cubic)
    C013–C014 (Cryptography/Fermat Machine)
```

Each layer provides ingredients for the next, culminating in the thesis refutation. C011 provides the "physics" explaining WHY the barrier exists.

## Key Insights

1. **Solvability ≠ Provability of Solvability**: Problems may be solvable in practice while provability of their solvability is obstructed
2. **Isomorphic Resources**: Computational hardness and arithmetic consistency are identical structural resources
3. **Gödelian Anchoring**: Diagonal mechanism maps obstructive problems to proof-theoretic phenomena
4. **Hardness as Necessity**: Not empirical fact about algorithms but structural requirement preventing triviality

## Philosophical Implications

The Solvability Theory reveals:
- **Computational limits are logical necessities**, not contingent empirical facts
- **Hardness prevents triviality**: removing it collapses the logical universe
- **Self-reference is inescapable**: diagonal construction works in any rich system
- **No universal solver exists**: not "haven't found it yet" but "cannot exist"

The refutation vindicates the intuition that "some problems are inherently hard" by showing the alternative destroys logic itself.

## Dependencies

**Imports:**
- M001 (BHK_R foundation, Carryless Pairing, Additive Hilbert System)
- M002 (Diagonal Lemma, Mirror Lemma)

**Provides:** Complete impossibility framework for computational problem classes

## Design Principles

1. **Barrier Composition**: C005 and C006 compose into unified resistance (C007)
2. **Normalization**: REFLEXICA derived, not assumed (C008)
3. **Concrete Instantiation**: Abstract impossibility grounded in SAT (C009, now in M004)
4. **Terminal Collapse**: Solvability thesis refuted via triviality (C010, now in M004)

## Entry Points

- **For barrier proofs:** C005 P2_T__Barrier (Adversarial), C006 P2_T__Audit_Barrier (Audit)
- **For resistance arguments:** C007 P2_T__Resistance
- **For REFLEXICA derivation:** C008 P2_T__Reflexica_Derived
- **For public API:** C008 P2_T__Public_Surface (aggregates C000–C008)
- **For SAT hardness / Galois correspondence:** see M004 (C009–C012)

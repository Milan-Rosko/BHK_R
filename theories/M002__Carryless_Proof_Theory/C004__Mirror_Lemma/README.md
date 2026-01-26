## C004 — Mirror Lemma

### Overview

C004 establishes the **Mirror Lemma** as a weak forcing principle within the BHK framework. Under the BHK reading, forcing is not an external meta-theoretic construction but an internal computational phenomenon: non-refutability at the meta-level translates to witnessable behavior at the object level.

The core insight is that incompleteness creates bounded "as-if" states: when a formula φ cannot be refuted, there exist bounded witnesses where φ behaves as if it were provable, without actually proving φ. This is weaker than classical forcing (which extends the universe) but sufficient for all downstream barrier constructions.

The mirror lemma bridges:
- (i) **Meta-level non-refutability** (a statement cannot be proven false)
- (ii) **Object-level bounding** (bounded witnesses that behave "as-if" the statement were true)

### Technical Details

Operationally, C004 provides:

- (i) **Mirror parameters**

   - `MirrorParams : Type` (parameters governing the mirror construction)
   - `REG : nat -> Form -> Prop` (regulator condition)
   - `BND : Form -> Form -> Prop` (bounding condition)
   - `ProvT_P : Form -> Prop` (provability-under-transform)

- (ii) **As-if relation**

   - `AsIF : MirrorParams -> Form -> Prop`
   - Captures bounded witness behavior

- (iii) **Fixed-witness theorem**

   - `Mirror_fixed_witness : forall phi, ~ProvT_P (NotF phi) -> AsIF MP phi`
   - Non-refutability implies as-if witness existence

- (iv) **Recursive extension**

   - `DiagDevice : Type` (diagonal device interface)
   - `ProvFormer : Type` (provability former interface)
   - `Recursive_Mirror_Lemma`: extends mirror to self-referential formulas

- (v) **Weak forcing correctness**

   - For self-referential formulas constructed via diagonal, the mirror point and theta are provably equivalent
   - Witnessed by computation: the diagonal device provides the self-referential fixpoint, mirror extracts the as-if witness

Downstream use is via the Phase-3 entry point:

`theories/M002__Proof_Theory/C004__Mirror_Lemma/P3_T__Weakforcing.v`

This exports the mirror lemma and weak forcing interface for barrier constructions.

### Files

- `theories/M002__Proof_Theory/C004__Mirror_Lemma/P1_S__Context.v`

Logical context definition. Establishes the semantic environment for mirror construction, including NotF as `phi -> Bot`.

- `theories/M002__Proof_Theory/C004__Mirror_Lemma/P2_R__Mirror_Core.v`

Core mirror mechanism realization. Implements the mirror parameter construction and as-if relation.

- `theories/M002__Proof_Theory/C004__Mirror_Lemma/P2_R__Mirror_Transport.v`

Transport lemmas for mirror witnesses. Establishes how mirror witnesses transfer across logical transformations.

- `theories/M002__Proof_Theory/C004__Mirror_Lemma/P2_S__Mirror_Lemma.v`

Mirror lemma semantic interface. Packages the fixed-witness theorem behind a minimal interface for static formulas.

- `theories/M002__Proof_Theory/C004__Mirror_Lemma/P3_S__Recursive_Mirror_Lemma.v`

Recursive mirror lemma semantic interface. Extends the mirror construction to self-referential formulas via the diagonal device.

- `theories/M002__Proof_Theory/C004__Mirror_Lemma/P3_T__Weakforcing.v`

Public API for weak forcing. Exports the mirror lemma, recursive extension, and theorem interfaces. This is the recommended entry point for downstream barrier constructions.

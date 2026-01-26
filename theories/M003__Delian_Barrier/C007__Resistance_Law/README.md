## C007 — Resistance Law

### Overview

C007 establishes the **Resistance Law** as a unified impossibility theorem within the BHK framework. Under the BHK reading, resistance is not a meta-theorem about inherent hardness but a constructive refutation: assuming a COMPUTATIONAL_SEPARATOR exists (bundling separator + diagonal device + semantic conditions) leads directly to an inhabitation of False.

The core insight is that **computational separation resists formalization**: any attempt to bundle decision procedures with their correctness proofs creates an immediate contradiction when fed to the diagonal device. This unifies the adversarial barrier (C005) and audit barrier (C006) into a single, self-contained reductio.

The resistance law is the repository's central impossibility result: it demonstrates that separators cannot exist, which downstream forces arithmetic integrity (C008) and establishes hardness conservation (C009).

### Technical Details

Operationally, C007 provides:

- (i) **Computational separator bundle**

   - `COMPUTATIONAL_SEPARATOR : Type`
   - Bundles: separator device + diagonal witness + semantic disjointness + soundness
   - Packages all ingredients needed for contradiction in a single record

- (ii) **Separation specification**

   - Abstract interface for separation problems
   - Defines what it means for a computational problem to be "separable"

- (iii) **Resistance theorem**

   - `RESIST : COMPUTATIONAL_SEPARATOR -> False`
   - Self-contained reductio consuming any purported separator
   - Witnessed by computation: diagonal + flip logic + soundness/disjointness collapse

- (iv) **Unification of barriers**

   - Subsumes C005 adversarial barrier (semantic truth collision)
   - Subsumes C006 audit barrier (Löb forcing)
   - Provides single entry point for impossibility arguments

- (v) **Correctness property**

   - The theorem holds constructively
   - No classical axioms needed for resistance itself
   - Pure BHK inhabitation of False from separator assumption

Downstream use is via the Phase-2 entry point:

`theories/M003__Delian_Barrier/C007__Resistance_Law/P2_T__Resistance.v`

This exports the RESIST theorem for use in normalization (C008) and hardness conservation (C009).

### Files

- `theories/M003__Delian_Barrier/C007__Resistance_Law/P1_S__Separation.v`

Separation specification. Defines the abstract interface for separation problems and COMPUTATIONAL_SEPARATOR bundle structure.

- `theories/M003__Delian_Barrier/C007__Resistance_Law/P2_R__Resistance_Proof.v`

Resistance proof realization. Implements the constructive refutation: shows that COMPUTATIONAL_SEPARATOR implies False by feeding it to the diagonal device and deriving collision via flip logic.

- `theories/M003__Delian_Barrier/C007__Resistance_Law/P2_T__Resistance.v`

Public resistance theorem export. Provides the canonical RESIST theorem as the unified impossibility result. This is the recommended entry point for all downstream impossibility arguments, normalization, and hardness conservation proofs.

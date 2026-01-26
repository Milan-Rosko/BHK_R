## C002 — Additive Hilbert System

### Overview

C002 defines a minimal, fully explicit "additive" provability nucleus over an implicational object language with falsity. Under the BHK reading, provability is not an abstract relation but a concrete inhabitation problem: to prove φ is to construct a witness that a proof-checking computation validates φ.

The design follows a "checker-first" architecture:

- (i) **Object language:** Formulas φ ::= ⊥ | (φ → ψ)
- (ii) **Proof objects:** Provability is witnessed by linear scripts (lists of formulas), checked by a total boolean function `check`
- (iii) **Additive closure:** The only theory-level rule is Modus Ponens, realized by explicit script concatenation

This construction provides the formal provability infrastructure for all downstream proof-theoretic developments, including the diagonal lemma (C003) and barrier theorems (M003).

### Technical Details

Operationally, C002 provides:

- (i) **Object language types**

   - `ATP_Form : Type` (formulas)
   - `ATP_Imp : ATP_Form -> ATP_Form -> ATP_Form` (implication)
   - `ATP_Bot : ATP_Form` (falsity)

- (ii) **Provability predicate**

   - `ATP_Prov : ATP_Form -> Prop`
   - Defined as: ∃ pf, check pf φ = true

- (iii) **Additive closure law**

   - `ATP_Prov_MP : Prov (A --> B) -> Prov A -> Prov B`
   - Realized by explicit script concatenation

- (iv) **Soundness bridge**

   - `Prov_from_check : check pf phi = true -> Prov phi`
   - Links boolean checking to propositional inhabitation

- (v) **Coding nucleus (Phase 4)**

   - `CODEC` interface: abstracts atoms, codes, pairing, and sequences
   - `CanonicalCodec`: canonical realization using `nat` and C001 pairing
   - Fueled decoding operations (`dec_seq_fuel`) to avoid unbounded search

Downstream use is via the Phase-5 entry point:

`theories/M001__BHK_R_Arithmetic/C002__Additive_Hilbert_System/P5_T__Proof_Theory.v`

It provides stable conceptual namespaces:

- `ATP`: Additive theory facade (Form, Prov, Imp, Bot, MP)
- `Coding`: Codec interface and canonical realization

### Files

- `theories/M001__BHK_R_Arithmetic/C002__Additive_Hilbert_System/P1_S__Kernel_Spec.v`

Specification of proof kernel interface. Defines the abstract signature for a Hilbert-style proof system.

- `theories/M001__BHK_R_Arithmetic/C002__Additive_Hilbert_System/P2_R__Hilbert_Kernel.v`

Hilbert system realization (K, S combinators, modus ponens). Implements the boolean checker `check` with explicit axiom schemas (K, S, EFQ) and modus ponens rule.

- `theories/M001__BHK_R_Arithmetic/C002__Additive_Hilbert_System/P2_S__Provability_Interface.v`

Provability predicate interface. Packages the kernel behind a minimal provability interface, defining `Prov` as projection of checkable artifacts.

- `theories/M001__BHK_R_Arithmetic/C002__Additive_Hilbert_System/P3_R__Additive_Laws.v`

Additive provability laws realization. Constructive proof of Modus Ponens closure via list concatenation, establishing the "additive" character of the theory.

- `theories/M001__BHK_R_Arithmetic/C002__Additive_Hilbert_System/P3_S__Additive_Theory.v`

Additive theory interface. Packages the additive closure laws behind a clean semantic interface.

- `theories/M001__BHK_R_Arithmetic/C002__Additive_Hilbert_System/P4_R__Coding_Nucleus.v`

Core coding infrastructure. Defines the abstract `CODEC` interface for arithmetization of syntax.

- `theories/M001__BHK_R_Arithmetic/C002__Additive_Hilbert_System/P4_R__Coding_Carryless.v`

Carryless coding realization. Instantiates the `CODEC` interface using C001 carryless pairing, providing concrete encoding operations for formulas and proof scripts.

- `theories/M001__BHK_R_Arithmetic/C002__Additive_Hilbert_System/P4_S__Coding.v`

Coding interface. Packages the coding realization behind a minimal interface, exposing only essential encoding/decoding operations.

- `theories/M001__BHK_R_Arithmetic/C002__Additive_Hilbert_System/P5_T__Proof_Theory.v`

Stable public surface. Exports the ATP nucleus and Coding interface for downstream use. This is the recommended entry point for all proof-theoretic constructions.

- `theories/M001__BHK_R_Arithmetic/C002__Additive_Hilbert_System/P6_P__Effectivity.v`

Effectivity witnesses. Demonstrates that proof checking and coding operations reduce under vm_compute, validating the computational discipline.

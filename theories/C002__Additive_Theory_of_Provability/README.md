## C002 — Additive Theory of Provability

**1 Overview**

C002 defines a minimal, fully explicit "additive" provability nucleus over an implicational object language with falsity[cite: 1832]. The design goal is to maintain a "checker-first" architecture:

- (i) **Object language:** Formulas $\varphi ::= \bot \mid (\varphi \to \psi)$[cite: 1832].
- (ii) **Proof objects:** Provability is witnessed by linear scripts (lists of formulas), checked by a total boolean function `check`[cite: 1830, 2521].
- (iii) **Additive closure:** The only theory-level rule is Modus Ponens (`Prov (A -> B) -> Prov A -> Prov B`), realized by explicit script concatenation[cite: 1836, 2589].

In Phase 4, C002 introduces a **coding nucleus** with a single canonical codec (nat-based) tied to C001 pairing, without committing to a global decoding correctness theorem at the T-layer[cite: 1838, 2697].

### 2 Downstream API

Downstream use is intended via the single Phase-5 entry point:

`theories/C002__Additive_Theory_of_Provability/P5_T__Proof_Theory.v`

### 3 Stable Namespaces

- `ATP`: Additive theory facade (`Form`, `Prov`, `Imp`, `Bot`)[cite: 2712].
- `Coding`: Codec interface and canonical realization[cite: 2712].

### 4 Additive Provability Nucleus

- (i) **Types:**

   - `ATP_Form : Type`[cite: 2713].
   - `ATP_Prov : ATP_Form -> Prop`[cite: 2715].

- (ii) **Closure:**

   - `ATP_Prov_MP : Prov (A --> B) -> Prov A -> Prov B`[cite: 2718].

- (iii) **Soundness bridge:**

   - `Prov_from_check : check pf phi = true -> Prov phi`[cite: 2723].

### 5 Coding Nucleus

- (i) **Interface:** `CODEC` (abstracts atoms, codes, pairing, and sequences)[cite: 2648].
- (ii) **Canonical realization:**

   - `CanonicalCodec`: Uses `nat` and C001 pairing[cite: 2706].

### 6 Design Discipline

- (i) **Proof-by-script:** `Prov` is defined as $\exists pf, \mathsf{Prf}(pf, \varphi)$. It is not an inductive predicate itself, but a projection of a checkable artifact[cite: 2549].
- (ii) **Kernel soundness:** The boolean kernel `check` is the ground truth. `Prf` is purely a soundness envelope[cite: 2541].
- (iii) **No meta-axioms:** No necessitation, reflection, or completeness axioms are introduced.
- (iv) **Interface-first coding:** Decoding is explicitly fuelled (`dec_seq_fuel`), avoiding the need for constructive unbounded search[cite: 2653].

### 7 Files

- `P2_R__Hilbert_Kernel.v`: Implementation of the Hilbert checker (K, S, EFQ axioms)[cite: 2450].
- `P3_R__Additive_Laws.v`: Constructive proof of Modus Ponens closure via list concatenation[cite: 2552].
- `P4_R__Coding_Carryless.v`: Realization of the `CODEC` interface using C001 pairing[cite: 2607].
- `P5_T__Proof_Theory.v`: Stable public surface[cite: 2709].

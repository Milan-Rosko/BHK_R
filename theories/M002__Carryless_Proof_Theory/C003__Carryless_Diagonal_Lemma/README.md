## C003 — Carryless Diagonal Lemma

### Overview

C003 implements a **total diagonal operator** over the C002 object language, utilizing the effective carryless pairing from C001. Under the BHK reading, the diagonal lemma is not a meta-theorem about unprovability but a constructive operation: given a formula template φ(x) with a free variable, the diagonal operator computes a sentence D such that D provably reduces to φ(code(D)).

The core mechanism is **code-level diagonalization**: the diagonal sentence D "talks about itself" by encoding its own code via the carryless pairing function. This self-reference is achieved purely by normalization, without assuming a global decoding law or reflection principle.

The construction provides the essential self-reference device for all downstream barrier theorems and impossibility results in M003.

### Technical Details

Operationally, C003 provides:

- (i) **Template syntax**

   - `Template : Type` (formula templates with holes and quotations)
   - `Hole : Template` (free variable placeholder)
   - `Quote0 : Template -> Template` (quotation constructor)

- (ii) **Diagonal operator**

   - `diag : Template -> Template`
   - Computes the fixed-point sentence for a given template

- (iii) **Compiler**

   - `compile_delta : Template -> (Template * CExp)`
   - Converts templates into evaluable expressions and their codes
   - Total, primitive recursive operation

- (iv) **Substitution**

   - `subst0 : Template -> Template -> Template`
   - Substitutes a template for the hole
   - Does not recurse under `Quote0` (inert quotation), preventing variable capture cycles

- (v) **Encoding and evaluation**

   - `encU : Template -> nat` (encoding to codes)
   - `eval : CExp -> ... -> nat` (evaluation of compiled expressions)

- (vi) **Correctness property (informal)**

   - `Prov (Imp (diag t) (subst0 t (diag t)))`
   - Witnessed by total computation: encU of the diagonal reduces to the evaluation of the self-applied code
   - The theorem holds even if `unpair` is not a perfect inverse of `pair`; it relies only on `eval` correctly processing the packed inputs it receives

Downstream use is via the Phase-2 entry point:

`theories/M002__Proof_Theory/C003__Carryless_Diagonal_Lemma/P2_T__Diagonal.v`

This exports the diagonal operator and compiler for use in barrier constructions.

### Files

- `theories/M002__Proof_Theory/C003__Carryless_Diagonal_Lemma/P1_S__Syntax.v`

Definition of Templates (syntax) and backend signature. Establishes the abstract interface for template manipulation and code generation.

- `theories/M002__Proof_Theory/C003__Carryless_Diagonal_Lemma/P2_R__Backend.v`

Instantiation of the backend using C001 carryless pairing. Provides concrete encoding and evaluation operations grounded in Zeckendorf arithmetic.

- `theories/M002__Proof_Theory/C003__Carryless_Diagonal_Lemma/P2_R__Compiler.v`

The total structural compiler and encoding logic. Implements the diagonal operator as a primitive recursive function, ensuring termination and computational transparency.

- `theories/M002__Proof_Theory/C003__Carryless_Diagonal_Lemma/P2_T__Diagonal.v`

Public surface exporting the diagonal operator. Provides the canonical diagonal device for downstream barrier constructions. This is the recommended entry point.

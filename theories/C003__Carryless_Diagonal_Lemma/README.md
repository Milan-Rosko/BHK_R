## C003 — Carryless Diagonal Lemma

**1 Overview**

C003 implements a **total diagonal operator** over the C002 object language, utilizing the effective carryless pairing from C001. The construction provides a constructive fixed-point theorem without assuming a global decoding law or reflection principle[cite: 1842].

The core mechanism is a **code-level diagonalization**:
$$\mathsf{encU}(\mathsf{diag}(t)) = \mathsf{eval}(E_t, \dots)$$
This ensures that the diagonal sentence $D$ provably implies its own expansion $\Theta(d)$ purely by normalization[cite: 1852].

### 2 Downstream API

Downstream use is via the phase-safe device interface exported in Phase 5.

- (i) **Template syntax:** `Template` allowing `Hole` and `Quote0` (quotation)[cite: 1845].
- (ii) **Diagonal operator:**

   - `diag : Template -> Template`[cite: 1842].
   - Computes the fixed point sentence.

- (iii) **Compiler:**

   - `compile_delta : Template -> (Template * CExp)`[cite: 1851].
   - Converts templates into evaluable expressions and their codes.

- (iv) **Correctness (informal):**

   - `Prov (Imp (diag t) (subst0 t (diag t)))` (conceptual).
   - Witnessed by total computation: `encU` of the diagonal reduces to the evaluation of the self-applied code[cite: 1852].

### 3 Design Discipline

- (i) **Total compilation:** All operations (`subst0`, `eval`, `encU`) are primitive recursive.
- (ii) **No decoding assumption:** The theorem holds even if `unpair` is not a perfect inverse of `pair`. It relies only on `eval` correctly processing the packed inputs it receives[cite: 1843].
- (iii) **Inert quotation:** Substitution does not recurse under `Quote0`, preventing variable capture cycles[cite: 1846].

### 4 Files

- `P1_S__Syntax.v`: Definition of Templates (syntax) and backend signature.
- `P2_R__Backend.v`: Instantiation of the backend using C001 carryless pairing.
- `P2_R__Compiler.v`: The total structural compiler and encoding logic.
- `P5_T__Diagonal.v`: Public surface exporting the diagonal operator.

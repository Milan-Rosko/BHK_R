## C004 — Mirror Lemma

**1 Overview**

C004 formalizes the **Mirror Schema**, a constructive principle relating non-refutability to "As-If" realizability. It establishes that if a single "Regulator" witness exists uniformly, then non-refutability implies the existence of a bounding witness[cite: 1866].

This phase introduces the **Transformer** interface for representable functions, enabling the application of the C003 diagonal to logical predicates[cite: 1870].

### 2 Downstream API

- (i) **AsIF:** $\mathsf{AsIF}(\varphi) \triangleequiv \exists i, b, (\mathsf{BND}(\varphi, b) \land \dots \land \neg\mathsf{Prov}(\neg\varphi))$[cite: 1864].
- (ii) **Mirror schema (`Mir`):**

   - `Mir(phi) := ~Prov(~phi) -> AsIF(phi)`[cite: 1869].

- (iii) **Fixed-witness pattern:**

   - The core theorem states that `AsIF` is witnessed by a constant pair $(i_0, b_0)$ if that pair serves as a uniform regulator/bound for the entire domain.
   - $\mathsf{REG}(i_0, b_0) \to (\forall \varphi, \neg\mathsf{Prov}(\neg\varphi) \to \mathsf{AsIF}(\varphi))$[cite: 1867].

- (iv) **Transformer diagonal:**

   - `Transformer`: The type of representable functions $G: \mathsf{Form} \to \mathsf{Form}$[cite: 1871].
   - `diag : Transformer -> Form`: The diagonal fixed point for logical maps.

### 3 Design Discipline

- (i) **Fixed-witness construction:** The proof explicitly constructs the witness for `AsIF` by "freezing" the regulator parameters.
- (ii) **Negation as implication:** Negation $\neg_F \varphi$ is encoded as $\varphi \to \bot$[cite: 1862].
- (iii) **Phase safety:** The `REG` and `BND` predicates are kept abstract to allow strictly typed realizations in later phases.

### 4 Files

- `P1_S__Context.v`: Local aliases and context for the mirror statements.
- `P2_R__Mirror_Core.v`: Core mirror parameters and fixed-witness schema.
- `P2_S__Mirror_Lemma.v`: Semantic facade for the core mirror lemma.
- `P2_R__Mirror_Transport.v`: Recursive mirror extension (theta variant).
- `P3_S__Recursive_Mirror_Lemma.v`: Semantic facade for recursive mirror.
- `P5_T__Weakforcing.v`: Public surface exporting mirror and diagonal interfaces.

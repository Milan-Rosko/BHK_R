## C001 — Carryless Pairing

**1 Overview**

C001 implements a **carryless pairing function** $\pi(x,y)$ based on Zeckendorf representations (sums of non-consecutive Fibonacci numbers). This construction allows for the encoding of pairs into natural numbers without relying on prime factorization or complex arithmetic bounds[cite: 1819, 1820].

The design enforces a strict separation between:

- (i) **Effective computation:** The pairing $\pi$ and unpairing $\pi^{-1}$ are total, terminating primitive recursive operations defined on the arithmetic nucleus[cite: 1823].
- (ii) **Certified laws:** The global inversion law $\pi^{-1}(\pi(x,y)) = (x,y)$ is *not* assumed in the pure surface. It is available only through an explicit opt-in certificate layer (**Reflexica**)[cite: 1824, 1825].

### 2 Downstream API

Downstream use is intended via the single Phase-5 entry point:

`theories/C001__Carryless_Pairing/P5_T__Carryless_Pairing.v`

It provides stable conceptual namespaces and re-exports canonical instances.

### 3 Stable Namespaces

- (i) `Prelude`: Re-exports the C000 arithmetic nucleus (`nat`, `add`, `mul`)[cite: 2365].
- (ii) `Fib`: Fibonacci sequence interface (canonical realization)[cite: 2366].
- (iii) `NatInj`: Constructor injectivity and discrimination laws[cite: 2366].
- (iv) `Pairing`: The carryless pairing device facade[cite: 2366].

### 4 Interfaces and Functions

- (i) **Constructor laws:**

   - `S_inj_public : S m = S n -> m = n`[cite: 2371].
   - `O_not_S_public : O <> S n`[cite: 2372].

- (ii) **Carryless pairing device (`CL_PAIR`):**

   - `CarrylessPair : CL_PAIR` (canonical instance)[cite: 2370].
   - `pair : nat -> nat -> nat`[cite: 2288].
   - `unpair : nat -> nat * nat`[cite: 2289].
   - `Z : nat -> list nat` (Zeckendorf support)[cite: 2287].

### 5 Opt-in Certificate (Phase 6)

- `Reflexica`: An axiom/certificate asserting `unpair (pair x y) = (x, y)`[cite: 2425]. This is **never** exported by the T-layer.

### 6 Design Discipline

- (i) **Total Zeckendorf arithmetic:** Support extraction $Z(x)$ is implemented via a bounded greedy scan using explicit fuel ($S(S(x))$), ensuring termination without partial functions[cite: 2233, 2243].
- (ii) **Band separation:** Pairing is achieved by placing $Z(x)$ on even indices and $Z(y)$ on odd indices (shifted by a band offset $B(x)$). This avoids arithmetic carries[cite: 1820, 2256].
- (iii) **Phase-free surface:** Implementation details (like the specific list operations in `P4_R`) are hidden. Only the `CL_PAIR` interface and `Prelude` types are exposed[cite: 1822].

### 7 Files

- `P1_S__Substrate.v`: Stable import of C000 nucleus[cite: 2047].
- `P2_R__Carryless.v`: Canonical Fibonacci realization (`fib` with explicit recursion)[cite: 2056].
- `P3_S__Injectivity.v`: Constructor laws (`S_inj`, discrimination)[cite: 2154].
- `P4_R__Pairing.v`: Realization of Zeckendorf logic ($Z, r, B$) and pairing[cite: 2193].
- `P5_T__Carryless_Pairing.v`: Public facade[cite: 2340].

## C001 — Carryless Pairing

### Overview

C001 implements a **carryless pairing function** based on Zeckendorf representations (sums of non-consecutive Fibonacci numbers). Under the BHK reading, pairing is not an axiomatic primitive but an explicit computation: a total, terminating primitive recursive operation defined on the arithmetic nucleus from C000.

The design enforces a strict separation between:

- (i) **Effective computation:** The pairing π and unpairing π⁻¹ are total, terminating operations that compute by kernel conversion.
- (ii) **Certified laws:** The global inversion law π⁻¹(π(x,y)) = (x,y) is *not* assumed in the pure surface. It is available only through an explicit opt-in certificate layer (Reflexica).

This construction allows for the encoding of pairs into natural numbers without relying on prime factorization or complex arithmetic bounds, establishing a golden-ratio-based coding substrate for all downstream arithmetization.

### Technical Details

Operationally, C001 provides:

- (i) **Fibonacci sequence interface**

   - `F : nat -> nat` (Fibonacci numbers)
   - `r : nat -> nat` (rank: first F k > n)
   - `B : nat -> nat` (band offset: 2 * r)

- (ii) **Zeckendorf support extraction**

   - `Z : nat -> list nat` (Zeckendorf representation as list of Fibonacci indices)

- (iii) **Carryless pairing device**

   - `pair : nat -> nat -> nat`
   - `unpair : nat -> nat * nat`

- (iv) **Constructor injectivity laws**

   - `S_inj : S m = S n -> m = n`
   - `O_not_S : O <> S n`

The implementation uses **band separation**: pairing is achieved by placing Z(x) on even Fibonacci indices and Z(y) on odd indices (shifted by band offset B(x)). This avoids arithmetic carries and grounds encoding in phi-arithmetic (phi = (1+sqrt(5))/2).

Downstream use is via the Phase-5 entry point:

`theories/M001__BHK_R_Arithmetic/C001__Carryless_Pairing/P5_T__Carryless_Pairing.v`

It provides stable conceptual namespaces:

- `Prelude`: Re-exports C000 arithmetic nucleus
- `Fib`: Fibonacci sequence interface
- `NatInj`: Constructor injectivity and discrimination laws
- `Pairing`: The carryless pairing device facade

### Files

- `theories/M001__BHK_R_Arithmetic/C001__Carryless_Pairing/P1_S__Substrate.v`

Stable import of C000 nucleus. Establishes the arithmetic substrate for pairing construction.

- `theories/M001__BHK_R_Arithmetic/C001__Carryless_Pairing/P2_R__Carryless.v`

Canonical Fibonacci realization. Defines `fib` with explicit primitive recursion and establishes growth properties.

- `theories/M001__BHK_R_Arithmetic/C001__Carryless_Pairing/P2_S__Carryless.v`

Fibonacci interface and Zeckendorf uniqueness. Packages the Fibonacci realization behind a minimal interface.

- `theories/M001__BHK_R_Arithmetic/C001__Carryless_Pairing/P3_R__Injectivity.v`

Injectivity proofs for pairing components. Establishes that the encoding is injective on each coordinate.

- `theories/M001__BHK_R_Arithmetic/C001__Carryless_Pairing/P3_S__Injectivity.v`

Injectivity interface. Packages injectivity results behind a clean interface.

- `theories/M001__BHK_R_Arithmetic/C001__Carryless_Pairing/P4_R__Pairing.v`

Realization of Zeckendorf logic (Z, r, B) and pairing. Implements the core pairing/unpairing operations using bounded greedy scan with explicit fuel (S(S(x))), ensuring termination without partial functions.

- `theories/M001__BHK_R_Arithmetic/C001__Carryless_Pairing/P4_S__Pairing.v`

CL_PAIR interface, band separation (even/odd indices). Packages the pairing device behind the canonical `CL_PAIR` record interface.

- `theories/M001__BHK_R_Arithmetic/C001__Carryless_Pairing/P5_T__Carryless_Pairing.v`

Public facade. Exports the canonical pairing instance and stable namespaces for downstream use. This is the recommended entry point.

- `theories/M001__BHK_R_Arithmetic/C001__Carryless_Pairing/P5_T__Effectivity.v`

Computational witnesses (vm_compute tests). Demonstrates that all operations reduce under vm_compute, validating the "computation is proof" discipline.

- `theories/M001__BHK_R_Arithmetic/C001__Carryless_Pairing/P6_A__Reflexica_Certificate.v`

Opt-in certificate layer. Provides the Reflexica axiom asserting `unpair (pair x y) = (x, y)`. This is *never* exported by the T-layer and must be explicitly imported when needed. Downstream, this certificate is derived constructively in M003/C008.

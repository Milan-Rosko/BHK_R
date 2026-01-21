## proofcase v.0.1

`proofcase` is a collection of small, self-contained Rocq (Coq) developments written in a deliberately minimal constructive style. The repository follows a BHK-oriented discipline: proofs live in a small core environment; computation is by kernel conversion (β,ι,ζ and transparent δ) plus explicitly defined recursion; and we avoid classical axioms and heavyweight numeric towers unless a subproject explicitly opts in.

The guiding idea is that BHK is not merely an external interpretation of the code: it is the organizing principle of the code. Types express meaning, and inhabitation is the only proof notion assumed at the base.

### 1 Introduction

At the top level, `proofcase` is organized around an explicit BHK-style nucleus in which propositions are understood by their canonical witnesses. To prove a statement is to construct an inhabitant of its type, and the meaning of connectives is given by their introduction forms (functions, pairs, tagged alternatives, dependent pairs, etc.).

Operationally, the repository is engineered so that computation is the primary proof engine. Normalization and definitional equality are carried by the kernel’s conversion rules (β,ι,ζ and transparent δ), together with explicit recursion on small inductive data. Many foundational equalities are therefore stated in conversion-friendly forms and discharged by reflexivity after simplification (`eq_refl`). The intent is not to optimize tactics, but to maximize semantic transparency: what is true should be visible as computation.

This explains the minimal base environment. By avoiding classical principles and heavy libraries at the top level, we keep proof meaning uniformly constructive and computational behavior explicit and predictable. Subprojects may layer additional structure, but the core discipline is invariant: establish meaning once, realize it by explicit constructions, and stabilize it through small façades.

Viewed this way, Rocq is treated as a typed artifact language: code is not a representation of proof objects; code is the proof object. The repository is therefore written to be read both as logic and as executable semantics.

### 2 Methodology

`proofcase` treats BHK not as an external interpretation but as a design constraint: proofs are inhabitants, and meaning is given by introduction forms plus reduction. As a result, the repository is organized so that computation (kernel conversion + explicit recursion) is the default proof engine, and large arithmetic libraries are avoided unless explicitly required.

A central methodological choice follows from this constraint: we avoid the classical prime-power Gödel coding route. Prime-based arithmetization is elegant in classical settings, but it silently imports a heavy multiplicative number-theoretic substrate (unique factorization, divisibility infrastructure, gcd/normalization lemmas, etc.). In a minimal constructive kernel this is not “free”; it forces a large arithmetic tower just to represent finitary syntax.

Instead, `proofcase` shifts coding to an additive substrate based on Fibonacci growth and Zeckendorf-style supports. Concretely, the repository implements a carryless pairing discipline in which codes are assembled as additive sums of Fibonacci values indexed in disjoint “bands.” Separation is enforced by parity (even vs odd indices) and a rank/band offset function, rather than by multiplicative properties of primes.

This has two proof-theoretic advantages.

1. The entire coding mechanism lives inside the BHK_R nucleus. It is built from explicit recursion over finitary data (unary `nat`, lists, and primitive addition), so both the construction and its computational behavior remain transparent under normalization.

2. The “strength” of arithmetization is localized. The pairing function is computationally effective in the everyday Kleene sense (it terminates and can be executed by `vm_compute`). However, its intended global inverse law is a uniform type inhabitation claim. Rather than hiding this gap, `proofcase` makes it explicit: when required, correctness is introduced as an opt-in certificate layer (e.g. Reflexica) rather than as an implicit global assumption.

In this way, hard downstream meta-theoretic developments are engineered to reduce to a small, named inhabitation problem (“the first realizer certificate”), rather than to an untracked dependency on rich number theory. This keeps the project computational, constructive, and proof-theoretically calibrated by design.

To keep developments readable and prevent semantic drift, projects are organized into explicit phases. Phase 0 fixes the shared meaning/computation nucleus. Later phases may admit multiple realizations of the same construction, but they are related through a single interaction layer that pins a stable surface and proves interoperability results.

(i) Phase 0 (`P0_S__...`) fixes the common BHK core: small inductive data and explicit recursion principles, together with conversion-friendly computation laws.

(ii) For each later phase `Pn` (with `n ≥ 1`), realizations (`Pn_R__...`) provide concrete constructions: Definitions/Fixpoints plus explicit proof terms. A phase may contain several realizations (variants) of the same unit.

(iii) The corresponding semantics file (`Pn_S__...`) is the interaction layer. It packages realizations behind a minimal interface (typically a small record), and establishes the explicit cross-realization results needed downstream: translations, simulations/refinements, or extensional agreement on observable functions.

In this style, the `S` file is not primarily a spine of Parameters. Instead, it stabilizes realized constructions and makes interoperability itself an explicit, checkable object. Semantics is treated as computation under control, not as an aspirational axiom layer.

### 3 Reduction discipline: isolating “first realizers”

A recurring theme in `proofcase` is that the central proof obligation of a construction is often an inhabitation problem rather than a computation problem.

Concretely, a construction may be effective in the everyday Kleene sense (it computes by explicit recursion), while its intended correctness property is a global inhabitation claim that is not derivable inside the minimal base without additional structure. In such cases, the repository separates:

* the realized algorithm (which reduces and can be regression-tested), from
* the uniform correctness inhabitant (which may be unavailable in the pure core).

When needed, `proofcase` introduces opt-in certificate layers (“axiom layers”) that provide exactly one missing inhabitant as a packaged interface, never as an implicit global assumption. This makes dependencies explicit, local, and reversible: the certificate can later be replaced by a constructive proof without changing downstream APIs.

This reduction discipline is methodological: downstream “hard” developments should be engineered so that their strength is measured against a small number of explicit certificates. In particular, later impossibility statements can be calibrated by showing that they imply (or require) the relevant certificate. This isolates the project’s hardness seed: a single named inhabitation problem rather than diffuse untracked assumptions.


## 4 Effectiveness discipline (Kleene-sense, practical)

We aim for effectiveness in the everyday Kleene sense: constructions are explicit, terminating, and compute what they claim to compute. Proofs do not rely on hidden axioms or untracked gaps.

* No `admit` or `Admitted`. Gaps are treated as incomplete work and are not left in committed files.
* Constructions are explicit (`Fixpoint`/`Definition`), so intended computation is visible and checkable by normalization.
* Soundness bridges are one-way by design; completeness claims are made only when explicitly realized.
* When a component is intentionally partial, partiality is made explicit in the type (e.g. `option`).

Files are named so the filename alone indicates phase, role, and semantic unit. We use a phase prefix to keep filenames valid Rocq identifiers (module names cannot begin with a digit) while preserving lexical ordering by phase.

Pattern:

```
P<Phase>_<Role>__Unit[__Qualifier].v
```

* `P<Phase>` is a nonnegative phase index (`P0`, `P1`, `P2`, …).
* `<Role>` indicates the file’s function within the phase.
* `Unit` is a stable identifier for the component/topic.
* `Qualifier` (optional) marks variants (`__A`, `__B`, `__Alt`, `__Draft`).

Roles:

* `S` = Semantics / interaction layer (interfaces, interoperability, translations)
* `R` = Realization (implementations / realizers / computational content)
* `T` = Phase-free public surface (only stable façades)
* `A` = Opt-in certificate layer (explicit meta commitments, quarantined)

Conventions:

* Phase 0 is reserved for the shared BHK meaning/computation nucleus (`P0_S__...`).
* For phases `n ≥ 1`, multiple realizations may exist (`Pn_R__Unit__A`, `Pn_R__Unit__B`, …); the phase semantics file (`Pn_S__Unit`) packages and relates them.
* Optional certificate layers must never be silently re-exported from the pure public surface; they are imported only by explicit opt-in `TA`/`RA` surfaces.

Result.

First, each `Pn_R__Unit__X.v` exports a single packed artifact representing what that realization exposes. Then `Pn_S__Unit.v` can be written uniformly as “interface + instances + bridges,” without depending on internal layouts.

Second, `Pn_S__Unit.v` is conservative in what it declares as shared surface: minimal records and explicit bridge lemmas are preferred over large signatures. This reduces coupling, lowers the cost of adding new realizations, and keeps semantics aligned with computation rather than drifting into aspirational axioms.

This demonstrates a self-similar calculus of meaning:

```
BHK -> (Realization -> Proof Semantics) => Realization of Realization
```

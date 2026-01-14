# proofcase v.0.1

`proofcase` is a collection of small, self-contained Rocq (Coq) developments written in a deliberately minimal, constructive style. The repository follows a BHK-oriented discipline: proofs live in a small core environment, computation is by kernel conversion (β,ι,ζ and transparent δ) plus explicitly defined recursion, and we avoid classical axioms and heavyweight numeric towers unless a subproject explicitly states otherwise.

## 1 Introduction

The top level of `proofcase` is organized around a small, explicit BHK-style core following the Brouwer–Heyting–Kolmogorov interpretation. In this setting, propositions are understood by their canonical witnesses: to prove a statement is to construct an inhabitant of its type, and the meaning of connectives is given by the corresponding introduction forms (functions, pairs, tagged alternatives, dependent pairs, etc.).

Operationally, the repository is designed so that “computation is the proof engine.” Normalization and definitional equality are carried by the kernel’s conversion rules (β,ι,ζ and transparent δ), together with explicitly defined recursion on inductive data. Many foundational equalities are therefore stated and discharged as definitional equalities (`eq_refl`) after simplification, reflecting that the intended content is computational rather than axiomatic.

This is the reason for keeping a minimal base environment: we avoid classical principles and heavyweight libraries at the top level, so that the proof meaning remains uniformly constructive and the computational behavior remains explicit and predictable. Subprojects may layer additional structure, but the core discipline is always: establish semantics first, realize it by explicit constructions, and assemble results through small façades.

## 2 Methodology

In this repository, “semantics” is not treated as non-computational. Under BHK, meaning is expressed by introduction forms and reduction: semantic content is therefore computational by design.

To keep projects readable and avoid semantic drift while preserving that computational character, subprojects are organized into explicit phases. Phase 0 fixes the shared meaning/computation nucleus; later phases admit multiple realizations and a single semantics/interaction layer that relates them.

- Phase 0 (`P0_S__...`) establishes the stable BHK core environment. This file is intentionally small and import-friendly: it fixes the basic data and recursion principles and records conversion-friendly computation laws.
- For each later phase `Pn` (with `n ≥ 1`), realizations (`Pn_R__...`) provide concrete constructions (Definitions/Fixpoints and explicit proof terms). A phase may contain multiple realizations (variants) of the same unit.
- The corresponding semantics file (`Pn_S__...`) is the interaction layer. It packages each realization behind a minimal interface (typically a record or small module type) and states/proves the cross-realization results that let variants communicate: translations, simulations/refinements, and interoperability theorems (e.g., extensional agreement on observable functions).

In this style, the `S` file is not primarily a “spine of Parameters.” Instead, it stabilizes and compares realized constructions, making the communication between realizations explicit and checkable by the kernel.

## 3 File naming convention

Files are named so that the filename alone indicates its phase, role, and semantic unit. We use a phase prefix to keep filenames valid Rocq identifiers (module names cannot begin with a digit) while preserving lexical ordering by phase.

Pattern.

```
P<Phase>_<Role>__Unit[__Qualifier].v
```

In detail.

- `P<Phase>` is a nonnegative phase index (`P0`, `P1`, `P2`, …).
- `<Role>` indicates the file’s function within the phase.
- `Unit` is a stable, reusable identifier for the topic/component (noun-like and project-stable).
- `Qualifier` (optional) is used for variants (e.g., `__A`, `__B`, `__Alt`, `__Draft`).

Roles.

- `S` = Semantics/interaction layer (interfaces, interoperability theorems, translations)
- `R` = Realization (implementations / realizers / computational content)

Conventions.

- Phase 0 is reserved for the shared BHK meaning/computation nucleus (`P0_S__...`).
- For phases `n ≥ 1`, multiple realizations may exist for the same unit (`Pn_R__Unit__A`, `Pn_R__Unit__B`, …); the phase semantics file (`Pn_S__Unit`) packages and relates these realizations.

Result.

First, in each Pn_R__Unit__X.v, we export a single packed artifact (record/module) that represents “what this realization exposes at phase n.” Then Pn_S__Unit.v can be uniformly written as “interface + instances + bridges,” without knowing internal module layouts.

Second, we keep Pn_S__Unit.v conservative in what it declares as shared surface: we prefer minimal records and explicit bridge lemmas over large signatures. That keeps the cost of adding a new realization low, and it keeps semantics aligned with computation rather than drifting into aspirational axioms.

This ensures and demonstrates how BHK itself becomes a self-similar calculus.

```

BHK -> (Relization -> Proof Semantics) => Realization of Realization

```



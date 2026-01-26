# proofcase

`proofcase ( v.0.2)` is a collection of self-contained Rocq (Coq) developments written in a deliberately minimal constructive style. The repository follows a BHK-oriented discipline: proofs live in a small core environment; computation is by kernel conversion 

```

  β,ι,ζ and transparent δ

```

plus explicitly defined recursion; and we avoid classical axioms and heavyweight numeric towers unless a subproject explicitly opts in.

The guiding idea is that the 

*Brouwer–Heyting–Kolmogorov interpretation* of provability (BHK)

is not merely an external interpretation of the code, **it is** the organizing principle of the code. Types express meaning, and inhabitation is the only proof notion assumed at the base.

- **Important Note:** All language in this repository that seemingly invokes non-constructive principles (e.g., “arithmetic truth”) corresponds either to a trivial lambda-definable notion or is purely pedagogical. The logic herein remains strictly constructive (until explicitly said otherwise).

## Main Innovations

This repository implements several novel constructive mechanisms to enforce hardness and barrier results without classical axioms:

* (i) **Carryless Pairing**: A structural arithmetic coding scheme that avoids prime factorization and multiplicative number theory, relying instead on Fibonacci growth and Zeckendorf supports, see https://milanrosko.com/carryless.html.

* (ii) **Reflexica Axiom**: A switchable consistency certificate that acts as an "opt-in" truth anchor (first realization), separating computational realization from global inversion laws.


* (iii) **BHK_R Semantics**: A lambda-definable local logic that serves as the organizing principle for the entire repository.


* (iv) **Mirror Lemma**: A mechanism for weak local forcing derived strictly from reflection principles, allowing "As-If" reasoning within the constructive core.


* (v) **The Adversarial and Audit Barrier**: Impossibility results for certified separators and self-auditing systems, showing that certain decision procedures cannot coexist with their own verification.

## On BHK_R

Our main “engine” `BHK_R` (reflexica) treats BHK not as an external interpretation but as a design constraint: proofs are inhabitants, and meaning is given by introduction forms plus reduction. As a result, the repository is organized so that computation (kernel conversion + explicit recursion) is the default proof engine, and large arithmetic libraries are avoided unless explicitly required.

A central methodological choice follows from this constraint: we avoid the classical prime-power Gödel coding route. Prime-based arithmetization is elegant in classical settings, but it silently imports a heavy multiplicative number-theoretic substrate (unique factorization, divisibility infrastructure, gcd/normalization lemmas, etc.). In a minimal constructive kernel this is not “free”; it forces a large arithmetic tower just to represent finitary syntax.

Instead, `BHK_R` shifts coding to an additive substrate based on Fibonacci growth and Zeckendorf-style supports. Concretely, the repository implements a carryless pairing discipline in which codes are assembled as additive sums of Fibonacci values indexed in disjoint “bands.” Separation is enforced by parity (even vs odd indices) and a rank/band offset function, rather than by multiplicative properties of primes.


## Effectiveness

We aim for effectiveness in the everyday Kleene sense: constructions are explicit, terminating, and compute what they claim to compute. Proofs do not rely on hidden axioms or untracked gaps.

* No `admit` or `Admitted`. Gaps are treated as incomplete work and are not left in committed files.
* Constructions are explicit (`Fixpoint`/`Definition`), so intended computation is visible and checkable by normalization.
* Soundness bridges are one-way by design; completeness claims are made only when explicitly realized.
* When a component is intentionally partial, partiality is made explicit in the type (e.g. `option`).

Files are named so the filename alone indicates phase, role, and semantic unit. We use a phase prefix to keep filenames valid Rocq identifiers (module names cannot begin with a digit) while preserving lexical ordering by phase.

Pattern:

```

  P<Phase>_<Role>__Unit.v

```

* `P<Phase>` is a nonnegative phase index (`P0`, `P1`, `P2`, …).
* `<Role>` indicates the file’s function within the phase.
* `Unit` is a stable identifier for the component/topic.

Roles:

* `S` = Semantics / interaction layer (interfaces, interoperability, translations)
* `R` = Realization (implementations / realizers / computational content)
* `T` = Phase-free public surface (only stable façades)
* `A` = Opt-in certificate layer (explicit meta commitments, quarantined) 

Conventions:

* Phase 0 is reserved for the shared BHK meaning/computation nucleus (`P0_S__...`).
* For phases `n ≥ 1`, multiple realizations may exist (`Pn_R__Unit__A`, `Pn_R__Unit__B`, etc.); the phase semantics file (`Pn_S__Unit`) packages and relates them.
* Optional certificate layers must never be silently re-exported from the pure public surface; they are imported only by explicit opt-in `TA`/`RA` surfaces.

Result.

This demonstrates a “self-similar” calculus of meaning:

```

  BHK -> (Realization -> Proof Semantics) => Realization of Realization

```

## References

We strongly advise to consult,

```

  @book{russell27,
    title        = {{Principia Mathematica}},
    author       = {Whitehead, A. N. and Russell, B.},
    year         = 1927,
    publisher    = {Cambridge University Press},
    address      = {Cambridge},
    isbn         = {0521626064},
    edition      = {2d ed.}
  }

    @book{kleene52,
    title        = {{Introduction to Metamathematics}},
    author       = {Kleene, S. C.},
    year         = 1952,
    publisher    = {North-Holland},
    isbn         = 9780444896230
  }


  @book{troelstra88,
    title        = {{Constructivism in Mathematics, Vol. 2}},
    author       = {Troelstra, A. S. and van Dalen, D.},
    year         = 1988,
    publisher    = {North-Holland (an imprint of Elsevier Science)},
    address      = {Amsterdam, New York},
    series       = {Studies in Logic and the Foundations of Mathematics},
    volume       = 123,
    isbn         = {0444703586}
  }

  @book{boolos07,
    title        = {{Computability and Logic}},
    author       = {Boolos, G. and Burgess, J. P. and Jeffrey, R. C.},
    year         = 2007,
    publisher    = {Cambridge University Press},
    isbn         = 9780521877520,
    edition      = {5th}
  }

```

For more intuition,

```

  @misc{rosko2025fibonacci,
    title        = {{A Fibonacci-Based Gödel Numbering: $\Delta_0$ Semantics Without Exponentiation}},
    author       = {Rosko, M.},
    year         = 2025,
    note         = {arXiv preprint},
    url          = {http://doi.org/10.48550/arXiv.2509.10382}

  }
  @misc{rosko2025fractal,
    title        = {{The Fractal Logic of $\Phi$-adic Recursion}},
    author       = {Rosko, M.},
    year         = 2025,
    note         = {arXiv preprint},
    url          = {http://doi.org/10.48550/arXiv.2510.08934}
  }
  @misc{rosko2025cubichilbert,
    title        = {{Cubic Incompleteness: Hilbert's Tenth Problem at Degree Three}},
    author       = {Rosko, M.},
    year         = 2025,
    note         = {arXiv preprint},
    url          = {http://doi.org/10.48550/arXiv.2510.00759},

  }
  @misc{rosko2025adversarial,
    title        = {{Adversarial Barrier in Uniform Class Separation}},
    author       = {Rosko, M.},
    year         = 2025,
    note         = {arXiv preprint},
    url          = {http://doi.org/10.48550/arXiv.2512.08149},

  }
  @misc{rosko2025fragment,
    title        = {{A Constructive Fragment of Physical Propositions}},
    author       = {Rosko, M.},
    year         = 2025,
    note         = {arXiv preprint},
    url          = {http://doi.org/10.48550/arXiv.2511.21296},

  }
  @misc{rosko2025solverparadox,
    title        = {{The Solver's Paradox in Formal Problem Spaces}},
    author       = {Rosko, M.},
    year         = 2025,
    url          = {http://doi.org/10.48550/arXiv.2511.14665},

  }
  @misc{rosko2025primeconjectures,
    title        = {{On the Realizability of Prime Conjectures in Heyting Arithmetic}},
    author       = {Rosko, M.},
    year         = 2025,
    url          = {http://doi.org/10.48550/arXiv.2511.07774}
  }

```

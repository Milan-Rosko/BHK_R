## C009 — SAT Reduction

### Overview

C009 establishes **SAT Reduction** as the concrete terminal problem within the BHK framework. Under the BHK reading, the reduction is not a meta-theorem about NP-hardness but a constructive equivalence: the existence of a certified SAT solver (one providing proof certificates for both SAT and UNSAT) is logically equivalent to the negation of arithmetic integrity.

The core result is **hardness conservation**: SAT hardness and arithmetic consistency are isomorphic structural resources. A certified SAT solver would enable construction of a COMPUTATIONAL_SEPARATOR, which the resistance law (C007) immediately refutes. This demonstrates that computational hardness of SAT is not an empirical contingency but a necessary consequence of arithmetic integrity.

The construction uses **arithmetized CNF**: SAT instances are encoded as natural numbers using carryless pairing (Zeckendorf representation), binding SAT's combinatorial hardness to phi-arithmetic's golden ratio structure at the encoding level.

### Technical Details

Operationally, C009 provides:

- (i) **Arithmetized CNF syntax**

   - `Lit : Type` := nat (literal: (var, polarity) via carryless pair)
   - `Clause : Type` := list Lit (clause: disjunction of literals)
   - `CNF : Type` := list Clause (formula: conjunction of clauses)
   - `encode_lit : nat -> bool -> Lit`
   - `decode_lit : Lit -> (nat * bool)`
   - `decode_clause : nat -> Clause`
   - `decode_cnf : nat -> CNF`

- (ii) **First-order logic extension**

   - `Form : Type` (formulas: Bot, Imp, Eq, All, Ex)
   - `Prov : Form -> Prop` (provability via proof checking)
   - Extends C002 ATP to richer logic with quantifiers and equality

- (iii) **SAT barrier instantiation**

   - `SAT_Form : nat -> Form` (satisfiable instances)
   - `UNSAT_Form : nat -> Form` (unsatisfiable instances)
   - Instantiates C005 adversarial barrier for SAT/UNSAT classes

- (iv) **Certified solver definition**

   - `Certified_SAT_Solver : Type` := SEPARATOR (from C005)
   - Bundles decision function with proof certificates for both SAT and UNSAT

- (v) **Hardness conservation theorem**

   - `Hardness_Conservation : (exists S : Certified_SAT_Solver) <-> ~Arithmetic_Integrity`
   - Forward: certified solver implies separator, which RESIST refutes, contradicting REFLEXICA
   - Backward: arithmetic inconsistency enables ex falso construction of arbitrary solver

- (vi) **Golden ratio connection**

   - Zeckendorf encoding binds SAT to phi = (1+sqrt(5))/2
   - Worst-case entropy of phi inherited by SAT instances
   - Combinatorial hardness grounded in number-theoretic structure

Downstream use is via the Phase-3 and Phase-4 entry points:

`theories/M004__Conservation_of_Hardness/C009__SAT_Reduction/P3_T__Structural_Integrity.v`
`theories/M004__Conservation_of_Hardness/C009__SAT_Reduction/P3_T__FOL.v`
`theories/M004__Conservation_of_Hardness/C009__SAT_Reduction/P4_T__Mechanism.v`

These export the hardness conservation theorem, FOL interface, and reduction mechanism.

### Files

- `theories/M004__Conservation_of_Hardness/C009__SAT_Reduction/P1_S__CNF_Syntax.v`

Arithmetized SAT syntax. Defines literal/clause/CNF encoding via carryless pairing, establishing the Zeckendorf representation of SAT instances.

- `theories/M004__Conservation_of_Hardness/C009__SAT_Reduction/P1_S__Syntax.v`

First-order logic syntax. Defines FOL formulas (Bot, Imp, Eq, All, Ex) extending the C002 ATP nucleus to richer logic.

- `theories/M004__Conservation_of_Hardness/C009__SAT_Reduction/P2_R__Reduction.v`

Reduction mechanism realization. Implements SAT_Form and UNSAT_Form definitions, establishing the mapping from SAT instances to formulas.

- `theories/M004__Conservation_of_Hardness/C009__SAT_Reduction/P2_R__Substitution.v`

Substitution mechanism for FOL. Implements variable substitution operations needed for quantifier handling.

- `theories/M004__Conservation_of_Hardness/C009__SAT_Reduction/P3_R__Kernel.v`

Kernel realization for FOL. Implements the extended proof checker handling quantifiers and equality beyond the ATP kernel.

- `theories/M004__Conservation_of_Hardness/C009__SAT_Reduction/P3_T__FOL.v`

Public FOL API. Exports the first-order logic interface with provability via proof checking, providing richer logic for downstream use.

- `theories/M004__Conservation_of_Hardness/C009__SAT_Reduction/P3_T__Structural_Integrity.v`

Hardness Conservation theorem. Proves the central result: certified SAT solver existence is equivalent to negation of arithmetic integrity. This is the key theorem instantiating the resistance law for SAT. This is the recommended entry point for hardness conservation arguments.

- `theories/M004__Conservation_of_Hardness/C009__SAT_Reduction/P4_T__Kernel_Sanity.v`

Effectivity witnesses and kernel sanity checks. Demonstrates that FOL kernel operations reduce under vm_compute, validating the computational discipline.

- `theories/M004__Conservation_of_Hardness/C009__SAT_Reduction/P4_T__Mechanism.v`

Public reduction mechanism. Exports the SAT reduction surface, providing the canonical interface for SAT barrier instantiation and diagonal mechanism application.

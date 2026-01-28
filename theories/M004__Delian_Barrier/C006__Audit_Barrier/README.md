## C006 — Audit Barrier

### Overview

C006 establishes the **Audit Barrier** as an impossibility theorem for self-verifying decision procedures within the BHK framework. Under the BHK reading, the barrier is a constructive refutation: assuming a decider can "audit itself" (verify its own correctness via reflection conditions) leads directly to an inhabitation of False via Löb's rule.

The core mechanism is **audit internalization**: demanding that a decider satisfy reflection conditions `Prov (Box φ -> φ)` for both a formula and its negation at a diagonal fixed point. When combined with Löb's rule, this forces the system to prove both the formula and its negation, contradicting consistency.

The barrier demonstrates that self-auditing decision procedures cannot exist: no decider can simultaneously:
- (i) **Provide total decisions** with proof certificates
- (ii) **Satisfy reflection conditions** for provability operator Box
- (iii) **Respect Löb's rule** (provability of provability-implies-truth entails provability)

### Technical Details

Operationally, C006 provides:

- (i) **Hilbert-Bernays interface**

   - `Box : Form -> Form` (provability operator)
   - `HB1 : forall A B, Prov (Imp A B) -> Prov (Imp (Box A) (Box B))` (distribution)
   - `HB2 : forall A, Prov A -> Prov (Box A)` (internalization)
   - `Loeb : forall A, Prov (Imp (Box A) A) -> Prov A` (Löb's rule)

- (ii) **Decider specification**

   - `DECIDER_T : (nat -> Form) -> (nat -> bool) -> Prop`
   - Bundles decision function with proof certificates
   - `sigma n = true -> Prov (A n)` and `sigma n = false -> Prov (NotF (A n))`

- (iii) **Audit internalization condition**

   - `AuditInt : (Form -> Form) -> (nat -> Form) -> nat -> Prop`
   - Demands `Prov (Imp (Box (A d)) (A d))` and `Prov (Imp (Box (NotF (A d))) (NotF (A d)))`
   - Creates tension when combined with Löb's rule at diagonal fixed point

- (iv) **Main barrier theorem**

   - `Audit_Barrier : DECIDER_T -> ~AuditInt`
   - Given decider satisfying HB conditions, cannot satisfy audit reflection conditions at diagonal index without proving Bot

- (v) **Diagonal adapter**

   - Connects to C003 diagonal device
   - Shows flip template realizes required fixed point
   - Provides concrete instantiation of the barrier

Downstream use is via the Phase-2 entry points:

`theories/M003__Delian_Barrier/C006__Audit_Barrier/P2_T__Audit_Barrier.v`
`theories/M003__Delian_Barrier/C006__Audit_Barrier/P2_T__Audit_Adapter.v`

These export the barrier theorem and its connection to the diagonal device.

### Files

- `theories/M003__Delian_Barrier/C006__Audit_Barrier/P1_S__Context.v`

Hilbert-Bernays interface and audit context. Defines Box operator, HB1/HB2/Loeb axioms, DECIDER_T, and AuditInt predicates.

- `theories/M003__Delian_Barrier/C006__Audit_Barrier/P2_R__Audit_Logic.v`

Audit logic realization. Implements the core proof mechanism: shows how AuditInt + Löb's rule forces contradiction at the diagonal index.

- `theories/M003__Delian_Barrier/C006__Audit_Barrier/P2_T__Audit_Barrier.v`

Main impossibility theorem using Löb's rule. Exports the canonical Audit_Barrier theorem showing self-verification impossibility. This is the recommended entry point for resistance constructions.

- `theories/M003__Delian_Barrier/C006__Audit_Barrier/P2_T__Audit_Adapter.v`

Diagonal device adapter. Connects C003 diagonal device to audit barrier, showing the flip template realizes the required fixed point and providing concrete instantiation of the impossibility.

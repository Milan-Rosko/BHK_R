(* P2_T__Audit_Adapter.v *)

(*************************************************************************)
(*                                                                       *)
(*  C_006 / Phase 3 (T): Audit Adapter                                   *)
(*                                                                       *)
(*  Connects C003 diagonal device with the C006 audit barrier.           *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From Audit_Barrier.C006 Require Import P1_S__Context.
From Audit_Barrier.C006 Require Import P2_T__Audit_Barrier.
From Diagonallemma.C003 Require Import P2_T__Diagonal.

Set Implicit Arguments.
Unset Strict Implicit.

Module C006_Audit_Adapter_T.

  Module Ctx := C006_Context_S.
  Module Diag := Diagonallemma.C003.P2_T__Diagonal.

  Section Adapter.

    Variable A : Ctx.nat -> Ctx.Form.
    Variable sigma : Ctx.nat -> Ctx.Prelude.bool.

    Variable Box : Ctx.Form -> Ctx.Form.

    Hypothesis HB1 : forall X Y : Ctx.Form, Ctx.Prov (Ctx.Imp X Y) -> Ctx.Prov (Ctx.Imp (Box X) (Box Y)).
    Hypothesis HB2 : forall X : Ctx.Form, Ctx.Prov X -> Ctx.Prov (Box X).
    Hypothesis Loeb : forall X : Ctx.Form, Ctx.Prov (Ctx.Imp (Box X) X) -> Ctx.Prov X.
    Hypothesis MP : forall X Y : Ctx.Form, Ctx.Prov (Ctx.Imp X Y) -> Ctx.Prov X -> Ctx.Prov Y.
    Hypothesis Consistent : ~ Ctx.Prov Ctx.Bot.

    (*
      Diagonal device instantiation (abstract adapter).
    *)
    
    Variable Flip_Template : Diag.Template.
    Variable Compiled : Diag.COMPILED Flip_Template.

    Variable Form_of_Template : Diag.Template -> Ctx.Form.

    Definition D_t : Diag.Template := Diag.diag (t := Flip_Template) Compiled.
    Definition d : Ctx.nat := Diag.encU D_t.
    Definition D : Ctx.Form := Form_of_Template D_t.

    (*
      Bridge: the diagonal instance realizes the flip at code d.
    *)
    
    Hypothesis Diag_As_Flip :
      D = (if sigma d then Ctx.NotF (A d) else A d).

    Theorem Audit_Barrier_Concrete :
      Ctx.DECIDER_T A sigma -> ~ Ctx.AuditInt Box A d.
    Proof.
      exact (@C006_Audit_Barrier_T.Audit_Barrier
               A sigma Box Loeb MP Consistent D d Diag_As_Flip).
    Qed.

  End Adapter.

End C006_Audit_Adapter_T.

Export C006_Audit_Adapter_T.

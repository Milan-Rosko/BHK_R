(* P4_S__Barrier_Interface.v *)

From C014 Require Import P1_S__Fermat_Interface P3_S__Machine_Definition.

Module Barrier_Interface.

  (** Refutes existence of any Fermat machine. *)
  Class BarrierEngine_Machine : Prop := {
    barrier_machine : ~ (exists M, Machine_Definition.Fermat_Machine M)
  }.

  (** Refutes a Fermat witness at exponent 4 (optional, for specific barriers). *)
  Class BarrierEngine_F4 : Prop := {
    barrier_F4 : forall t : Fermat_Interface.Triple, 
      P1_T__Arithmetic_Surface.C014_Arithmetic_T.Fermat_Relation 
        P1_R__Peano_Arithmetic.four t -> False
  }.

End Barrier_Interface.
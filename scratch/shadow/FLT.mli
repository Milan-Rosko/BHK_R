
type __ = Obj.t

module BHK :
 sig
  type nat =
  | O
  | S of nat

  val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat
 end

module N :
 sig
  type nat = BHK.nat =
  | O
  | S of nat

  val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat
 end

module Fermat_Interface :
 sig
  type coq_Triple = (N.nat * N.nat) * N.nat
 end

module Coq_N :
 sig
  type nat = BHK.nat =
  | O
  | S of nat

  val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat
 end

val pow : Coq_N.nat -> Coq_N.nat -> Coq_N.nat

val leb : Coq_N.nat -> Coq_N.nat -> bool

val two : Coq_N.nat

val three : Coq_N.nat

module C014_Arithmetic_T :
 sig
  type coq_Triple = Fermat_Interface.coq_Triple

  type coq_Fermat_Relation = __
 end

module Sumbool_Extraction :
 sig
  val coq_N_eq_dec : Coq_N.nat -> Coq_N.nat -> bool

  val coq_Fermat_Check_Witness :
    Coq_N.nat -> Fermat_Interface.coq_Triple -> bool
 end

module Machine_Definition :
 sig
  type coq_Fermat_Machine = __
 end

module Fermat_Solver_R :
 sig
  val witness_solvable_from_machine : __
 end

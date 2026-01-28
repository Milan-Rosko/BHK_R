
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module BHK =
 struct
  type nat =
  | O
  | S of nat

  (** val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 **)

  let rec nat_rect f f0 = function
  | O -> f
  | S n0 -> f0 n0 (nat_rect f f0 n0)

  (** val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 **)

  let rec nat_rec f f0 = function
  | O -> f
  | S n0 -> f0 n0 (nat_rec f f0 n0)

  (** val add : nat -> nat -> nat **)

  let rec add m n =
    match m with
    | O -> n
    | S m' -> S (add m' n)

  (** val mul : nat -> nat -> nat **)

  let rec mul m n =
    match m with
    | O -> O
    | S m' -> add n (mul m' n)
 end

module N = BHK

module Fermat_Interface =
 struct
  type coq_Triple = (N.nat * N.nat) * N.nat
 end

module Coq_N = BHK

(** val pow : Coq_N.nat -> Coq_N.nat -> Coq_N.nat **)

let rec pow n = function
| Coq_N.O -> Coq_N.S Coq_N.O
| Coq_N.S m' -> Coq_N.mul n (pow n m')

(** val leb : Coq_N.nat -> Coq_N.nat -> bool **)

let rec leb n m =
  match n with
  | Coq_N.O -> true
  | Coq_N.S n' -> (match m with
                   | Coq_N.O -> false
                   | Coq_N.S m' -> leb n' m')

(** val two : Coq_N.nat **)

let two =
  Coq_N.S (Coq_N.S Coq_N.O)

(** val three : Coq_N.nat **)

let three =
  Coq_N.S two

module C014_Arithmetic_T =
 struct
  type coq_Triple = Fermat_Interface.coq_Triple

  type coq_Fermat_Relation = __
 end

module Sumbool_Extraction =
 struct
  (** val coq_N_eq_dec : Coq_N.nat -> Coq_N.nat -> bool **)

  let coq_N_eq_dec n =
    Coq_N.nat_rec (fun m ->
      match m with
      | Coq_N.O -> true
      | Coq_N.S _ -> false) (fun _ iHn m ->
      match m with
      | Coq_N.O -> false
      | Coq_N.S n0 -> iHn n0) n

  (** val coq_Fermat_Check_Witness :
      Coq_N.nat -> Fermat_Interface.coq_Triple -> bool **)

  let coq_Fermat_Check_Witness n = function
  | (p, n0) ->
    let (n1, n2) = p in
    let b0 = leb three n in
    if b0
    then let s = coq_N_eq_dec n1 Coq_N.O in
         if s
         then false
         else let s0 = coq_N_eq_dec n2 Coq_N.O in
              if s0
              then false
              else let s1 = coq_N_eq_dec n0 Coq_N.O in
                   if s1
                   then false
                   else coq_N_eq_dec (Coq_N.add (pow n1 n) (pow n2 n))
                          (pow n0 n)
    else false
 end

module Machine_Definition =
 struct
  type coq_Fermat_Machine = __
 end

module Fermat_Solver_R =
 struct
  (** val witness_solvable_from_machine : __ **)

  let witness_solvable_from_machine =
    __
 end

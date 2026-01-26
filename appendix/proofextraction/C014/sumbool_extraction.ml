
type __ = Obj.t

type bool =
| True
| False

type ('a, 'b) prod =
| Pair of 'a * 'b

type sumbool =
| Left
| Right

module BHK =
 struct
  type nat =
  | O
  | S of nat
 end

module C_002_Prelim =
 struct
  type bool =
  | Coq_true
  | Coq_false

  type 'a option =
  | Some of 'a
  | None

  type 'a list =
  | Coq_nil
  | Coq_cons of 'a * 'a list

  type coq_ProofKernel =
    __ -> __ -> bool
    (* singleton inductive, whose constructor was Build_ProofKernel *)

  type coq_AdditiveProvability = { coq_Imp : (__ -> __ -> __); coq_Bot : __ }
 end

module Prelude =
 struct
  type bool = C_002_Prelim.bool =
  | Coq_true
  | Coq_false

  (** val bool_rect : 'a1 -> 'a1 -> bool -> 'a1 **)

  let bool_rect f f0 = function
  | Coq_true -> f
  | Coq_false -> f0

  (** val bool_rec : 'a1 -> 'a1 -> bool -> 'a1 **)

  let bool_rec f f0 = function
  | Coq_true -> f
  | Coq_false -> f0

  type 'a option = 'a C_002_Prelim.option =
  | Some of 'a
  | None

  (** val option_rect : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

  let option_rect f f0 = function
  | Some a -> f a
  | None -> f0

  (** val option_rec : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

  let option_rec f f0 = function
  | Some a -> f a
  | None -> f0

  type 'a list = 'a C_002_Prelim.list =
  | Coq_nil
  | Coq_cons of 'a * 'a list

  (** val list_rect :
      'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

  let rec list_rect f f0 = function
  | Coq_nil -> f
  | Coq_cons (y, l0) -> f0 y l0 (list_rect f f0 l0)

  (** val list_rec :
      'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

  let rec list_rec f f0 = function
  | Coq_nil -> f
  | Coq_cons (y, l0) -> f0 y l0 (list_rec f f0 l0)

  type coq_ProofKernel =
    __ -> __ -> bool
    (* singleton inductive, whose constructor was Build_ProofKernel *)

  type coq_Form = __

  type coq_Proof = __

  (** val check : coq_ProofKernel -> coq_Proof -> coq_Form -> bool **)

  let check p0 =
    p0

  type coq_AdditiveProvability = C_002_Prelim.coq_AdditiveProvability = { 
  coq_Imp : (__ -> __ -> __); coq_Bot : __ }

  type coq_Form_ATP = __

  (** val coq_Imp :
      coq_AdditiveProvability -> coq_Form_ATP -> coq_Form_ATP -> coq_Form_ATP **)

  let coq_Imp a =
    a.coq_Imp

  (** val coq_Bot : coq_AdditiveProvability -> coq_Form_ATP **)

  let coq_Bot a =
    a.coq_Bot

  type nat = BHK.nat =
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

module C011_Diophantine_S =
 struct
  module N = Prelude

  (** val leb : N.nat -> N.nat -> C_002_Prelim.bool **)

  let rec leb m n =
    match m with
    | N.O -> C_002_Prelim.Coq_true
    | N.S m' ->
      (match n with
       | N.O -> C_002_Prelim.Coq_false
       | N.S n' -> leb m' n')
 end

module Rad = C011_Diophantine_S

module N = Rad.N

(** val pow : N.nat -> N.nat -> N.nat **)

let rec pow n = function
| N.O -> N.S N.O
| N.S m' -> N.mul n (pow n m')

(** val leb0 : N.nat -> N.nat -> bool **)

let rec leb0 n m =
  match n with
  | N.O -> True
  | N.S n' -> (match m with
               | N.O -> False
               | N.S m' -> leb0 n' m')

(** val two : N.nat **)

let two =
  N.S (N.S N.O)

type triple = ((N.nat, N.nat) prod, N.nat) prod

(** val n_eq_dec : N.nat -> N.nat -> sumbool **)

let n_eq_dec n =
  N.nat_rec (fun m -> match m with
                      | N.O -> Left
                      | N.S _ -> Right) (fun _ iHn m ->
    match m with
    | N.O -> Right
    | N.S n0 -> iHn n0) n

(** val fermat_Check_Witness : N.nat -> triple -> sumbool **)

let fermat_Check_Witness n = function
| Pair (p, n0) ->
  let Pair (n1, n2) = p in
  let b0 = leb0 (N.S two) n in
  (match b0 with
   | True ->
     let s = n_eq_dec n1 N.O in
     (match s with
      | Left -> Right
      | Right ->
        let s0 = n_eq_dec n2 N.O in
        (match s0 with
         | Left -> Right
         | Right ->
           let s1 = n_eq_dec n0 N.O in
           (match s1 with
            | Left -> Right
            | Right -> n_eq_dec (N.add (pow n1 n) (pow n2 n)) (pow n0 n))))
   | False -> Right)

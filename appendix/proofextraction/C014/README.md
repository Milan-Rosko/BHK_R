
type __ = Obj.t

type bool =
| True
| False

type ('a, 'b) prod =
| Pair of 'a * 'b

type sumbool =
| Left
| Right

module BHK :
 sig
  type nat =
  | O
  | S of nat
 end

module C_002_Prelim :
 sig
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

module Prelude :
 sig
  type bool = C_002_Prelim.bool =
  | Coq_true
  | Coq_false

  val bool_rect : 'a1 -> 'a1 -> bool -> 'a1

  val bool_rec : 'a1 -> 'a1 -> bool -> 'a1

  type 'a option = 'a C_002_Prelim.option =
  | Some of 'a
  | None

  val option_rect : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

  val option_rec : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

  type 'a list = 'a C_002_Prelim.list =
  | Coq_nil
  | Coq_cons of 'a * 'a list

  val list_rect : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

  val list_rec : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

  type coq_ProofKernel =
    __ -> __ -> bool
    (* singleton inductive, whose constructor was Build_ProofKernel *)

  type coq_Form = __

  type coq_Proof = __

  val check : coq_ProofKernel -> coq_Proof -> coq_Form -> bool

  type coq_AdditiveProvability = C_002_Prelim.coq_AdditiveProvability = { 
  coq_Imp : (__ -> __ -> __); coq_Bot : __ }

  type coq_Form_ATP = __

  val coq_Imp :
    coq_AdditiveProvability -> coq_Form_ATP -> coq_Form_ATP -> coq_Form_ATP

  val coq_Bot : coq_AdditiveProvability -> coq_Form_ATP

  type nat = BHK.nat =
  | O
  | S of nat

  val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat
 end

module C011_Diophantine_S :
 sig
  module N :
   sig
    type bool = C_002_Prelim.bool =
    | Coq_true
    | Coq_false

    val bool_rect : 'a1 -> 'a1 -> bool -> 'a1

    val bool_rec : 'a1 -> 'a1 -> bool -> 'a1

    type 'a option = 'a C_002_Prelim.option =
    | Some of 'a
    | None

    val option_rect : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

    val option_rec : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

    type 'a list = 'a C_002_Prelim.list =
    | Coq_nil
    | Coq_cons of 'a * 'a list

    val list_rect : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

    val list_rec : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

    type coq_ProofKernel =
      __ -> __ -> bool
      (* singleton inductive, whose constructor was Build_ProofKernel *)

    type coq_Form = __

    type coq_Proof = __

    val check : coq_ProofKernel -> coq_Proof -> coq_Form -> bool

    type coq_AdditiveProvability = C_002_Prelim.coq_AdditiveProvability = { 
    coq_Imp : (__ -> __ -> __); coq_Bot : __ }

    type coq_Form_ATP = __

    val coq_Imp :
      coq_AdditiveProvability -> coq_Form_ATP -> coq_Form_ATP -> coq_Form_ATP

    val coq_Bot : coq_AdditiveProvability -> coq_Form_ATP

    type nat = BHK.nat =
    | O
    | S of nat

    val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

    val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

    val add : nat -> nat -> nat

    val mul : nat -> nat -> nat
   end

  val leb : N.nat -> N.nat -> C_002_Prelim.bool
 end

module Rad :
 sig
  module N :
   sig
    type bool = C_002_Prelim.bool =
    | Coq_true
    | Coq_false

    val bool_rect : 'a1 -> 'a1 -> bool -> 'a1

    val bool_rec : 'a1 -> 'a1 -> bool -> 'a1

    type 'a option = 'a C_002_Prelim.option =
    | Some of 'a
    | None

    val option_rect : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

    val option_rec : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

    type 'a list = 'a C_002_Prelim.list =
    | Coq_nil
    | Coq_cons of 'a * 'a list

    val list_rect : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

    val list_rec : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

    type coq_ProofKernel =
      __ -> __ -> bool
      (* singleton inductive, whose constructor was Build_ProofKernel *)

    type coq_Form = __

    type coq_Proof = __

    val check : coq_ProofKernel -> coq_Proof -> coq_Form -> bool

    type coq_AdditiveProvability = C_002_Prelim.coq_AdditiveProvability = { 
    coq_Imp : (__ -> __ -> __); coq_Bot : __ }

    type coq_Form_ATP = __

    val coq_Imp :
      coq_AdditiveProvability -> coq_Form_ATP -> coq_Form_ATP -> coq_Form_ATP

    val coq_Bot : coq_AdditiveProvability -> coq_Form_ATP

    type nat = BHK.nat =
    | O
    | S of nat

    val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

    val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

    val add : nat -> nat -> nat

    val mul : nat -> nat -> nat
   end

  val leb : N.nat -> N.nat -> C_002_Prelim.bool
 end

module N :
 sig
  type bool = C_002_Prelim.bool =
  | Coq_true
  | Coq_false

  val bool_rect : 'a1 -> 'a1 -> bool -> 'a1

  val bool_rec : 'a1 -> 'a1 -> bool -> 'a1

  type 'a option = 'a C_002_Prelim.option =
  | Some of 'a
  | None

  val option_rect : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

  val option_rec : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

  type 'a list = 'a C_002_Prelim.list =
  | Coq_nil
  | Coq_cons of 'a * 'a list

  val list_rect : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

  val list_rec : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

  type coq_ProofKernel =
    __ -> __ -> bool
    (* singleton inductive, whose constructor was Build_ProofKernel *)

  type coq_Form = __

  type coq_Proof = __

  val check : coq_ProofKernel -> coq_Proof -> coq_Form -> bool

  type coq_AdditiveProvability = C_002_Prelim.coq_AdditiveProvability = { 
  coq_Imp : (__ -> __ -> __); coq_Bot : __ }

  type coq_Form_ATP = __

  val coq_Imp :
    coq_AdditiveProvability -> coq_Form_ATP -> coq_Form_ATP -> coq_Form_ATP

  val coq_Bot : coq_AdditiveProvability -> coq_Form_ATP

  type nat = BHK.nat =
  | O
  | S of nat

  val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat
 end

val pow : N.nat -> N.nat -> N.nat

val leb0 : N.nat -> N.nat -> bool

val two : N.nat

type triple = ((N.nat, N.nat) prod, N.nat) prod

val n_eq_dec : N.nat -> N.nat -> sumbool

val fermat_Check_Witness : N.nat -> triple -> sumbool

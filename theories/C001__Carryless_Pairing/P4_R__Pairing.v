(* P4_R__Pairing.v *)

From Carryless_Pairing.C001 Require Import
  P1_S__Substrate
  P2_R__Carryless.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*  Adds the local infrastructure required by the pairing construction.  *)
(*  No changes to Phase-0. No classical axioms.                          *)
(*************************************************************************)

(*************************************************************************)
(* Syntax note: bool/list/prod are local to keep the core nucleus small. *)
(*************************************************************************)

Module Pairing_Realization.

(*************************************************************************)
(*                                                                       *)
(*   We consider,                                                        *)
(*                                                                       *)
(*   pi_CL_tau(x,y)=Sum{e in Z(x)} F_{2e}+Sum{j in Z(y)} F_{B(x)+2j-1}.  *)
(*                                                                       *)
(*************************************************************************)


  Module N := P1_S__Substrate.Prelude.
  Module A := P2_R__Carryless.Fib_Realization.

  (*************************************************************************)
  (* Local booleans and lists                                              *)
  (*************************************************************************)

  Inductive bool : Type :=
  | true : bool
  | false : bool.

  Definition negb (b : bool) : bool :=
    match b with true => false | false => true end.

  Inductive list (A0 : Type) : Type :=
  | nil : list A0
  | cons : A0 -> list A0 -> list A0.

  Arguments nil {A0}.
  Arguments cons {A0} _ _.

  Fixpoint app {A0} (xs ys : list A0) : list A0 :=
    match xs with
    | nil => ys
    | cons x xs' => cons x (app xs' ys)
    end.

  Fixpoint map {A0 B0} (f : A0 -> B0) (xs : list A0) : list B0 :=
    match xs with
    | nil => nil
    | cons x xs' => cons (f x) (map f xs')
    end.

  Fixpoint fold {A0 B0} (f : A0 -> B0 -> B0) (xs : list A0) (z : B0) : B0 :=
    match xs with
    | nil => z
    | cons x xs' => f x (fold f xs' z)
    end.

  Fixpoint filter {A0} (p : A0 -> bool) (xs : list A0) : list A0 :=
    match xs with
    | nil => nil
    | cons x xs' =>
        match p x with
        | true => cons x (filter p xs')
        | false => filter p xs'
        end
    end.

  (*************************************************************************)
  (* Products (internal)                                                   *)
  (*************************************************************************)

  Inductive prod (A0 B0 : Type) : Type :=
  | pair : A0 -> B0 -> prod A0 B0.
  Arguments pair {A0 B0} _ _.

  Definition fst {A0 B0} (p : prod A0 B0) : A0 :=
    match p with pair a _ => a end.

  Definition snd {A0 B0} (p : prod A0 B0) : B0 :=
    match p with pair _ b => b end.

  (*************************************************************************)
  (* Basic nat comparisons (decidable, bounded)                            *)
  (*************************************************************************)

  Fixpoint leb (m n : N.nat) : bool :=
    match m, n with
    | N.O, _ => true
    | N.S _, N.O => false
    | N.S m', N.S n' => leb m' n'
    end.

  Definition ltb (m n : N.nat) : bool :=
    match leb (N.S m) n with
    | true => true
    | false => false
    end.

  (*************************************************************************)
  (* Truncated subtraction (monus)                                         *)
  (*************************************************************************)

  Fixpoint monus (m n : N.nat) : N.nat :=
    match m, n with
    | m', N.O => m'
    | N.O, N.S _ => N.O
    | N.S m', N.S n' => monus m' n'
    end.

  (*************************************************************************)
  (* Fibonacci access                                                      *)
  (* We reuse the canonical fib: fib 0 = 0, fib 1 = 1, fib 2 = 1, ...       *)
  (*************************************************************************)

  Definition F (k : N.nat) : N.nat := A.Fib.fib k.

  (*************************************************************************)
  (* Rank r(x): first index k such that F k > x                            *)
  (* Bounded by S (S x) (coarse but primitive-recursive).                  *)
  (*************************************************************************)

  Fixpoint find_r_aux (x : N.nat) (k fuel : N.nat) : N.nat :=
    match fuel with
    | N.O => k
    | N.S fuel' =>
        match ltb x (F k) with
        | true => k
        | false => find_r_aux x (N.S k) fuel'
        end
    end.

  Definition r (x : N.nat) : N.nat :=
    (* start k=O, fuel = S(S x) *)
    find_r_aux x N.O (N.S (N.S x)).

  Definition B (x : N.nat) : N.nat := N.add (r x) (r x).  (* 2*r(x) *)

  (*************************************************************************)
  (* Zeckendorf support Z(x) by bounded greedy scan downwards              *)
  (*************************************************************************)

  (*************************************************************************)
  (* Syntax note: Z uses a bounded greedy scan down from r(x),             *)
  (* not a uniqueness proof of Zeckendorf representations.                 *)
  (*************************************************************************)

  Definition dec (n : N.nat) : N.nat :=
    match n with
    | N.O => N.O
    | N.S n' => n'
    end.

  Fixpoint zeck_greedy_down (k : N.nat) (rem : N.nat) (prev_taken : bool)
    : prod (list N.nat) N.nat :=
    match k with
    | N.O => pair nil rem
    | N.S k' =>
        match prev_taken with
        | true =>
            zeck_greedy_down k' rem false
        | false =>
            match leb (F k) rem with
            | true =>
                let pr := zeck_greedy_down k' (monus rem (F k)) true in
                pair (cons k (fst pr)) (snd pr)
            | false =>
                zeck_greedy_down k' rem false
            end
        end
    end.

  Definition Z (x : N.nat) : list N.nat :=
    (* scan from r(x) down to 1; including k=0 is harmless since F0=0 *)
    fst (zeck_greedy_down (r x) x false).

  (*************************************************************************)
  (* Sum of Fibonacci values over a support list                           *)
  (*************************************************************************)

  Definition sumF (xs : list N.nat) : N.nat :=
    fold (fun k acc => N.add (F k) acc) xs N.O.

  (*************************************************************************)
  (* Parity and small index transforms                                     *)
  (*************************************************************************)

  Fixpoint is_even (n : N.nat) : bool :=
    match n with
    | N.O => true
    | N.S N.O => false
    | N.S (N.S n') => is_even n'
    end.

  Definition is_odd (n : N.nat) : bool := negb (is_even n).

  Fixpoint div2 (n : N.nat) : N.nat :=
    match n with
    | N.O => N.O
    | N.S N.O => N.O
    | N.S (N.S n') => N.S (div2 n')
    end.

  Definition two (n : N.nat) : N.nat := N.add n n.
  Definition two_j_minus1 (j : N.nat) : N.nat := monus (two j) (N.S N.O).  (* 2j-1 *)

  (*************************************************************************)
  (* Typed carryless pairing                                               *)
  (*************************************************************************)

  (*************************************************************************)
  (* Pairing encodes x on even indices, y on odd indices above B(x).       *)
  (*************************************************************************)

  Definition even_band (x : N.nat) : list N.nat :=
    map (fun e => two e) (Z x).

  Definition odd_band (x y : N.nat) : list N.nat :=
    map (fun j => N.add (B x) (two_j_minus1 j)) (Z y).

  Definition pi_CL_tau (x y : N.nat) : N.nat :=
    sumF (app (even_band x) (odd_band x y)).

  (*************************************************************************)
  (* Typed unpairing                                                       *)
  (*************************************************************************)

  (*************************************************************************)
  (* Unpairing filters by parity and the band threshold (B(x)+1).          *)
  (*************************************************************************)

  Definition half_even_indices (zn : list N.nat) : list N.nat :=
    map div2 (filter is_even zn).

  Definition geq (m n : N.nat) : bool := leb n m.

  Definition odd_ge_B1 (Bx k : N.nat) : bool :=
    match is_odd k with
    | false => false
    | true => geq k (N.S Bx)
    end.

  Definition decode_odd_index (Bx k : N.nat) : N.nat :=
    div2 (N.S (monus k Bx)).

  Definition y_indices (Bx : N.nat) (zn : list N.nat) : list N.nat :=
    map (fun k => decode_odd_index Bx k)
        (filter (odd_ge_B1 Bx) zn).

  Definition unpair_CL_tau (n : N.nat) : prod N.nat N.nat :=
    let zn := Z n in
    let X := half_even_indices zn in
    let x := sumF X in
    let Bx := B x in
    let Y := y_indices Bx zn in
    let y := sumF Y in
    pair x y.

End Pairing_Realization.

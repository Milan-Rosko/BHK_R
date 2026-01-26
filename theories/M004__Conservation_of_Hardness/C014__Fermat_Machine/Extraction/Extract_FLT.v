(* Extract_FLT.v *)
(* This driver manually extracts the OCaml artifacts for the Fermat Machine *)

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt.

(* Force output to current directory (which will be handled by the script) *)
Set Extraction Output Directory ".".

(* Import the new modular definitions *)
From Fermat_Machine.C014 Require Import P1_T__Arithmetic_Surface.
From Fermat_Machine.C014 Require Import P3_P__Sumbool_Extraction.
From Fermat_Machine.C014 Require Import P3_S__Machine_Definition.
From Fermat_Machine.C014 Require Import P3_R__Fermat_Solver.

(* Extract the key computational components *)
Extraction "FLT.ml"
  (* The Decider *)
  Sumbool_Extraction.N_eq_dec
  Sumbool_Extraction.Fermat_Check_Witness

  (* The Solver Logic *)
  Fermat_Solver_R.witness_solvable_from_machine

  (* The Definitions *)
  Machine_Definition.Fermat_Machine
  C014_Arithmetic_T.Fermat_Relation
  C014_Arithmetic_T.Triple.


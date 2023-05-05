Require Import DG4iSL_cut_elim.

Require Import Extraction.
Extraction Language Haskell.

Unset Extraction Optimize.

(* Time Separate *) Extraction G4iSL_cut_elimination.
(* Extraction "/(*ers/IanShillito/CoqForm/lol.hs" GL4ip_cut_elimination. *)
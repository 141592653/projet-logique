(******************************************************************************)
(*                                                                            *)
(*                      INVERSION DE MD* VIA SAT SOLVEUR                      *)
(*                                                                            *)
(*                      Projet Logique 2016 - Partie SAT                      *)
(*   Auteur, license, etc.                                                    *)
(******************************************************************************)


(** The main function of this project. [genCNF digest] returns a CNF formula
    describing possible pre-images of [digest]. *)
val genCNF : Data.digest -> Formula.cnf

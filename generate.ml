(******************************************************************************)
(*                                                                            *)
(*                      INVERSION DE MD* VIA SAT SOLVEUR                      *)
(*                                                                            *)
(*                      Projet Logique 2016 - Partie SAT                      *)
(*   Auteur, license, etc.                                                    *)
(******************************************************************************)
		
open Param
open Printf
open Formula
open Data

(*** Main function ***)

    
let genCNF digest =  				(* TODO *)
  let etape i = 
   
    Equiv(Const(digest.(i)) , Xor(Xor(Const(digest.(i+10)),Lit(Pos((13*i) mod 512 + 1))), Xor(Lit(Pos((14*i + 1) mod 512 + 1)),Lit(Pos((15*i + 2) mod 512 + 1)))))
  in
  let complete_f = ref (etape 0) in 
  for i = 0 to 10 do 
    complete_f := And(etape i,!complete_f)
  done;
  complete_f := And(!complete_f,Or(Lit(Pos(512)),Lit(Neg(512))));
  (*Printf.printf "%s\n" (displayFormula !complete_f);
  Printf.printf "%s\n" (displayCnf (formulaeToCnf !complete_f));*)
  formulaeToCnf !complete_f

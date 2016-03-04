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

let pos n = Lit(Pos n)
let neg n = Lit(Neg n)

(*Variables de 1 à 512 : input*)
let input i j = 1 + i*32 + j

(*Première variable du round*)
let begin_round = 513

(*nombre de variables dans un step*)
let step_nb = 9 * 32

(*numéro dans le step*)
let a_nb= 0
let b_nb= 1
let c_nb= 2
let d_nb= 3
let non_lin_nb= 4
let carry41_nb= 5
let carry42_nb= 6
let sum4_nb= 7
let carry_lr_nb= 8

let test = true

(* permet de donner le numéro de la variable*)
let var_index step_index s i = 
  if test then 
    input step_index i
  else
    begin_round + s*step_nb + (step_index * 32) + i

(*as , bs ,cs, ds avec s le numéro du step*)
let a s i = var_index a_nb s i
let b s i = var_index b_nb s i
let c s i = var_index c_nb s i
let d s i = var_index d_nb s i

(*résultat de la fonction non linéaire*)
let non_lin s i = var_index non_lin_nb s i

(*addition de a,f , k et snput*)
let carry41 s i = var_index carry41_nb s i
let carry42 s i = var_index carry42_nb s i
let sum4 s i = var_index sum4_nb s i


(*addition de b et du left_rotate*)
let carry_lr s i = var_index carry_lr_nb s i
(*let sum_lr s i = begin_round + s*step_nb + (8*32) + i inutile, dirrectement dans bi+1*)

(* Formule pour f*)
let f s = 
  let formula_f = ref (Const true) in 
  for i = 0 to 31 do 
    formula_f := And(!formula_f,
		     Imply(
			 Or(
			     And(pos (b s i), pos (c s i)),
			     And(neg (b s i), pos (d s i))
		       ), pos(non_lin s i)
		    ))
  done;
  !formula_f

(*** Main function 
* Digest : tableau de 128 bits ***)
let genCNF digest = 
  if digest.(127) then
    print_string "coucou";
  formulaeToCnf (Lit(Pos(512)))









(*WEAK HASH : let etape i = 
  
  Equiv(Const(digest.(i)) , Xor(Xor(Const(digest.(i+10)),Lit(Pos((13*i) mod 512 + 1))), Xor(Lit(Pos((14*i + 1) mod 512 + 1)),Lit(Pos((15*i + 2) mod 512 + 1)))))
  in
  let complete_f = ref (etape 0) in 
  for i = 0 to 10 do 
  complete_f := And(etape i,!complete_f)
  done;
  complete_f := And(!complete_f,Or(Lit(Pos(512)),Lit(Neg(512))));
  (*Printf.printf "%s\n" (displayFormula !complete_f);
  Printf.printf "%s\n" (displayCnf (formulaeToCnf !complete_f));*)
  formulaeToCnf !complete_f*)

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

(*Variables de 1 à 512 : input*)
let input i j = 1 + i*32 + j

(*Première variable du round*)
let begin_round = 513

(*nombre de variables dans un step*)
let step_nb = 9 * 32

(*ai , bi ,ci, di avec i le numéro du step*)
let a i j = begin_round + i*step_nb + j
let b i j = begin_round + i*step_nb + 32 + j
let c i j = begin_round + i*step_nb + (2*32) + j
let d i j = begin_round + i*step_nb + (3*32) + j
let a_pos i j = Lit(Pos(a i j))
let a_neg i j = Lit(Neg(a i j))
let b_pos i j = Lit(Pos(b i j))
let b_neg i j = Lit(Neg(b i j))
let c_pos i j = Lit(Pos(c i j))
let c_neg i j = Lit(Neg(c i j))
let d_pos i j = Lit(Pos(d i j))
let d_neg i j = Lit(Neg(d i j))

(*résultat de la fonction non linéaire*)
let non_lin i j = begin_round + i*step_nb + (4*32) + j
let non_lin_pos i j = Lit(Pos(non_lin i j))
let non_lin_neg i j = Lit(Neg(non_lin i j))

(*addition de a,f , k et input*)
let carry41 i j = begin_round + i*step_nb + (5*32) + j
let carry42 i j = begin_round + i*step_nb + (6*32) + j
let sum4 i j = begin_round + i*step_nb + (7*32) + j

let carry41_pos i j = Lit(Pos(carry41 i j))
let carry41_neg i j = Lit(Neg(carry41 i j))
let carry42_pos i j = Lit(Pos(carry42 i j))
let carry42_neg i j = Lit(Neg(carry42 i j))
let sum4_pos i j = Lit(Pos(sum4 i j))
let sum4_neg i j = Lit(Neg(sum4 i j))

(*addition de b et du left_rotate*)
let carry_lr i j = begin_round + i*step_nb + (8*32) + j
let carry_lr_pos i j = Lit(Pos(carry_lr i j))
let carry_lr_neg i j = Lit(Neg(carry_lr i j))
(*let sum_lr i j = begin_round + i*step_nb + (8*32) + j inutile, dirrectement dans bi+1*)

(* Formule pour f*)
let f s = 
  let formula_f = ref (Const true) in 
  true
 (* for i = 0 to 31 do 
    formula_f := And(!formula_f, Or(And(Lit(Pos(b s i), Lit(Pos(c s i))),And()))*)


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

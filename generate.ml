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
open Md

(* Permet de transformer une liste de formules en la conjonction des formules correspondantes *)
let rec  list_to_formula l = match l with 
  |[] -> Const(true)
  |f::q -> And(f,list_to_formula q)

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
  if test && step_index <> 4 then 
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

(* Formule pour f, testée : ok*)
let f s = 
  let formula_f = ref (Const true) in 
  for i = 0 to 31 do 
    formula_f := And(!formula_f,
		     Equiv(
			 Or(
			     And(pos (b s i), pos (c s i)),
			     And(neg (b s i), pos (d s i))
		       ), pos(non_lin s i)
		    ))
  done;
  !formula_f


(*Instructions pour tester les fonctions non linéaires :
  mettre la variable test à true
  mettre dans genCNF test_f digest
  vérifier que les premiers 32 bits du digest de l'input trouvée sont égaux aux premiers 32 bits du digest en entrée
*)

(*Permet de relier les variables que l'on souhaite aux variables de digest*)
let bound_digest_test_f digest = 
  let formula_bound = ref (Const true) in 
  for i = 0 to 31 do 
    formula_bound := And (!formula_bound, Equiv (pos (non_lin 0 i), Const(digest.(i))) )
  done;
  !formula_bound

let test_f digest =
  formulaeToCnf (And(bound_digest_test_f digest,f 0)) 


(************ Affectations ****************)
(* non testé *)
let affectations s =
  let formula_aff = ref (Const true) in 
  for i = 0 to 31 do 
    formula_aff := And(!formula_aff,
		       And(Equiv(pos (d (s+1) i) , pos (c s i)),
			   And(Equiv(pos (c (s+1) i) , pos (b s i)),
			       Equiv(pos (a (s+1) i) , pos (d s i))
			   )
		       ))
      

  done;
  !formula_aff   

let bound_digest_test_aff digest = 
  let formula_bound = ref (Const true) in 
  for i = 0 to 31 do 
    formula_bound := And (!formula_bound,
			  And(And(Equiv ( pos (a 0 i), Const(a0.(i))) ,
				  Equiv ( pos (b 0 i), Const(b0.(i)))),
			      And(Equiv ( pos (c 0 i), Const(c0.(i))),
				  Equiv ( pos (d 0 i), Const(d0.(i))))
			      ))
  done;
  !formula_bound

let test_aff digest = 
  formulaeToCnf (And(bound_digest_test_aff digest,affectations 0)) 

let add_rotate s = 
  formulaeToCnf (Const(true))

let add4 s = 
  let round = s / 16 in 
  (*initialisation des retenues *)
  let formula_add4 = ref (And(Equiv ( pos (carry41 s 0), Const false),
			      Equiv ( pos (carry42 s 0), Const false))) 
  in
  for i = 0 to 31 do 
    let formulae = [
      Equiv(list_to_formula [neg (a i s); neg (non_lin i s); Equiv(Const(vectK.(s).(i)), Const(false)) ; Equiv (Const(input (choice round s) i),false)] , list_to_formula [neg (carry41 s (i+1)); neg (carry42 s (i+1)); neg (sum4 s (i+1))])
    ] in 
    formula_add4 := And(list_to_formula formulae, !formula_add4)
  done;
  !formula_add4
  (*initialisa
  for i = 0 to 31 do
  *)

(*** Main function 
     * Digest : tableau de 128 bits ***)
let genCNF digest = 
  formulaeToCnf (And(bound_digest_test_f digest,f 0)) 





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

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

(*ce serait mieux de faire un open mais ça marche pas...*)
(*choix du mot*)
let choice1 i =  i
let choice2 i =  (5*i + 1) mod 16
let choice3 i =  (3*i + 5) mod 16
let choice4 i =  (7*i) mod 16

(*renvoie la fonction de choix du mot de 32 bits dans input associée au round r*)
let choice r = 
  match r with 
  |0 -> choice1
  |1 -> choice2
  |2 -> choice3
  |3 -> choice4
  |_ -> failwith "Round supérieur à 4"


(* Permet de transformer une liste de formules en la conjonction des formules correspondantes *)
let rec  list_to_formula l = match l with 
  |[] -> Const(true)
  |f::q -> And(f,list_to_formula q)

(*transforme un entier en litéral*)
let pos n = Lit(Pos n)
let neg n = Lit(Neg n)
(*transforme un entier et un booléen en littéral*)
let lit n b = 
  if b then 
    pos n
  else
    neg n

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

let test = ref true

(* permet de donner le numéro de la variable*)
let var_index step_index s i = 
  if !test && step_index <> 4 then 
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


(** ******************************* Affectations *********************************)
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

(** ****************************** Addition - rotation ***************************)
(*non testé*)
(* ici, dep_rot est le numéro de la première variable du mot 32 bits qui subit la rotation et dep_b est le deuxième mot 32 bits qui lui est additionné*)
let add_rotate dep_rot  = 
  formulaeToCnf (Const(true))

(** ***************************** Addition des 4 mots ****************************)



(*compte le nombre de valeur true d'un tableau de booléens*)
let count_true bool_arr = 
  let fold_func n b = if b then n + 1 else n in 
  Array.fold_left fold_func 0 bool_arr

(*ici, n appartient à [0,7], il représente les 8 combinaisons de booléens possiblespour les 3 variables additionnées*)
let formula_add4_bool s i n = 

  let n_ref = ref n in 
  let bool_arr = Array.make 4 false in
  for i = 0 to 2 do (*conversion de n en binaire*)
    bool_arr.(i) <- if !n_ref mod 2 = 0 then false else true ;
    n_ref := !n_ref / 2
  done; 
  bool_arr.(3) <- vectK.(s).(i);
(* le nombre de booléens à la valeur true caractérise exactement le résultat de la somme et les deux retenues*)
  let nb_true = count_true bool_arr in 
  let carry41_bool = nb_true >= 2 and carry42_bool = nb_true = 4 in 
  let sum4_result = if nb_true mod 2 = 0 then false else true in 
  Equiv(
      list_to_formula [
	  lit (a s i) bool_arr.(0);
	  lit (non_lin s i) bool_arr.(1); 
	  lit (input (choice (s/16) s) i) bool_arr.(2)] ,
      list_to_formula [
	  lit (carry41 s i) carry41_bool;
	  lit (carry42 s i) carry42_bool;
	  lit (sum4    s i) sum4_result
    ])
  
	     
  

(*non testé*)
let add4 s = 
  (*initialisation des retenues *)
  let formula_add4 = ref (And(Equiv ( pos (carry41 s 0), Const false),
			      Equiv ( pos (carry42 s 0), Const false))) 
  in
  for i = 0 to 31 do 
    for j = 0 to 7 do 
      formula_add4 := And(formula_add4_bool s i j, !formula_add4)
    done
  done;
  !formula_add4

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

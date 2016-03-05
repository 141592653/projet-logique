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

(* Fonctionnement : j'ai divisé le calcul de la formule en 5 parties : 
-initialisation des variables
-affectation (qui correspondent aux d:=!c dans md.ml))
-inversion de la fonction non linéaire
-addition de 4 mots de 32 bits
-addition combiné à la rotation (ce qui permet de diminuer le nombre de clauses)

Pour chacune de ces phases, j'ai écrit une fonction caml associée qui, pour prendre en paramètre un mot de 32 bits, reçoit le numéro de la première variable correpondant à ces 32 bits.*)

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

(*Variables de 1 à 512 : input, s est le numéro du steo*)
let input s = 1 + s*32

(*Première variable du round*)
let begin_round = 513

(*nombre de variables dans un step*)
let step_nb = 9 * 32

(*indice dans le step des différentes variables. Les variables d'un step sont rangées par groupe de 32 variables. Ici, le premier groupe correspond aux 32 bits de a, le second ceux de b, etc. *)
let a_nb= 0
let b_nb= 1
let c_nb= 2
let d_nb= 3
let non_lin_nb= 4
let carry41_nb= 5
let carry42_nb= 6
let sum4_nb= 7
let carry_lr_nb= 8

let test = ref false

(*var index permet de renvoyer le numéro de la première variable d'un groupe de 32 bits. *)
let var_index step_index s = 
  if !test && step_index <> 4 then 
    input (step_index + 1)
  else
    begin_round + s*step_nb + (step_index * 32) 

(*as , bs ,cs, ds avec s le numéro du step*)
let a s = var_index a_nb s
let b s = var_index b_nb s
let c s = var_index c_nb s
let d s = var_index d_nb s

(*résultat de la fonction non linéaire*)
let non_lin s = var_index non_lin_nb s

(*addition de a,f , k et snput*)
let carry41 s = var_index carry41_nb s
let carry42 s = var_index carry42_nb s
let sum4 s = var_index sum4_nb s


(*addition de b et du left_rotate*)
let carry_lr s = var_index carry_lr_nb s
(*let sum_lr s i = begin_round + s*step_nb + (8*32) + i inutile, dirrectement dans bi+1*)

(* Formule pour f, testée : ok. b_start, c_start et d_start sont les première variaables des groupes de 32 variables b,c et d.*)
let f b_start c_start d_start non_lin_start = 
  let formula_f = ref (Const true) in 
  for i = 0 to 31 do 
    formula_f := And(!formula_f,
		     Equiv(
			 Or(
			     And(pos (b_start + i), pos (c_start + i)),
			     And(neg (b_start + i), pos (d_start + i))
		       ), pos(non_lin_start + i)
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
    formula_bound := And (!formula_bound, Equiv (pos (non_lin 0 + i), Const(digest.(i))) )
  done;
  !formula_bound

let test_f digest =
  test := true;
  formulaeToCnf (And(bound_digest_test_f digest,f (b 0) (c 0) (d 0) (non_lin 0))) 


(** ******************************* Affectations *********************************)
(* non testé *)
let affectation receiver sender =
  let formula_aff = ref (Const true) in 
  for i = 0 to 31 do 
    formula_aff := And(!formula_aff,
		       Equiv(pos (receiver + i) , pos (sender + i))
		      )
      

  done;
  !formula_aff   

let bound_digest_test_aff digest = 
  let formula_bound = ref (Const true) in 
  for i = 0 to 31 do 
    formula_bound := And (!formula_bound,
			  And(And(Equiv ( pos (a 0 + i), Const(a0.(i))) ,
				  Equiv ( pos (b 0 + i), Const(b0.(i)))),
			      And(Equiv ( pos (c 0 + i), Const(c0.(i))),
				  Equiv ( pos (d 0 + i), Const(d0.(i))))
			      ))
  done;
  !formula_bound

let test_aff digest = 
  test := true;
  formulaeToCnf (And(bound_digest_test_aff digest,affectation (a 0) (b 0))) 

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

(*addendi est le ième terme de l'addition. add_arr4 est un tableau de boléen dont on connait la valeur (en pratique, c'est vectK.s) 
carry ;: retenues
result : résultat de l'addition
n appartient à [0,7], il représente les 8 combinaisons de booléens possibles pour les 3 variables additionnées*)
let formula_add4_bool addend1 addend2 addend3 add_arr4 carry1 carry2 result i n = 

  let n_ref = ref n in 
  let bool_arr = Array.make 4 false in
  for i = 0 to 2 do (*conversion de n en binaire*)
    bool_arr.(i) <- if !n_ref mod 2 = 0 then false else true ;
    n_ref := !n_ref / 2
  done; 
  bool_arr.(3) <- add_arr4.(i);
(* le nombre de booléens à la valeur true caractérise exactement le résultat de la somme et les deux retenues*)
  let nb_true = count_true bool_arr in 
  let carry41_bool = nb_true >= 2 and carry42_bool = nb_true = 4 in 
  let sum4_result = if nb_true mod 2 = 0 then false else true in 
  Equiv(
      list_to_formula [
	  lit (addend1 + i) bool_arr.(0);
	  lit (addend2 + i) bool_arr.(1); 
	  lit (addend3 + i) bool_arr.(2)] ,
      list_to_formula [
	  lit (carry1 + i) carry41_bool;
	  lit (carry2 + i) carry42_bool;
	  lit (result + i) sum4_result
    ])
  
	     
  
(*formula_add4_bool (a s) (non_lin s) (input (choice round s)) vectK.(s) (carry41 s) (carry42 s) (sum4 s) i j*)

(*non testé*)
let add4 addend1 addend2 addend3 add_arr4 carry1 carry2 result s = 
  (*initialisation des retenues *)
  let round = s / 16 in 
  let formula_add4 = ref (And(Equiv ( pos (carry41 s), Const false),
			      Equiv ( pos (carry42 s), Const false))) 
  in
  for i = 0 to 31 do 
    for j = 0 to 7 do 
      formula_add4 := And(formula_add4_bool addend1 addend2 addend3 add_arr4 carry1 carry2 result i j, !formula_add4)
    done
  done;
  !formula_add4

let bound_digest_test_add digest = 
  let formula_bound = ref (Const true) in 
  for i = 0 to 31 do 
    formula_bound := And (!formula_bound,
			  Equiv ( pos (161 + i), Const(digest.(i))) )
  done;
  !formula_bound

let test_add digest = 
  test := true;
  formulaeToCnf (And(bound_digest_test_dd digest, add4 1 33 65 vectK.(s) 97 129 161)) 
  

(*** Main function 
     * Digest : tableau de 128 bits ***)
let genCNF digest = 
  test_f digest





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

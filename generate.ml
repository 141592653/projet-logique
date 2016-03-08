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
  |[x] -> x
  |f::q -> And(f,list_to_formula q)

(* Conversion en binaire, little endian, size est le nombre de bit que l'on souhaite avoir. Attention, si le nombre est trop grand, il sera tronqué.*)
let int_to_bin n size = 
  let n_ref = ref n in 
  let bool_arr = Array.make size false in 
  for i = 0 to size -1 do 
    bool_arr.(i) <- if !n_ref mod 2 = 0 then false else true;
    n_ref := !n_ref / 2
  done;
  bool_arr

(*compte le nombre de valeur true d'un tableau de booléens*)
let count_true bool_arr = 
  let fold_func n b = if b then n + 1 else n in 
  Array.fold_left fold_func 0 bool_arr

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
let input s =  1 + s*32

(*Première variable du round*)
let begin_round = 513 (*input*) + 3*32 (*a0 c0 d0*) + 8*32 (*carry et sum finaux*)

(*nombre de variables dans un step*)
let var_per_step = 6 * 32
(* on met Param.steps +1 à cause de a0, b0, c0, d0 qui en quelque sortent comptent pour un step*)

let last_carry_a = 513 + 3*32 
let last_carry_b = 513 + 4*32
let last_carry_c = 513 + 5*32
let last_carry_d = 513 + 6*32
let last_sum_a = 513 + 7*32
let last_sum_b = 513 + 8*32
let last_sum_c = 513 + 9*32
let last_sum_d = 513 + 10*32

(*indice dans le step des différentes variables. Les variables d'un step sont rangées par groupe de 32 variables. Ici, le premier groupe correspond aux 32 bits de a, le second ceux de b, etc. *)
let b_nb= 0
let non_lin_nb= 1
let carry41_nb= 2
let carry42_nb= 3
let sum4_nb= 4
let carry_lr_nb= 5


(*var index permet de renvoyer le numéro de la première variable d'un groupe de 32 bits. *)
let var_index step_index s = 
  begin_round + s*var_per_step + (step_index * 32) 

(*as , bs ,cs, ds avec s le numéro du step*)

let b s =  if s >= 0 then var_index b_nb s
	  else
	    match s with 
	    |(-1) -> 577 (*d0*)
	    |(-2)-> 545 (*c0*)
	    |(-3)-> 513 (*a0*)
	    | _ -> failwith "Impossible de donner à b une valeur inférieure à -4"

let a s = b (s-3)
let c s = b (s-1)
let d s = b (s-2)


(*résultat de la fonction non linéaire*)
let non_lin s = var_index non_lin_nb s

(*addition de a,f , k et snput*)
let carry41 s = var_index carry41_nb s
let carry42 s = var_index carry42_nb s
let sum4 s = var_index sum4_nb s


(*addition de b et du left_rotate*)
let carry_lr s = var_index carry_lr_nb s
(*let sum_lr s i = begin_round + s*step_nb + (8*32) + i inutile, dirrectement dans bi+1*)


(** ***********************Fonctions non linéraires *********************************)
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

let g b_start c_start d_start non_lin_start = 
  let formula_g = ref (Const true) in 
  for i = 0 to 31 do 
    formula_g := And(!formula_g,
		     Equiv(
		       Or(
			 And(pos (b_start + i), pos (d_start + i)),
			 And(neg (d_start + i), pos (c_start + i))
		       ), pos(non_lin_start + i)
		     ))
  done;
  !formula_g

let h b_start c_start d_start non_lin_start = 
  let formula_h = ref (Const true) in 
  for i = 0 to 31 do 
    formula_h := And(!formula_h,
		     Equiv(
		       Xor(
			 Xor(pos (b_start + i), pos (c_start + i)),
			 pos (d_start + i)
		       ), pos(non_lin_start + i)
		     ))
  done;
  !formula_h

let i b_start c_start d_start non_lin_start = 
  let formula_i = ref (Const true) in 
  for i = 0 to 31 do 
    formula_i := And(!formula_i,
		     Equiv(
		       Xor(
			 pos (c_start + i),
			 Or(neg (d_start + i), pos (b_start + i))
		       ), pos(non_lin_start + i)
		     ))
  done;
  !formula_i

let non_lin_func round = 
  match round with 
    |0 -> f
    |1 -> g
    |2 -> h
    |3 -> i
    | _ -> failwith "Il y a plus de 5 rounds."


(*Instructions pour tester les fonctions non linéaires :
  mettre la variable test à true
  mettre dans genCNF test_f digest
  vérifier que les premiers 32 bits du digest de l'input trouvée sont égaux aux premiers 32 bits du digest en entrée
*)

(*Permet de relier les variables que l'on souhaite aux variables de digest*)
let bound_digest_test_f digest = 
  let formula_bound = ref (Const true) in 
  for i = 0 to 31 do 
    formula_bound := And (!formula_bound, Equiv (pos (97 + i), Const(digest.(i))) )
  done;
  !formula_bound

let test_f digest =
  formulaeToCnf (And(bound_digest_test_f digest,f 1 33 65 97)) 

 

(** ****************************** Addition - rotation ***************************)

let modz a b = 
  let c = a mod b in 
  if c >= 0 then 
    c 
  else
    c + b

let formula_add_rot_bool addend1 addend2_rot carry result i r n =
  let bool_arr = int_to_bin n 3 in
  (* le nombre de booléens à la valeur true caractérise exactement le résultat de la somme et les deux retenues*)
  let nb_true = count_true bool_arr in 
  let sum_res = int_to_bin nb_true 2 in 
  Imply(list_to_formula [
    lit (addend1 + i) bool_arr.(0);
    lit (addend2_rot + (modz (i - r) 32)) bool_arr.(1) ;
    lit (carry + i) bool_arr.(2)
  ],
	if i = 31 then
	  lit (result + i) sum_res.(0)
	else
	  list_to_formula [
	    lit (result + i) sum_res.(0);
	    lit (carry + i + 1) sum_res.(1)
	  ]
  )

(*non testé*)
(* ici, dep_rot est le numéro de la première variable du mot 32 bits qui subit la rotation et dep_b est le deuxième mot 32 bits qui lui est additionné*)
let add_rotate addend1 addend2_rot carry result r  = 
  let formula_rot = ref (Equiv ( pos carry, Const false)) in 
  
  for i = 0 to 31 do 
    for j = 0 to 7 do
      formula_rot := And (!formula_rot , formula_add_rot_bool addend1 addend2_rot carry result i r j)
    done;
  done;
  !formula_rot

(*Remarque : on utilise la meme fonction pour le test da l'addition de 4 mots de 32 bits*)
let bound_digest_test_add digest = 
  let formula_bound = ref (Const true) in 
  for i = 0 to 31 do 
    formula_bound := And (!formula_bound,
			  Equiv ( pos (481 + i), Const(digest.(i))) )
  done;
  !formula_bound

(*vectK.(0) = 0xd76aa478*)
(*Pour tester la fonction add : test_add dans generate et dans md puis vérifier que le premier octet du digest reste le meme.*)
let test_add_rotate digest = 
  formulaeToCnf (And(bound_digest_test_add digest, add_rotate 1 33 65 481 3))


(** ***************************** Addition des 4 mots ****************************)


(*addendi est le ième terme de l'addition. 
  add_arr4 est un tableau de boléen dont on connait la valeur (en pratique, c'est vectK.s) pour les tests, on peut le mettre à 0. 
  carry ;: retenues
  result : résultat de l'addition
  n appartient à [0,31], il représente les 5 bits associés aux trois termes et aux deux retenues *)
let formula_add4_bool addend1 addend2 addend3 add_arr4 carry1 carry2 result i n = 
  let bool_arr = int_to_bin n 6 in  (*conversion de n en binaire avec une case de trop*)    
  bool_arr.(5) <- add_arr4.(i);
  (* le nombre de booléens à la valeur true caractérise exactement le résultat de la somme et les deux retenues*)
  let nb_true = count_true bool_arr in 
  let sum_res = int_to_bin nb_true 3 in  
  
  Imply(
    list_to_formula [
      lit (addend1 + i) bool_arr.(0);
      lit (addend2 + i) bool_arr.(1); 
      lit (addend3 + i) bool_arr.(2);
      lit (carry1 + i) bool_arr.(3);
      lit (carry2 + i) bool_arr.(4)
    ] ,

    if i = 31 then
      lit (result + i)  sum_res.(0)
    else if i = 30 then
      list_to_formula [
	lit (result + i)     sum_res.(0);
	lit (carry1 + i + 1) sum_res.(1);
      ]
    else
      list_to_formula [
	lit (result + i)     sum_res.(0);
	lit (carry1 + i + 1) sum_res.(1);
	lit (carry2 + i + 2) sum_res.(2)
      ]
  )
    
    


(*testée avec 0-digest, honest-digest, vectK.(0), falses, et trues : OK*)
let add4 addend1 addend2 addend3 add_arr4 carry1 carry2 result  = 
  (*initialisation des retenues *)
  let formula_add4 = ref (list_to_formula [
    Equiv ( pos carry1, Const false);
    Equiv ( pos carry2, Const false);
    Equiv ( pos (carry2 + 1), Const false)
  ]
  ) 
  in
  for i = 0 to 31 do 
    for j = 0 to 31 do 
      formula_add4 := And(formula_add4_bool addend1 addend2 addend3 add_arr4 carry1 carry2 result i j, !formula_add4)
    done
  done;
  !formula_add4


(*vectK.(0) = 0xd76aa478*)
(*Pour tester la fonction add : test_add dans generate et dans md puis vérifier que le premier octet du digest reste le meme.*)
let test_add digest = 
  formulaeToCnf (And(bound_digest_test_add digest, add4 1 33 65 vectK.(0) 97 129 481))


(** **************************** Initialisation ******************************* **)
let initialize digest = 
  let init_formula = ref (Const true) in 
  for i = 0 to 31 do 
    init_formula := list_to_formula [
      !init_formula;
      (*lit (a 0 + i) a0.(i);
      lit (b 0 + i) b0.(i);
      lit (c 0 + i) c0.(i);
      lit (d 0 + i) d0.(i);*)
      

      lit (last_sum_a + i) digest.(i);
      lit (last_sum_b + i) digest.(i + 32);	
      lit (last_sum_c + i) digest.(i + 64);
      lit (last_sum_d + i) digest.(i + 96)
    ]
  done;
  !init_formula


let subst_vect var_nb bool_arr formula = 
  let rec create_subst i =
    if i = Array.length bool_arr then  []
      else (var_nb + i, bool_arr.(i)) :: (create_subst (i+1)) 
  in

  Formula.subst formula (create_subst 0)

(*Permet de récupérer la valeur des première variables de l'input*)
let parse_partial_input () = 
  match !Param.partialKnownInput with 
  |Some name_file ->
    let input_str = let ic = open_in name_file in
		    try (let line = input_line ic in
			 close_in ic;
			 line)
	      with e -> close_in_noerr ic; raise e in
    Data.parseInput input_str 
  |None -> [||]
      
let inverse_md5 digest  = 
  let big_formula = ref (initialize digest) in
  for r = 0 to !Param.rounds - 1 do
    for s = r * !Param.steps to (r + 1) * !Param.steps - 1 do
      let nl = non_lin_func r (b s) (c s) (d s) (non_lin s) in 
      let addr =  add_rotate (b s) (sum4 s) (carry_lr s) (b (s+1)) vectS.(s) in 
      let add4f = add4 (a s) (non_lin s) (input (choice r s)) vectK.(s) (carry41 s) (carry42 s) (sum4 s) in 
      big_formula := 
	list_to_formula [
	    !big_formula;
	    nl;
	    addr;
	    add4f
	  ];    
	if s = 3 then
	  begin
	    big_formula := subst_vect (a 0) Data.a0 !big_formula;
	    big_formula := subst_vect (b 0) Data.b0 !big_formula;
	    big_formula := subst_vect (c 0) Data.c0 !big_formula;
	    big_formula := subst_vect (d 0) Data.d0 !big_formula;
	  end

    done
  done;
  let last_variables = !Param.rounds * !Param.steps in 
  big_formula := 
    list_to_formula [
      !big_formula;
      subst_vect (a 0) Data.a0 (add_rotate (a last_variables) (a 0) last_carry_a last_sum_a 0);
      subst_vect (b 0) Data.b0 (add_rotate (b last_variables) (b 0) last_carry_b last_sum_b 0);
      subst_vect (c 0) Data.c0 (add_rotate (c last_variables) (c 0) last_carry_c last_sum_c 0);
      subst_vect (d 0) Data.d0 (add_rotate (d last_variables) (d 0) last_carry_d last_sum_d 0);
    ] ;   
  (*big_formula := subst_32 (a 0) Data.a0 !big_formula;*)
  (*big_formula := subst_vect 1  !big_formula*)
  let partial_input = parse_partial_input () in
  Printf.printf "%d\n" !Param.partialSize;
  if Array.length partial_input = 0 then 
    formulaeToCnf !big_formula
  else
    formulaeToCnf (subst_vect 1 (Array.sub partial_input 0 !Param.partialSize ) !big_formula)

(*** Main function 
     * Digest : tableau de 128 bits ***)
let genCNF digest = 
  inverse_md5 digest


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

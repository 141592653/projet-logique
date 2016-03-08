(******************************************************************************)
(*                                                                            *)
(*                      INVERSION DE MD* VIA SAT SOLVEUR                      *)
(*                                                                            *)
(*                      Projet Logique 2016 - Partie SAT                      *)
(*   Auteur, license, etc.                                                    *)
(******************************************************************************)

open Printf
open Param

type var = int
type literal =
| Pos of var
| Neg of var
type clause = literal list
type cnf = clause list

type formula =
| Const of bool
| Lit of literal
| Not of formula
| And of formula*formula
| Or of formula*formula
| Xor of formula*formula
| Imply of formula*formula
| Equiv of formula*formula

let displayLit l = match l with
  | Pos d -> sprintf "%d" d
  | Neg d -> sprintf "-%d" d

let rec displayFormula = function
  | Const b -> sprintf "%b" b
  | Lit l -> displayLit l
  | Not f -> sprintf "Not[%s]" (displayFormula f)
  | And (f1,f2) -> sprintf "[%s] /\\ [%s]" (displayFormula f1) (displayFormula f2)
  | Or (f1,f2) -> sprintf "(%s) \\/ (%s)" (displayFormula f1) (displayFormula f2)
  | Xor (f1,f2) -> sprintf "(%s) + (%s)" (displayFormula f1) (displayFormula f2)
  | Imply (f1, f2) -> sprintf "{%s} ==> {%s}" (displayFormula f1) (displayFormula f2)
  | Equiv (f1,f2) -> sprintf "{%s} <==> {%s}" (displayFormula f1) (displayFormula f2)
    

let rec simple  f = match f with 
  |Const b -> Const b
  |Lit l -> Lit l
  |Not f2 ->
    begin 
      match f2 with 
      |Const(b) -> Const(not b)
      |Or(f3,f4) -> simple(And (Not(f3),Not(f4)))
      |And(f3,f4) -> simple (Or (Not(f3),Not(f4)))
      |Not f3 -> simple(f3)
      |Lit l -> (match l with 
	|Pos d -> Lit (Neg d)
	|Neg d -> Lit (Pos d))
      |Imply(f3,f4) -> simple(And(f3,Not(f4)))
      |Equiv(f3,f4) -> simple(Xor(f3,f4))
      |Xor(f3,f4) -> simple(Equiv(f3,f4))
    end
  |Or(f1,f2)-> (match  simple f1, simple f2 with 
    |(_,Const(true)) |(Const(true),_)  -> Const(true)
    |(a,Const(false)) -> a
    |(Const(false),a) -> a
    |(a,b) -> Or(a,b))
  |And(f1,f2)-> (match  simple f1, simple f2 with 
    |(_,Const(false)) |(Const(false),_)  -> Const(false)
    |(a,Const(true))|(Const(true),a) -> a
    |(a,b) -> And(a,b))
  |Xor(f1,f2) -> simple(Or(And(Not(f1),f2),And(f1,Not(f2))))
  |Imply(f1,f2) -> simple(Or(Not(f1),f2))
  |Equiv(f1,f2) -> simple(And(Imply(f1,f2),Imply(f2,f1)))
    

let subst f tau = 
 (*) let f_simple = simple f in *)
  let rec subst_rec f x b = match f with 
    |Const(_) -> f
    |Lit (Pos d) when (d = x) -> Const(b)
    |Lit (Neg d) when (d = x) -> Const(not b)
    |Lit _ -> f
    |Or (g,d)-> Or(subst_rec g x b, subst_rec d x b)
    |Not f -> Not (subst_rec f x b)
    |And (g,d)-> And(subst_rec g x b, subst_rec d x b)
    |Imply (g,d)-> Imply(subst_rec g x b, subst_rec d x b)
    |Equiv (g,d)-> Equiv(subst_rec g x b, subst_rec d x b)
    |Xor (g,d)-> Xor(subst_rec g x b, subst_rec d x b)
  in
  let rec subst_list l f = match l with 
    |[] -> f
    |(x,b)::q -> subst_list q (subst_rec f x b) in 
  
  subst_list tau f
    
  
let formulaeToCnf fl = 
  (*ici, pre correspond à preCcopute : on calcule d'abord la formule sous forme cnf mais avec le type formule puis on convertit avec preToCNF au type cnf.*)
  let rec simpleToPre f = match f with 
    |Const _ | Lit _ -> f
    |Or(f1,f2) -> let nf1 = simpleToPre f1 and nf2 = simpleToPre f2 in
		  begin
		    match Or(nf1,nf2) with 
		    |Or(And(f1,f2),f3) |Or(f3,And(f1,f2)) -> And(simpleToPre(Or(f1,f3)), simpleToPre(Or(f2,f3)))
		    |f -> f
		  end

    |And(f1,f2) -> And(simpleToPre f1, simpleToPre f2)
    |_ -> f
  in
  
  let rec preToCNF f = match f with 
    |Lit (l) -> [[l]]
    |Or(f1,f2) -> [(List.hd (preToCNF f1)) @ (List.hd (preToCNF f2))]
    |And(f1,f2) -> (preToCNF f1)@(preToCNF f2) 
    |Const(true) -> Printf.printf "Attention, constante dans la cnf\n\n\n\n"; [[Pos 0]]
    |Const(false) ->  Printf.printf "Attention, constante dans la cnf\n\n\n\n\n"; [[Neg 0]]
    |_ -> [[]]
  in 
  preToCNF (simpleToPre (simple fl))





(*********************** Conversion au format dimacs ************************)

(*compte grâce à une table de hachage le nombre de variables dans une formule*)
let nb_var_cnf cnf = 
  let nb_var = ref 0 in 
  let rec nb_var_clause c = 
    match c with 
    |[] -> ()
    |(Pos l)::q | (Neg l)::q -> 
      if l > !nb_var then 
	nb_var := l;
      nb_var_clause q in 
  let rec nb_var_rec cnf = match cnf with 
    |[] -> ()
    |c::q -> nb_var_clause c;
      nb_var_rec q in 
  nb_var_rec cnf;
  !nb_var

(************Affichage d'une clause ****************)
let displayClause c = 
  (*let clause_str = List.map displayLit c in*)
  let rec displayClause_rec c= match c with
    |[] -> ""
    |[l] -> displayLit l
    |l::q -> (displayLit l)^" "^(displayClause_rec q)
  in
  displayClause_rec c 
  (*(String.concat " " clause_str)*)

(* les tests montrent que ma fonction de displayClause_rec est plus rapide que le concat. Par contre, la meme fonction pour displaycnf est catastrophique : on passe de 1,4 s pour 16 steps à plusieurs minutes.*)

(******************Affichage d'une formule cnf *******************)
let displayCnf cnf = 
  let cnf_str = List.map displayClause cnf in 
  (String.concat "" (["p cnf "; string_of_int (nb_var_cnf cnf); " " ; string_of_int (List.length cnf) ; "\n" ])) ^ (String.concat " 0\n" cnf_str) ^ " 0\n"

      



(*********************** Fin conversion au format dimacs *******************)

(*** TEST ***)
let dummyCNF =
  [[Pos 1;Pos 2;Pos 3];
   [Pos 2;Pos 3;Pos 4];
   [Pos 3;Pos 4;Neg 1]
  ]
let sat_solver = ref "./minisat"

(** Return the result of minisat called on [cnf] **)
let testCNF cnf =
  let cnf_display = displayCnf cnf
  and fn_cnf = "temp_cnf.out"
  and fn_res = "temp_res.out" in
  let oc = open_out fn_cnf in
  Printf.fprintf oc "%s\n" cnf_display;
  close_out oc;
  let resc = (Unix.open_process_in
		(!sat_solver ^ " \"" ^ (String.escaped fn_cnf)
		 ^ "\" \"" ^ (String.escaped fn_res)^"\"") : in_channel) in
  let _ = Unix.close_process_in resc in
  let resSAT = let ic = open_in fn_res in
	       try (let line1 = input_line ic in
		    let line2 = try input_line ic with _ -> "" in
		    close_in ic;
		    line1^line2)
	       with e -> close_in_noerr ic; raise e in
  resSAT
    
let test () =
  Printf.printf "%s\n" (displayFormula (simple (Not(And(Lit(Pos(1)),Lit(Pos(2)))))));
  Printf.printf "%s\n" (displayFormula (simple (Xor(Lit(Pos(1)),Lit(Neg(1))))));
  Printf.printf "%s\n" (displayFormula (simple (Not(Equiv(Lit(Neg(1)),Not(And(Lit(Pos(1)),Lit(Neg(2)))))))));
  Printf.printf "%s\n" (displayCnf (formulaeToCnf (Not(And(Lit(Pos(1)),Lit(Pos(2)))))));
  Printf.printf "%s\n" (displayCnf (formulaeToCnf (Xor(Lit(Pos(1)),Lit(Neg(1))))));
  Printf.printf "%s\n" (displayCnf (formulaeToCnf (Not(Equiv(Lit(Neg(1)),Not(And(Lit(Pos(1)),Lit(Neg(2)))))))));
  Printf.printf "%s\n" (displayCnf (formulaeToCnf (Not(Equiv(Const(true),Not(And(Lit(Pos(1)),Const(false))))))));(*faux*)
  let xor = (Equiv(Const(false) , 
					     Xor(
					       Xor(Const(true),Lit(Pos(1))),
					       Xor(Lit(Pos(2)),Lit(Pos(3)))
					     )
				       )) in
  Printf.printf "%s\n" (displayCnf (formulaeToCnf xor));
  Printf.printf "%s\n" (testCNF (formulaeToCnf xor ));
  Printf.printf "%s\n" (displayFormula (simple xor ));
  Printf.printf "%d\n" (nb_var_cnf dummyCNF);
  Printf.printf "%s\n" (displayCnf dummyCNF);
  Printf.printf "%s\n" (testCNF dummyCNF);



    

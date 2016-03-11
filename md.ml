(******************************************************************************)
(*                                                                            *)
(*                      INVERSION DE MD* VIA SAT SOLVEUR                      *)
(*                                                                            *)
(*                      Projet Logique 2016 - Partie SAT                      *)
(*   Auteur, license, etc.                                                    *)
(******************************************************************************)

(* Input: only one chunk of 512 bits (16 words of 32 bits), NO padding
   Output: digest of 128 bits (WITHOUT padding)
   By default:
   - 4 rounds for the only chunk
   - each round is made of 16 steps
   - each step consume a word of the input (not linear !)
   - can be seen as 64 steps such that non-linear functions (i.e., F,G,H,I), and
   parts of inputs that are consumed depend on the current step
 *)

open Param
open Data
open Printf

(*correspondances wiki : 
r -> vectS dans data.ml
k -> vectK dans data.ml
h0,h1,h2,h3 -> a0,b0,c0,d0 dans data.ml
 *)

let xor b1 b2 = match (b1,b2) with
  |(true,true)|(false,false) -> false
  |(true,false)|(false,true) -> true

(*calcul le xor de deux vecteurs de 32 bits*)
let xor_32 a b = 
  let res = Array.make 32 false in 
  for i = 0 to 31 do 
    res.(i) <- xor a.(i) b.(i)
  done;
  res
    

(** Fonction non linéaires utilisées dans MD5, toutes sur 32 bits*)

let f_32 b c d  =
  let ret = Array.make 32 false in 
  for i = 0 to 31 do 
    ret.(i) <- (b.(i) && c.(i)) || (not b.(i) && d.(i))
  done;
  ret

let g_32 b c d = 
  let ret = Array.make 32 false in 
  for i = 0 to 31 do 
    ret.(i) <- (b.(i) && d.(i)) || (c.(i) && not d.(i))
  done;
  ret
let h_32 b c d = 
  let ret = Array.make 32 false in 
  for i = 0 to 31 do 
    ret.(i) <- xor b.(i) (xor c.(i) d.(i))
  done;
  ret
let i_32 b c d = 
  let ret = Array.make 32 false in 
  for i = 0 to 31 do 
    ret.(i) <- xor c.(i) (b.(i)|| not d.(i))
  done;
  ret

(*renvoie la fonction non linéaire associée au round r*)
let non_linear r = 
  match r with 
  |0 -> f_32
  |1 -> g_32
  |2 -> h_32
  |3 -> i_32
  |_ -> failwith "Round supérieur à 4"

(*choix du mot de l'input en fonction du step*)
let choice1 s =  s
let choice2 s =  (5*s + 1) mod 16
let choice3 s =  (3*s + 5) mod 16
let choice4 s =  (7*s) mod 16

(*renvoie la fonction de choix du mot de 32 bits dans input associée au round r*)
let choice r = 
  match r with 
  |0 -> choice1
  |1 -> choice2
  |2 -> choice3
  |3 -> choice4
  |_ -> failwith "Round supérieur à 4"


(*convertit une matrice de taille 4*32 en digest de 128 bits*)
let convert432_to_digest d = 
  let new_d  = Array.make 128 false in
  for i = 0 to 3 do 
    for j = 0 to 31 do 
      new_d.(32*i+j) <- d.(i).(j)
    done
  done;
  new_d

(*Convertit un message de 512 bits en matrice 16x32*)
let convert_input_to_32 input = 
  let input_32 = Array.make_matrix 16 32 true in
  for i = 0 to 15 do
    input_32.(i) <- Array.sub input (32*i) 32
  done;
  input_32

(*addition de deux mots 32 bits en little endian*)
let add_32 a b = 
  let ret = ref false in
  let res = Array.make 32 false in 
  for i = 0 to 31 do
    match (a.(i),b.(i),!ret) with
    |(false,false,false)  -> ret := false ; res.(i) <- false
    |(false,false,true) |(false,true,false) |(true,false,false)-> ret := false; res.(i) <- true
    |(true,true, false) |(true,false,true) |(false,true,true) -> ret := true; res.(i) <- false
    |(true,true,true) -> ret := true; res.(i) <- true
  done;
  res

(*fonction de modulo dont le résultat est toujours positif*)
let modn a b = 
  let c = a mod b in 
  if c >= 0 then 
    c 
  else
    -c

(* rotation vers la gauche en little endian*)
let left_rotate a n = 
  let res = Array.make 32 false in
  for i = 0 to 31 do 
    res.(modn (i+n) 32) <- a.(i)
  done;
  res

(******************** Fonctions de test *******************)
(*ces fonctions doivent remplacer md5 input et permettent de tester les formules correspondantes dans generate.ml *)
let test_f input = 
  let input_32 = convert_input_to_32 input in 
  let digest = Array.make_matrix 4 32 true in 
  digest.(0) <- f_32 input_32.(1) input_32.(2) input_32.(3);
  convert432_to_digest digest

let test_add_rotate input = 
  let input_32 = convert_input_to_32 input in 
  let digest = Array.make_matrix 4 32 true in 
  digest.(0) <- add_32 input_32.(0) (left_rotate input_32.(1) 3);
  convert432_to_digest digest

let test_add input = 
  let input_32 = convert_input_to_32 input in 
  let digest = Array.make_matrix 4 32 true in 
  digest.(0) <-add_32 (add_32 input_32.(0) input_32.(1)) (add_32 vectK.(0) input_32.(2));
   convert432_to_digest digest

(*Calcule le digest associé à input, c'est simplement la traduction en OCaml du pseudo code de wikipédia sans le padding.*)
let md5 input  = 
  let input_32 = convert_input_to_32 input in 
  let digest = Array.make_matrix 4 32 true in 
  let a = ref a0 and b = ref b0 and c = ref c0 and d = ref d0 in 
  for r = 0 to !Param.rounds - 1 do 
    for s = r * !Param.steps to (r + 1) * !Param.steps - 1 do  
      let temp = Array.copy !d in 
      let f = non_linear r !b !c !d in 
      d:=!c;
      c:=!b;
      b:= add_32 !b (left_rotate (add_32 (add_32 !a f ) (add_32 vectK.(s) input_32.(choice r s))) vectS.(s)) ;
      a:= temp
    done
  done;
  
  digest.(0) <- add_32 !a a0; digest.(1) <- add_32 !b b0;
  digest.(2) <- add_32 !c c0; digest.(3) <- add_32 !d d0;
  convert432_to_digest digest


(*** Main function ***)	  
let compute input =
  md5 input 


	 
(* WEAK HASH :

let d = Array.make 128 false in 
   for i = 0 to 10 do 
   d.(i) <- xor (xor d.(i+10) input.((i*13) mod 512)) (xor input.((i*14 + 1) mod 512) input.((i*15 + 2) mod 512)) 
   done;
   d*)

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

let xor_32 a b = 
  let res = Array.make 32 false in 
  for i = 0 to 31 do 
    res.(i) <- xor a.(i) b.(i)
  done;
  res
    

(** Fonction non linéaires *)

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

(*** Main function ***)	  
let compute input =
  let input_32 = convert_input_to_32 input in 
  let digest = Array.make_matrix 4 32 true in 
  let a = ref a0 and b = ref b0 and c = ref c0 and d = ref d0 in 
  for i = 0 to 63 do 
    let round = i / 16 in 
    let temp = Array.copy !d in 
    d:=!c;
    c:=!b;
    (*b:=*)
    
    
  done;
  convert432_to_digest digest


    
(* WEAK HASH let d = Array.make 128 false in 
   for i = 0 to 10 do 
   d.(i) <- xor (xor d.(i+10) input.((i*13) mod 512)) (xor input.((i*14 + 1) mod 512) input.((i*15 + 2) mod 512)) 
   done;
   d*)

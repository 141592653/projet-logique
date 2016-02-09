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

let xor b1 b2 = match (b1,b2) with
  |(true,true)|(false,false) -> false
  |(true,false)|(false,true) -> true
       
(*** Main function ***)	  
let compute input =
  let d = Array.make 128 false in 
  for i = 0 to 10 do 
    d.(i) <- xor (xor d.((i*42) mod 10) input.((i*13) mod 512)) (xor input.((i*14 + 1) mod 512) input.((i*15 + 2) mod 512)) 
  done;
  d

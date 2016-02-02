(******************************************************************************)
(*                                                                            *)
(*                      INVERSION DE MD* VIA SAT SOLVEUR                      *)
(*                                                                            *)
(*                      Projet Logique 2016 - Partie SAT                      *)
(*   Auteur, license, etc.                                                    *)
(******************************************************************************)

open Printf

type level = Low | Normal | High

let steps = ref 16 (* full MD5: 16 *)
let rounds = ref 1 (* full MD5: 4 *)
let verbose = ref High
let partialKnownInput = ref None
let partialSize = ref 0
		  
let pp = printf 

(** Prefix of each line *)
let strOfLevel = function
  | High -> "[[WARNING]]"
  | Normal -> "(Info)"
  | Low -> "--"
    
let log ?level:(lev=Normal) s =
  if lev == High || (lev == Normal && !verbose <> High) || !verbose == Low
  then printf "%s %s\n" (strOfLevel lev) s



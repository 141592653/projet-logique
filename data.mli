(******************************************************************************)
(*                                                                            *)
(*                      INVERSION DE MD* VIA SAT SOLVEUR                      *)
(*                                                                            *)
(*                      Projet Logique 2016 - Partie SAT                      *)
(*   Auteur, license, etc.                                                    *)
(******************************************************************************)

(* Convention: Least significant bit at position 0 (little-endian) *)

(*** Data types ***)
(** Internal representation of steps/words (steps of md5; i.e., a, b, c and d).
   (note: length is 32) *)
type step = bool array

(** Internal representation of digests. (note: length is 128) *)
type digest = bool array

(** Internal representation of inputs. (note: length is 512) *)
type input = bool array
		  

(*** Data managment ***)		  
(** Translate a step in hexadecimal into internal representation [step] *)
val parseStep : string -> step

(** [displayStep step] returns the hexadecimal representation of [step] *)
val displayStep : step -> string

(** Translate a digest in hexadecimal into internal representation [digest] *)
val parseDigest : string -> digest

(** [displayDigest digest] returns the hexadecimal representation of [digest] *)
val displayDigest : digest -> string

(** Translate an input in hexadecimal into internal representation [input] *)
val parseInput : string -> input

(** [displayInput input] returns the hexadecimal representation of [input] *)
val displayInput : input -> string

(** Translate an Int32 into a digest *)
val int32_to_arr : Int32.t -> digest

(** Translate a digest into an Int32 *)
val arr_to_int32 : digest -> Int32.t

(** Try to parse the string returned by minisat by extracting the valuationf of
    the 512 first variables *)
val parseSol : string -> input option

(** Equality over digest *)
val eqDigest : digest -> digest -> bool

				     
(*** Constants for MD5 ***)
(** Per-step shift amounts *)
val vectS : int array

(** Pre-step predefined constants (steps) *)
val vectK : step array
		 
(** Predefined IV (steps) *)
val a0 : step
val b0 : step
val c0 : step
val d0 : step

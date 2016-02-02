(******************************************************************************)
(*                                                                            *)
(*                      INVERSION DE MD* VIA SAT SOLVEUR                      *)
(*                                                                            *)
(*                      Projet Logique 2016 - Partie SAT                      *)
(*   Auteur, license, etc.                                                    *)
(******************************************************************************)

(*** Loggign & Verbosity ***)
(** Level of verbosity (e.g., in High mode, only very important messages are
    displayed) *)
type level = Low | Normal | High

(** Current level of verbosity *)
val verbose : level ref

(** Logging function. [level] is an optional argument (Normal by default) *)
val log : ?level:level -> string -> unit


(*** Parameters ***)
(** The number of steps of md5 *)
val steps : int ref

(** The number of rounds of md5 *)
val rounds : int ref

(** Partial information about input stored in this file (if any) *)
val partialKnownInput : string option ref

(** Size (in bits) of partial information about input stored in this file (if any) *)
val partialSize : int ref

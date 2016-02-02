(******************************************************************************)
(*                                                                            *)
(*                      INVERSION DE MD* VIA SAT SOLVEUR                      *)
(*                                                                            *)
(*                      Projet Logique 2016 - Partie SAT                      *)
(*   Auteur, license, etc.                                                    *)
(******************************************************************************)

(** Types of CNF formulae *)
type var = int
type literal =
  | Pos of var
  | Neg of var
type clause = literal list
type cnf = clause list

(** Types of formulae *)
type formula =
  | Const of bool
  | Lit of literal
  | Not of formula
  | And of formula*formula
  | Or of formula*formula
  | Xor of formula*formula
  | Imply of formula*formula
  | Equiv of formula*formula

(** Simplify formula and only keep Lit, Or, And (maybe Const but at top level) *)
val simple : formula -> formula

(** Given a substitution (var*bool) list, partially evaluates a formla *)
val subst : formula -> (var * bool) list -> formula
					     
(** Classical translation from formulae to CNF formula *)
val formulaeToCnf : formula-> cnf			    			  
(** [displayFormula formula] returns its representation *)
val displayFormula : formula -> string

(** [displayCNF formula] returns its representation in 'dimacs' format *)
val displayCnf : cnf -> string

(** Launch some tests *)
val test : unit -> unit

(******************************************************************************)
(*                                                                            *)
(*                      INVERSION DE MD* VIA SAT SOLVEUR                      *)
(*                                                                            *)
(*                      Projet Logique 2016 - Partie SAT                      *)
(*   Auteur, license, etc.                                                    *)
(******************************************************************************)

open Param
open Printf

let sat_solver = ref "./minisat"  (* executable of the chosen SAT solver *)
let invert = ref true	 	  (* invert instead of compute md5 ? *)

(* Some constants *)
let fn_cnf_suffix = "__CNF.dimacs"
let fn_res_suffix = "__inputFound.out"
let fn_digest_suffix = "__digest.out"
let fn_sol_suffix = "__CNF-sol.out"


(** All tests that are running when using option '-t'. *)
let launch_test () =
  log ~level:High "Launching tests of module Formula... ";
  Formula.test ();
  log ~level:High "End of tests... ";
  (* [TODO] You may add some tests here. *)
  exit(0)

(** Return prefix of filename [s] (before '.') *)
let basename s =
  try String.sub s 0 (String.rindex s '.')
  with Not_found -> s

		      
(** After parsing options and filename, this function is called:
    Compute pre-image (or image) of a given digest (resp. input) stored in file
    [fn_input] *)
let computeRes fn_input =
  let fn_cnf = String.concat "" [basename fn_input; fn_cnf_suffix]
  and fn_res = String.concat "" [basename fn_input; fn_res_suffix]
  and fn_digest = String.concat "" [basename fn_input; fn_digest_suffix] 
  and fn_sol = String.concat "" [basename fn_input; fn_sol_suffix] in

  (* Read inputted file *)
  let input = let ic = open_in fn_input in
	      try (let line = input_line ic in
		   close_in ic;
		   line)
	      with e -> close_in_noerr ic; raise e in
  log (sprintf "Input: [%s ]" input);
  log (sprintf "Number of rounds/steps: [%d/%d]" !Param.rounds !Param.steps);
  
  if not(!invert)
  then begin			(* then, we only compute a md5 hash *)
      (* Parse string [s] and build the representation of the input *)
      log ~level:Low "Parsing input (message)...";
      let input = Data.parseInput input in

      (* Compute digest *)
      log ~level:Low "Computing md5...";
      let digest = Md.compute input in
      log ~level:Low "Displaying digest...";
      let digest_display = Data.displayDigest digest in
      printf "==> Digest is: [ %s]\n" digest_display;

      (* Write this in digest file *)
      log (sprintf "Writing digest in %s..." fn_digest);
      let oc = open_out fn_digest in
      Printf.fprintf oc  "%s\n" digest_display;
      close_out oc;
    end
  else begin			(* then, we try to invert *)
      (* Parse string [s] and build the representation of the digest *)
      log ~level:Low "Parsing input (digest)...";
      let digest = Data.parseDigest input in

      (* Compute the CNF describing possible pre-images *)
      log ~level:Low "Computing CNF...";
      let cnf = Generate.genCNF digest in
      log ~level:Low "Displaying CNF...";
      let cnf_display = Formula.displayCnf cnf in
      (* log ~level:Low (sprintf "CNF is \n%s" cnf_display); *)

      (* Write this in CNF file *)
      log (sprintf "Writing CNF in %s..." fn_cnf);
      let oc = open_out fn_cnf in
      Printf.fprintf oc  "%s\n" cnf_display;
      close_out oc;

      (* Launch Sat-solver on CNF *)
      log (sprintf "Launching %s and write result in %s..." !sat_solver fn_sol);
      let resc = (Unix.open_process_in
		    (!sat_solver ^ " \"" ^ (String.escaped fn_cnf)^ "\""^
		       " \"" ^ (String.escaped fn_sol)^ "\"")
		  : in_channel) in
      let resSAT = let acc = ref [] in
		   try while true do
			 acc := (input_line resc) :: !acc
		       done; ""
		   with End_of_file ->
		     close_in resc;
		     if List.length !acc = 0
		     then begin
			 log ~level:High (sprintf "It seems that there is no executable called '%s' at top level." !sat_solver);
			 exit 0;
		       end
		     else String.concat "\n" (List.rev !acc) in
      close_in resc;

      (* Print the result (SAT?)*)
      log ~level:Low(sprintf "### Result of minisat:\n%s\n" resSAT);

      (* Read file outputted by sat-solver and interpret the result and print/write it *)
      log ~level:Low (sprintf "Reading file %s ..." fn_sol);
      let solSAT = let ic = open_in fn_sol in
		   try (let line1 = input_line ic in
			let line2 = try input_line ic with _ -> "" in
			close_in ic;
			line1^line2)
		   with e -> close_in_noerr ic; raise e in
      log ~level:Low (sprintf "Parsing %s ..." solSAT);
      let inputFound = Data.parseSol solSAT in
      match inputFound with
      | None -> log ~level:High (sprintf "UNSAT!\nNo input was found.");
      | Some input -> begin
	  log (sprintf "Writing found input in %s..." fn_res);
	  log ~level:High (sprintf "### Found input: [ %s]" (Data.displayInput input));
	  let oc = open_out fn_res in
	  fprintf oc "%s\n" (Data.displayInput input);
	  close_out oc;
	  log (sprintf "Compute this input and check if OK...");
	  let digest2 = Md.compute input in
	  log (sprintf "Computed digest is: [ %s]" (Data.displayDigest digest2));
	  log (sprintf "==> Are they equal?: %b" (Data.eqDigest digest digest2));
	end
    end
	 
let main () =	      
  Arg.parse [("-r", Arg.Int (fun rounds -> Param.rounds := rounds), "Fix the number of rounds");
	     ("-s", Arg.Int (fun steps -> Param.steps := steps), "Fix the number of steps");
	     ("-v", Arg.Unit (fun () -> Param.verbose := Param.Normal), "Verbose mode (normal)");
	     ("-v2", Arg.Unit (fun () -> Param.verbose := Param.Low), "Very verbose mode");
	     ("-t", Arg.Unit (fun () -> launch_test ()), "Just launch some tests");
	     ("-p", Arg.Tuple [Arg.Int (fun d -> Param.partialSize := d);
			       Arg.String (fun s -> Param.partialKnownInput := Some s)],
	      "Adding partial information about input (number of the first known bits and path)");
	     ("-c", Arg.Unit (fun () -> invert := false), "Compute md5(input) instead of inverting")
	    ]
	    (fun s -> computeRes s)
	    "Try to invert (or compute) a given hash (resp. input) (128 (resp. 512) bits given in hexadecimal)";;
  
  main ()
       

(******************************************************************************)
(*                                                                            *)
(*                      INVERSION DE MD* VIA SAT SOLVEUR                      *)
(*                                                                            *)
(*                      Projet Logique 2016 - Partie SAT                      *)
(*   Auteur, license, etc.                                                    *)
(******************************************************************************)

open Printf
open Param

type step = bool array
type digest = bool array
type input = bool array

let dummyStep = Array.make 32 false
let dummyDigest = Array.make 128 false
let dummyInput = Array.make 512 false

(** Exponentiation over integers *)
let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n ->
     let b = pow a (n / 2) in
     b * b * (if n mod 2 = 0 then 1 else a)
	       
(** Translate an Int32 into a digest *)
let int32_to_arr int32 = 
  let int = ((Int32.to_int int32) + (pow 2 32)) mod (pow 2 32) in (* TODO: moche *)
  let arr32 = Array.make 32 false in
  for i = 0 to 31 do
    arr32.(i) <- ((int / (pow 2 i)) mod 2 = 1)
  done;
  arr32

(** Translate a digest into a Int32 *)
let arr_to_int32 arr = 
  let int32 = ref Int32.zero in
  for i = 0 to 31 do
    if arr.(i) then
      int32 := Int32.add !int32 (Int32.shift_left Int32.one i)
  done;
  !int32

let parseStep s =
  let hex = Int32.of_string s in
  int32_to_arr hex
	       
let parseDigest s =
  let strList = Str.split (Str.regexp " +") s in
  let hexList = List.map (fun s -> (Int32.of_string s)) strList in
  if List.length hexList <> 4 then begin
      log ~level:High "Digest input should contain 4 hexadecimals values separated by '\\n' or ' '.";
      failwith "Critical error";
    end;
  List.fold_right (fun hex acc -> Array.append (int32_to_arr hex) acc)  hexList (Array.make 0 false)

		  
let parseInput s =      
  let strList = Str.split (Str.regexp " +") s in
  let hexList = List.map (fun s -> (Int32.of_string s)) strList in
  if List.length hexList <> 16 then begin
      log ~level:High "Message input should contain 16 hexadecimals values separated by '\\n' or ' '.";
      failwith "Critical error";
    end;
  List.fold_right (fun hex acc -> Array.append (int32_to_arr hex) acc) hexList (Array.make 0 false)

(** Display a bool array containing [nbWords] of 32-bits words *)
let displayGen tab nbWords =
  let acc = ref "" in
  for i = 0 to (nbWords-1) do
    let word = Array.sub tab (32*i) 32 in
    let wordInt32 = arr_to_int32 word in
    acc := !acc ^ (sprintf "0x%lx " wordInt32)
  done;
  !acc
   
let displayStep step =
  if Array.length step <> 32 then begin
      log ~level:High "Step is not 32 bits long.";
      failwith "Critical error";
    end;
  displayGen step 1
	     
let displayInput input =
  if Array.length input <> 512 then begin
      log ~level:High "Input is not 512 bits long.";
      failwith "Critical error";
    end;
  displayGen input 16
	     
let displayDigest digest =
  if Array.length digest <> 128 then begin
      log ~level:High "Digest is not 128 bits long.";
      failwith "Critical error";
    end;
  displayGen digest 4


let parseSol s =
  let isSat = s.[0] = 'S' in
  if not(isSat)
  then None
  else begin
      let strList = Str.split (Str.regexp " +") s in
      let fstStr = List.hd strList in (* is of the form 'SAT [fstVar] *)
      let strListClean = (String.sub fstStr 3 ((String.length fstStr)-3)) :: (List.tl strList) in
      let strArray = Array.of_list strListClean in
      let inputInt = Array.sub strArray 0 512 in (* extract the first 512 variables *)
      let input = Array.map (fun d -> (int_of_string d) > 0) inputInt in
      Some input
    end

let eqDigest d1 d2 =
  try
    for i = 0 to 127 do
      if d1.(i) <> d2.(i) then failwith ""
    done;
    true
  with _ -> false

	      
(* HARD-CODED CONSTANTS *)
let vectS = 	     (* r_i *)
  [| 7; 12; 17; 22;  7; 12; 17; 22;  7; 12; 17; 22;  7; 12; 17; 22;
     5;  9; 14; 20;  5;  9; 14; 20;  5;  9; 14; 20;  5;  9; 14; 20;
     4; 11; 16; 23;  4; 11; 16; 23;  4; 11; 16; 23;  4; 11; 16; 23; 
     6; 10; 15; 21;  6; 10; 15; 21;  6; 10; 15; 21;  6; 10; 15; 21 |]
    
(* Least significant bit at position 0 *)
let a0 = parseStep "0x67452301"
let b0 = parseStep "0xEFCDAB89"
let c0 = parseStep "0x98BADCFE"
let d0 = parseStep "0x10325476"
			
let vectK =
  Array.map parseStep
	    [|
	      "0xd76aa478"; "0xe8c7b756"; "0x242070db"; "0xc1bdceee";
	      "0xf57c0faf"; "0x4787c62a"; "0xa8304613"; "0xfd469501";
	      "0x698098d8"; "0x8b44f7af"; "0xffff5bb1"; "0x895cd7be";
	      "0x6b901122"; "0xfd987193"; "0xa679438e"; "0x49b40821";
	      "0xf61e2562"; "0xc040b340"; "0x265e5a51"; "0xe9b6c7aa";
	      "0xd62f105d"; "0x02441453"; "0xd8a1e681"; "0xe7d3fbc8";
	      "0x21e1cde6"; "0xc33707d6"; "0xf4d50d87"; "0x455a14ed";
	      "0xa9e3e905"; "0xfcefa3f8"; "0x676f02d9"; "0x8d2a4c8a";
	      "0xfffa3942"; "0x8771f681"; "0x6d9d6122"; "0xfde5380c";
	      "0xa4beea44"; "0x4bdecfa9"; "0xf6bb4b60"; "0xbebfbc70";
	      "0x289b7ec6"; "0xeaa127fa"; "0xd4ef3085"; "0x04881d05";
	      "0xd9d4d039"; "0xe6db99e5"; "0x1fa27cf8"; "0xc4ac5665";
	      "0xf4292244"; "0x432aff97"; "0xab9423a7"; "0xfc93a039";
	      "0x655b59c3"; "0x8f0ccc92"; "0xffeff47d"; "0x85845dd1";
	      "0x6fa87e4f"; "0xfe2ce6e0"; "0xa3014314"; "0x4e0811a1";
	      "0xf7537e82"; "0xbd3af235"; "0x2ad7d2bb"; "0xeb86d391"
	     |]

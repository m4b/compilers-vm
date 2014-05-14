(* 
   compile:
   ocamlopt.opt -unsafe -ccopt -O5 -S -inline 20 -nodynlink m32x.ml -o m32x

   profile:
   ocamlopt.opt -p -unsafe -ccopt -O5 -S -inline 20 -nodynlink m32x.ml -o m32xp ; ocamloptp -p m32x.ml

   copyleft: Matthew Barney

   ==========

*)

open Sys
open Printf

let ( $ ) f x = f x
let sob byte = 
  sprintf "0x%02x" byte

let programName () = 
  if Array.length argv < 2 then 
    begin
      printf "Usage: machine <program name>\n";
      exit 1
    end
  else
    argv.(1)

let programExists pn =
  if file_exists pn then
    ()
  else
    begin
      printf "Program '%s' not found.\n" pn;
      exit 1
    end

let make_byte_array channel = 
  let size = in_channel_length channel in
  let ar = Array.make size 0 in
  for i = 0 to size - 1 do
    ar.(i) <- input_byte channel
  done;
  ar

exception BAD_OPCODE of string

(* get leftmost hex bit *)
let oc hex = hex lsr 28

let nibbleN n hex =
  (hex lsr (n*4)) land 0xf

let div32 x y =
  let word = 4294967296 in
  let x' = 
    if x < 0 then
      word + x
    else
      x in
  let y' = 
    if y < 0 then
      word + y
    else
      y in
  x' / y'


(* nand from 64bit signed to emulating 32 bit unsigned *)
(* ... so not portable ? *)
(* let nand a b = 0xffffffff land (lnot (a land b)) *)
let nand a b = 
  let word = 4294967296 in
  let res = lnot (a land b) in
  if res < 0 then
    word + res
  else
    res

(* register functions *)
(* ================== *)

let init_registers () =  Array.make 8 0x0

(*   program instruction``arrays''  *)
(* ================================ *)

(* c bigarrays *)
(*
open Bigarray

let setp ar offset value = ar.{offset} <- value

let getp ar offset = ar.{offset}

let makep size =
  let a = Array1.create int c_layout size in
  Array1.fill a 0x0;
  a

let make_instruction_array ar =
  let instruction_ar = makep ((Array.length ar) / 4) in
  for i = 0 to (Array.length ar) / 4 - 1 do
    let instruction = 
      (ar.(4*i)   lsl 24)  +
      (ar.(4*i+1) lsl 16)  +
      (ar.(4*i+2) lsl 8)   +
      (ar.(4*i+3))
    in
    instruction_ar.{i} <- instruction
  done;
  instruction_ar
*)
(* OCaml arrays *)

let setp ar offset value = ar.(offset) <- value

let getp ar offset = ar.(offset)

let make_instruction_array ar =
  let instruction_ar = Array.create ((Array.length ar) / 4) 0x0  in
  for i = 0 to (Array.length ar) / 4 - 1 do
    let instruction = 
      (ar.(4*i)   lsl 24)  +
      (ar.(4*i+1) lsl 16)  +
      (ar.(4*i+2) lsl 8)   +
      (ar.(4*i+3))
    in
    instruction_ar.(i) <- instruction
  done;
    instruction_ar


(*    memory functions      *)
(* ======================== *)

let memsize = 10000000
let addressStack = Stack.create ()
let addressCounter = ref 0

let getaddress ac =
  if Stack.is_empty addressStack then
    ac + 1
  else
    Stack.pop addressStack

(* malloc returns identifier *)
let malloc words memory =
  let address =
    if Stack.is_empty addressStack then
      begin
	incr addressCounter;
	!addressCounter
      end
    else
      Stack.pop addressStack
  in
  memory.(address) <- Array.create words 0x0;
  address
  
let destructiveLoad program memory =
  let program' = Array.copy program in
  memory.(0x0) <- program'

let init_memory iar = 
  let mem = Array.create memsize [||] in
  mem.(0) <- iar;
  mem

(* execute instructions *)
(* ==================== *)

let rec execute1 reg memory eip halt ac =

  if halt then
    ()
  else

    let instruction = memory.(0x0).(eip) in
    let opcode = oc instruction in
    let c = 7 land instruction in
    let b = 7 land (instruction lsr 3) in
    let a = 7 land (instruction lsr 6) in
  
  begin
    match opcode with

      0x0 -> 
	if (reg.(c)) = 0x0 then
	  ()
	else
	  reg.(a) <- reg.(b);
	execute1 reg memory (eip+1) halt ac

    | 0x1 ->
	let address = reg.(b) in
	let offset = reg.(c) in
	let value = memory.(address).(offset) in
	reg.(a) <- value;
	execute1 reg memory (eip+1) halt ac
	    
    | 0x2 -> 
	let address = reg.(a) in
	let offset = reg.(b) in
	let value = reg.(c) in
	memory.(address).(offset) <- value;
	execute1 reg memory (eip+1) halt ac
	
    | 0x3 ->
	let value = (reg.(b) + reg.(c)) mod 4294967296 in
	reg.(a) <- value;
	execute1 reg memory (eip+1) halt ac

    | 0x4 ->
	let value = (reg.(b) * reg.(c)) mod 4294967296 in
	reg.(a) <- value;
	execute1 reg memory (eip+1) halt ac

    | 0x5 ->
	let value = reg.(b) / reg.(c) in
	reg.(a) <- value;
	execute1 reg memory (eip+1) halt ac


    | 0x6 ->
	let value = nand reg.(b) (reg.(c)) in
	reg.(a) <- value;
	execute1 reg memory (eip+1) halt ac

    | 0x7 ->
	execute1 reg memory (eip+1) true ac

    | 0x8 ->
	let words = reg.(c) in
	let address = getaddress ac in
	memory.(address) <- Array.create words 0x0;
	reg.(b) <- address;
	execute1 reg memory (eip+1) halt address

    | 0x9 ->
	let address = reg.(c) in
	Stack.push address addressStack;
	execute1 reg memory (eip+1) halt ac
     
    | 0xa ->

	let value = reg.(c) in
	let ascii = char_of_int value in 
	flush stdout;
	print_char ascii;
	execute1 reg memory (eip+1) halt ac

    | 0xb ->

	flush stdout;
	let input = input_byte stdin in
	reg.(c) <- input;
	execute1 reg memory (eip+1) halt ac

    | 0xc ->
	let address = reg.(b) in
	let offset = reg.(c) in
	if address = 0x0 then
	  ()
	else
	  destructiveLoad (memory.(address)) memory;
	execute1 reg memory offset halt ac

    | 0xd ->
	reg.((nibbleN 6 instruction) lsr 1) <- 33554431 land instruction;
	execute1 reg memory (eip+1) halt ac

    | opcode ->
	raise (BAD_OPCODE (sob opcode))
  end


let init iar =
  let genreg = init_registers () in
  let memory = init_memory iar in
  genreg,memory

let parseArgs () =
  let len = Array.length argv in
  if len < 2 then 
    begin
      printf "Usage: machine <program name>\n";
      exit 1
    end
  else
    argv.(1)

let main  =
  begin
    let program = parseArgs () in
    programExists program;
    let programChannel = open_in program in

    let programArray = make_byte_array programChannel in
    let executable = make_instruction_array programArray in
    let (reg, memory) = init executable in

    close_in programChannel;
    flush stdout;

    Gc.set { (Gc.get()) with Gc.minor_heap_size = (262144*64)};
    Gc.set { (Gc.get()) with Gc.major_heap_increment = (126976*64)};

    execute1 reg memory 0 false 0;
    printf "Time elapsed since execution: %f\n" (time ());
    exit 0;
     
  end

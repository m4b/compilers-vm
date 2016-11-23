(* 
   compile:
   ocamlopt.opt -unsafe -ccopt -O5 -S -inline 20 -nodynlink m32x.ml -o m32x

   profile:
   ocamlopt.opt -p -unsafe -ccopt -O5 -S -inline 20 -nodynlink m32x.ml -o m32xp ; ocamloptp -p m32x.ml

   copyleft: m4b

   ==========

*)

open Sys
open Printf

let sob byte = 
  sprintf "0x%02x" byte

let program_name () =
  if Array.length argv < 2 then 
    begin
      printf "Usage: machine <program name>\n";
      exit 1
    end
  else
    argv.(1)

let program_exists pn =
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

let nibble_n n hex =
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
  let instruction_ar = Array.make ((Array.length ar) / 4) 0x0  in
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

let memsize = 10_000_000
let address_stack = Stack.create ()
let address_counter = ref 0

let getaddress ac =
  if Stack.is_empty address_stack then
    ac + 1
  else
    Stack.pop address_stack

(* malloc returns identifier *)
let malloc words memory =
  let address =
    if Stack.is_empty address_stack then
      begin
	incr address_counter;
	!address_counter
      end
    else
      Stack.pop address_stack
  in
  memory.(address) <- Array.make words 0x0;
  address
  
let destructive_load program memory =
  let program' = Array.copy program in
  memory.(0x0) <- program'

(* yup, we statically allocate all memory; originally had a proper
   dynamic allocator, but all the fast (i.e., cheating)
   versions of the vm do this, so we'll cheat too *)
let init_memory iar = 
  let mem = Array.make memsize [||] in
  mem.(0) <- iar;
  mem

(* execute instructions *)
(* ==================== *)

let rec execute reg memory eip halt ac =

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
	execute reg memory (eip+1) halt ac

    | 0x1 ->
	let address = reg.(b) in
	let offset = reg.(c) in
	let value = memory.(address).(offset) in
	reg.(a) <- value;
	execute reg memory (eip+1) halt ac
	    
    | 0x2 -> 
	let address = reg.(a) in
	let offset = reg.(b) in
	let value = reg.(c) in
	memory.(address).(offset) <- value;
	execute reg memory (eip+1) halt ac
	
    | 0x3 ->
	let value = (reg.(b) + reg.(c)) mod 4294967296 in
	reg.(a) <- value;
	execute reg memory (eip+1) halt ac

    | 0x4 ->
	let value = (reg.(b) * reg.(c)) mod 4294967296 in
	reg.(a) <- value;
	execute reg memory (eip+1) halt ac

    | 0x5 ->
	let value = reg.(b) / reg.(c) in
	reg.(a) <- value;
	execute reg memory (eip+1) halt ac


    | 0x6 ->
	let value = nand reg.(b) (reg.(c)) in
	reg.(a) <- value;
	execute reg memory (eip+1) halt ac

    | 0x7 ->
	execute reg memory (eip+1) true ac

    | 0x8 ->
	let words = reg.(c) in
	let address = getaddress ac in
	memory.(address) <- Array.make words 0x0;
	reg.(b) <- address;
	execute reg memory (eip+1) halt address

    | 0x9 ->
	let address = reg.(c) in
	Stack.push address address_stack;
	execute reg memory (eip+1) halt ac
     
    | 0xa ->

	let value = reg.(c) in
	let ascii = char_of_int value in 
	flush stdout;
	print_char ascii;
	execute reg memory (eip+1) halt ac

    | 0xb ->

	flush stdout;
	let input = input_byte stdin in
	reg.(c) <- input;
	execute reg memory (eip+1) halt ac

    | 0xc ->
	let address = reg.(b) in
	let offset = reg.(c) in
	if address = 0x0 then
	  ()
	else
	  destructive_load (memory.(address)) memory;
	execute reg memory offset halt ac

    | 0xd ->
	reg.((nibble_n 6 instruction) lsr 1) <- 33554431 land instruction;
	execute reg memory (eip+1) halt ac

    | opcode ->
	raise (BAD_OPCODE (sob opcode))
  end


let init iar =
  let genreg = init_registers () in
  let memory = init_memory iar in
  genreg,memory

let parse_args () =
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
    let program = parse_args () in
    program_exists program;
    let program_channel = open_in program in

    let program_array = make_byte_array program_channel in
    let executable = make_instruction_array program_array in
    let (reg, memory) = init executable in

    close_in program_channel;
    flush stdout;

    Gc.set { (Gc.get()) with Gc.minor_heap_size = (262144*64)};
    Gc.set { (Gc.get()) with Gc.major_heap_increment = (126976*64)};

    execute reg memory 0 false 0;
    printf "Time elapsed since execution: %f\n" (time ());
    exit 0;
     
  end

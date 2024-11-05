(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

module Platform = Util.Platform

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge



(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m

let caller_saved = [ Reg Rax
                   ; Reg Rcx
                   ; Reg Rdx
                   ; Reg Rsi
                   ; Reg Rdi
                   ; Reg R08
                   ; Reg R09
                   ; Reg R10
                   ; Reg R11 ]

let callee_saved = [ Reg Rbx
                   ; Reg Rbp
                   ; Reg R12
                   ; Reg R13
                   ; Reg R14
                   ; Reg R15 ]

exception Not_a_regster

let compile_save_regs (regs : X86.operand list) : X86.ins list =
  List.map
    (function
      | Reg r -> Pushq, [Reg r]
      | _ -> raise Not_a_regster)
    regs

let compile_restore_regs (regs : X86.operand list) : X86.ins list =
  List.rev_map
    (function
      | Reg r -> Popq, [Reg r]
      | _ -> raise Not_a_regster)
    regs

(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip) %rax.

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt : ctxt) (dest : X86.operand) : Ll.operand -> ins =
  function
  | Null -> Movq, [Imm (Lit 0L); dest]
  | Const c -> Movq, [Imm (Lit c); dest]
  | Id i -> Movq, [lookup ctxt.layout i; dest]
  | Gid g -> Leaq, [Ind3 (Lbl (Platform.mangle g), Rip); dest]



(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: Don't forget to preserve caller-save registers (only if needed). ]

   [ NOTE: Remember, call can use labels as immediates! You shouldn't need to
     perform any RIP-relative addressing for this one. ]

   [ NOTE: It is the caller's responsibility to clean up arguments pushed onto
     the stack, so you must free the stack space after the call returns. (But
     see below about alignment.) ]

   [ NOTE: One important detail about the ABI besides the conventions is that,
  at the time the [callq] instruction is invoked, %rsp *must* be 16-byte aligned.
  However, because LLVM IR provides the Alloca instruction, which can dynamically
  allocate space on the stack, it is hard to know statically whether %rsp meets
  this alignment requirement.  Moroever: since, according to the calling
  conventions, stack arguments numbered > 6 are pushed to the stack, we must take
  that into account when enforcing the alignment property.

  We suggest that, for a first pass, you *ignore* %rsp alignment -- only a few of
  the test cases rely on this behavior.  Once you have everything else working,
  you can enforce proper stack alignment at the call instructions by doing
  these steps:
    1. *before* pushing any arguments of the call to the stack, ensure that the
    %rsp is 16-byte aligned.  You can achieve that with the x86 instruction:
    `andq $-16, %rsp`  (which zeros out the lower 4 bits of %rsp, possibly
    "allocating" unused padding space on the stack)

    2. if there are an *odd* number of arguments that will be pushed to the stack
    (which would break the 16-byte alignment because stack slots are 8 bytes),
    allocate an extra 8 bytes of padding on the stack.

    3. follow the usual calling conventions - any stack arguments will still leave
    %rsp 16-byte aligned

    4. after the call returns, in addition to freeing up the stack slots used by
    arguments, if there were an odd number of slots, also free the extra padding.

  ]
*)

let arg_regs = [ Reg Rdi
               ; Reg Rsi
               ; Reg Rdx
               ; Reg Rcx
               ; Reg R08
               ; Reg R09 ]

let compile_call (ctxt : ctxt) (fop, fargs : Ll.operand * (ty * Ll.operand) list) : X86.ins list =
  failwith "compile_call not implemented"


(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls : (tid * ty) list) (t : Ll.ty) : int =
  match t with
  | Void | I8 | Fun _ -> 0
  | I1 | I64 | Ptr _ -> 8
  | Struct ts -> List.fold_left (fun acc t -> acc + size_ty tdecls t) 0 ts
  | Array (n, t) -> n * size_ty tdecls t
  | Namedt tid -> size_ty tdecls (lookup tdecls tid)




(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)
let compile_gep (ctxt : ctxt) (op : Ll.ty * Ll.operand) (path : Ll.operand list) : ins list =
  failwith "compile_gep not implemented"



(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let compile_insn (ctxt : ctxt) ((uid : uid), (i : Ll.insn)) : X86.ins list =
  let compile_operand = compile_operand ctxt
  and lookup = lookup ctxt.layout in
  match i with

  | Binop (bop, _, op1, op2) ->
    let a = Reg Rax and b = Reg Rcx in
    let dest = lookup uid in
    begin
      [ compile_operand a op1
      ; compile_operand b op2 ]
      @ (match bop with
        | Add  -> [Addq,  [b; a]]
        | Sub  -> [Subq,  [b; a]]
        | Mul  -> [Imulq, [b; a]]
        | And  -> [Andq,  [b; a]]
        | Or   -> [Orq,   [b; a]]
        | Xor  -> [Xorq,  [b; a]]
        | Shl  -> [Shlq,  [b; a]]
        | Lshr -> [Shrq,  [b; a]]
        | Ashr -> [Sarq,  [b; a]]) @
      [ Movq, [a; dest] ]
    end

  | Alloca ty ->
    let size = size_ty ctxt.tdecls ty in
    let dest = lookup uid in
    [
      Subq, [Imm (Lit (Int64.of_int size)); Reg Rsp];
      Movq, [Reg Rsp; dest]
    ]

  (* TODO: error handling *)
  | Load (_, op) ->
    let dest = lookup uid in
    [
      compile_operand (Reg Rax) op;
      Movq, [Ind2 Rax; Reg Rax];
      Movq, [Reg Rax; dest]
    ]

  (* TODO: error handling *)
  | Store (_, op1, op2) ->
    [
      compile_operand (Reg Rax) op1;
      compile_operand (Reg Rcx) op2;
      Movq, [Reg Rax; Ind2 Rcx];
    ]

  | Icmp (cnd, _, op1, op2) ->
    let a = Reg Rax and b = Reg Rcx in
    let dest = lookup uid in
    [
      compile_operand a op1;
      compile_operand b op2;
      Cmpq, [a; b];
      Movq, [Imm (Lit 0L); a];
      Set (compile_cnd cnd), [a];
      Movq, [a; dest]
    ]

  (* TODO: error handling *)
  | Call (Void, fop, fargs) ->
    compile_call ctxt (fop, fargs)

  (* TODO: error handling *)
  | Call (_, fop, fargs) ->
    let dest = lookup uid in
    (* Assume compile_call puts the return value in rax. *)
    compile_call ctxt (fop, fargs)
    @ [Movq, [Reg Rax; dest]]

  | Bitcast (_, op, _) ->
    let dest = lookup uid in
    [
      compile_operand (Reg Rax) op;
      Movq, [Reg Rax; dest]
    ]

  | Gep (ty, op, path) ->
    let dest = lookup uid in
    (* Assume compile_gep puts the result pointer in rax. *)
    compile_gep ctxt (ty, op) path
    @ [Movq, [Reg Rax; dest]]

(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are
   globally unique . *)
let mk_lbl (fn : string) (l :string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let compile_terminator (fn : string) (ctxt : ctxt) (t : Ll.terminator) : ins list =
  let mk_lbl = mk_lbl fn in
  (* We don't use any other callee-saved registers so we don't restore them here. *)
  let epilog = [ Movq, [Reg Rbp; Reg Rsp]
               ; Popq, [Reg Rbp]
               ; Retq, [] ] in
  match t with
  | Ret (_, None)
    -> epilog
  | Ret (_, Some operand)
    -> (compile_operand ctxt (Reg Rax) operand)
       :: epilog
  | Br lbl
    -> [ Jmp, [Imm (Lbl (mk_lbl lbl))] ]
  | Cbr (operand, lbl1, lbl2)
    -> [ compile_operand ctxt (Reg Rax) operand
       ; Cmpq, [Imm (Lit 1L); (Reg Rax)]
       ; J Eq, [Imm (Lbl (mk_lbl lbl1))]
       ; Jmp, [Imm (Lbl (mk_lbl lbl2))] ]

(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete.
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let compile_block (fn : string) (ctxt : ctxt) (blk : Ll.block) : ins list =
  (blk.insns |> List.map (compile_insn ctxt) |> List.flatten) @
  compile_terminator fn ctxt (snd blk.term)


let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)


(* Complete this helper function, which computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions. We will test this function as part of
   the hidden test cases.

   You might find it useful for compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
(* Note: this function is here only to satisfy some test cases. *)
let arg_loc (n : int) : operand =
  if n < 6 then
    List.nth arg_regs n
  else
    let offset = (n - 6) * 8 + 16 in
    Ind3 (Lit (Int64.of_int offset), Rbp)


(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals

*)
(* Note: we only copy function arguments in registers to stack.

   function frame:

          --------------------
         |        ...         |
         |       arg 7        |
         |       arg 6        |
         |     saved rip      |
         |     saved rsp      |
   rbp -> --------------------
         |     arg 0 copy     |
         |        ...         |
         |     arg 5 copy     |
         |      local %1      |
         |      local %2      |
         |        ...         |
          --------------------
*)
let stack_layout (args : uid list) ((block, lbled_blocks) : cfg) : layout =
  let args_layout =
    List.mapi (
      fun i arg ->
        arg,
        let offset = if i < 6 then -8 - i * 8 else (i - 6) * 8 + 16 in
          Ind3 (Lit (Int64.of_int offset), Rbp)
    ) args
  and _, locals_layout =
    List.fold_left (
      fun (i, lyt) (uid, insn) -> match insn with
        | Store _ | Call (Void, _ , _)
          -> i, lyt
        | _
          -> let local_offset = - 8 * (i + List.length arg_regs) in
             i + 1, (uid, Ind3 (Lit (Int64.of_int local_offset), Rbp)) :: lyt
    ) (1, []) (
      block.insns @
      (lbled_blocks
        |> List.map (fun (_, b) -> b.insns)
        |> List.flatten)
    ) in
  args_layout @ locals_layout


(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)
let compile_fdecl (tdecls : (tid * ty) list) (name : string) ({ f_param; f_cfg; _ } : fdecl) : prog =
  let entry_block, lbled_blocks = f_cfg in
  let context = {tdecls = tdecls; layout = stack_layout f_param f_cfg} in
  (* In LLVMlite, there's no `internal` function definitions, so all
     functions are treated as `global` labels in X86lite. *)
  (* Entry block. *)
  Asm.gtext name (
    (* Prolog. We don't use any other callee-saved registers so we don't save them here. *)
    [ Pushq, [Reg Rbp]
    ; Movq, [Reg Rsp; Reg Rbp] ]
    @ (compile_save_regs arg_regs) @
    [ let local_stack_size = (List.length context.layout - List.length f_param) * 8 in
      Subq, [Imm (Lit (Int64.of_int local_stack_size)); Reg Rsp] ]
    @ compile_block name context entry_block
  )
  (* Labeled blocks. *)
  :: List.map (fun (lbl, block) -> compile_lbl_block name lbl context block) lbled_blocks

(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (_t1,g,_t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog ({tdecls; gdecls; fdecls; _} : Ll.prog) : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)


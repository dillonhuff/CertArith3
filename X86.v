(* x86-64 processor model *)

(* We only need a few registers *)
Inductive x86Reg : Set :=
| RAX : x86Reg
| RCX : x86Reg
| RBP : x86Reg
| RSP : x86Reg.

Inductive x86Instr : Set :=
| Pushq : x86Reg -> x86Instr
| Popq : x86Reg -> x86Instr
| Addq : x86Reg -> x86Reg -> x86Instr
| Subq : x86Reg -> x86Reg -> x86Instr
| IMulq : x86Reg -> x86Reg -> x86Instr
| Ret.

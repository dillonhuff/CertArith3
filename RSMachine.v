Require Import List ZArith.

(* RSMachine definition *)

Inductive rsReg : Set :=
| RS0
| RS1.

Definition beq_rsReg (r0 r1 : rsReg) : bool :=
  match r0, r1 with
    | RS0, RS0 => true
    | RS1, RS1 => true
    | _, _ => false
  end.

Definition rsArg := nat.

Inductive rsBop : Set :=
| RSAdd : rsBop
| RSSub : rsBop
| RSMul : rsBop.

Inductive rsInstr : Set :=
| PushReg : rsReg -> rsInstr
| PushArg : rsArg -> rsInstr
| Pop : rsReg -> rsInstr
| RSBinop : rsBop -> rsReg -> rsReg -> rsInstr.

Record rsMachine :=
  {
    rsRegValMap : rsReg -> Z;
    rsArgValMap : rsArg -> Z;
    rsStk : list Z
  }.

Definition rsProgram := list rsInstr.

(* RSMachine program evaluation *)

Open Scope Z_scope.

Definition evalRSBop (b : rsBop) (v0 v1 : Z) :=
  match b with
    | RSAdd => v0 + v1
    | RSSub => v0 - v1
    | RSMul => v0 * v1
  end.

Inductive rsBopEvalR : rsBop-> Z -> Z -> Z -> Prop :=
| RSBopEvalR : forall b v0 v1, rsBopEvalR b v0 v1 (evalRSBop b v0 v1).

Inductive rsInstrEvalR : rsMachine -> rsInstr -> rsMachine -> Prop :=
| RSInstrEvalR_pushReg :
    forall r rvm ram stk,
      rsInstrEvalR
        (Build_rsMachine rvm ram stk)
        (PushReg r)
        (Build_rsMachine rvm ram (rvm r :: stk))
| RSInstrEvalR_pushArg :
    forall a rvm ram stk,
      rsInstrEvalR
        (Build_rsMachine rvm ram stk)
        (PushArg a)
        (Build_rsMachine rvm ram (ram a :: stk))
| RSInstrEvalR_pop :
    forall v r rvm ram stk,
      rsInstrEvalR
        (Build_rsMachine rvm ram (v :: stk))
        (Pop r)
        (Build_rsMachine
           (fun x => if beq_rsReg x r then v else rvm x) ram stk)
| RSInstrEvalR_rsBinop :
    forall r0 r1 b rvm ram stk r,
      rsBopEvalR b (rvm r1) (rvm r0) r ->
      rsInstrEvalR
        (Build_rsMachine rvm ram stk)
        (RSBinop b r0 r1)
        (Build_rsMachine
           (fun x => if beq_rsReg x r1 then r else rvm x)
           ram
           stk).

(* RSMachine properties *)


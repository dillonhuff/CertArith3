Require Import List ZArith.

Require Import StkMachine RSMachine.

(* Compilation of StkMachine programs into RSMachine programs *)

Definition sBopToRSBop (b : sBop) : rsBop :=
  match b with
    | SAdd => RSAdd
    | SSub => RSSub
    | SMul => RSMul
  end.

Definition stkInstrToRSInstrs (i : stkInstr) : list rsInstr :=
  match i with
    | Push a => PushArg (RSArg (stkArgName a)) :: nil
    | SBinop b =>
      Pop RS0 :: Pop RS1 :: RSBinop (sBopToRSBop b) RS0 RS1 :: PushReg RS1 :: nil
  end.




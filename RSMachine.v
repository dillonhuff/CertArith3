Require Import List ZArith.

Inductive rsReg : Set :=
| RS0
| RS1.

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


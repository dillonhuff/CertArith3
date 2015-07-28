Require Import List ZArith.

(* Stack machine definition *)

Definition stkArg : Set := nat.
Definition stkArgName (a : stkArg) : nat := a.

Inductive sBop : Set :=
| SAdd : sBop
| SSub : sBop
| SMul : sBop.

Inductive stkInstr : Set :=
| Push : stkArg -> stkInstr
| SBinop : sBop -> stkInstr.

Record stkMachine :=
  {
    smArgMap : stkArg -> Z;
    smStk : list Z
  }.

Definition stkProgram := list stkInstr.

(* Stack machine program semantics *)

Inductive sBopEvalR : Z -> Z -> Z -> Prop :=
| sBopEvalR_add : forall v1 v2, sBopEvalR v1 v2 (v1 + v2)
| sBopEvalR_sub : forall v1 v2, sBopEvalR v1 v2 (v1 - v2)
| sBopEvalR_mul : forall v1 v2, sBopEvalR v1 v2 (v1 * v2).

Inductive stkInstrEvalR : stkMachine -> stkInstr -> stkMachine -> Prop :=
| StkInstrEvalR_Push : forall sav stk a,
                         stkInstrEvalR
                           (Build_stkMachine sav stk)
                           (Push a)
                           (Build_stkMachine sav ((sav a) :: stk))
| StkInstrEval_SBinop : forall b sav stk v1 v2 res,
                          (sBopEvalR v1 v2 res) ->
                          stkInstrEvalR
                            (Build_stkMachine sav (v2 :: v1 :: stk))
                            (SBinop b)
                            (Build_stkMachine sav (res :: stk)).

Inductive stkProgEvalR : stkMachine -> stkProgram -> stkMachine -> Prop :=
| StkProgEvalR_nil : forall sm1, stkProgEvalR sm1 nil sm1
| StkProgEvalR_cons :
    forall i p sm1 sm2 sm1',
      stkInstrEvalR sm1 i sm1' ->
      stkProgEvalR sm1' p sm2 ->
      stkProgEvalR sm1 (i :: p) sm2.

(* Basic stack machine properties *)

Theorem args_constant_instr :
  forall i sm1 sm2, stkInstrEvalR sm1 i sm2 -> smArgMap sm1 = smArgMap sm2.
Proof.
  intros; inversion H; unfold smArgMap; reflexivity.
Qed.

Theorem args_constant_program :
  forall p sm1 sm2, stkProgEvalR sm1 p sm2 -> smArgMap sm1 = smArgMap sm2.
Proof.
  induction p.

  intros. inversion H. reflexivity.

  intros. inversion H.

  pose proof args_constant_instr.
  specialize (H6 a sm1 sm1').
  apply H6 in H3.

  specialize (IHp sm1' sm2).
  apply IHp in H5. congruence.
Qed.

Theorem stkProgram_cons :
  forall i p sm1 sm2 sm1',
    stkInstrEvalR sm1 i sm1' ->
    stkProgEvalR sm1' p sm2 ->
    stkProgEvalR sm1 (i :: p) sm2.
Proof.
  intros; inversion H0; eapply StkProgEvalR_cons; eauto.
  congruence. congruence.
Qed.

Theorem stkProgram_concat :
  forall p1 p2 sm1 sm2 sm1',
    stkProgEvalR sm1 p1 sm1' ->
    stkProgEvalR sm1' p2 sm2 ->
    stkProgEvalR sm1 (p1 ++ p2) sm2.
Proof.
  induction p1.

  intros. simpl.
  inversion H. assumption.

  intros.
  rewrite <- app_comm_cons.
  inversion H.
  eapply StkProgEvalR_cons. eauto.
  eauto.
Qed.

Theorem stkProgram_uncons :
  forall i p sm1 sm2,
    stkProgEvalR sm1 (i :: p) sm2 ->
    exists sm1', stkInstrEvalR sm1 i sm1' /\ stkProgEvalR sm1' p sm2.
Proof.
  intros;
  inversion H; eapply ex_intro;
  split; solve [apply H3 | apply H5].
Qed.

Theorem stkProgram_unconcat :
  forall p1 p2 sm1 sm2,
    stkProgEvalR sm1 (p1 ++ p2) sm2 ->
    (exists sm1', stkProgEvalR sm1 p1 sm1' /\ stkProgEvalR sm1' p2 sm2).
Proof.
  induction p1.

  intros. simpl in H.
  eapply ex_intro. split. apply StkProgEvalR_nil. assumption.

  (* Inductive step *)
  intros.

  rewrite <- app_comm_cons in H.

  inversion H.
  apply IHp1 in H5. inversion H5. inversion H6.
  clear H6. clear H5.

  eapply ex_intro.

  split.

  apply (StkProgEvalR_cons a p1 sm1 x sm1'); assumption.
  assumption.
Qed.

Lemma stkProgram_cons_nil :
  forall i sm1 sm2,
    stkInstrEvalR sm1 i sm2 ->
    stkProgEvalR sm1 (i :: nil) sm2.
Proof.
  intros; apply (StkProgEvalR_cons i nil sm1 sm2 sm2); 
  first [assumption | apply StkProgEvalR_nil].
Qed.

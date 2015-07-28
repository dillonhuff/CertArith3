Require Import ZArith.
Require Import List.

(* Arithmetic expressions with variables *)

Definition aArg := nat.

Definition mkAArg n : aArg := n.
Definition aArgName (a : aArg) := a.

Inductive aBop : Set :=
| AAdd : aBop
| ASub : aBop
| AMul : aBop.

Inductive aExp : Set :=
| ArgExp : aArg -> aExp
| ABinop : aBop -> aExp -> aExp -> aExp.

Definition aMap := aArg -> Z.

Open Scope Z_scope.

Fixpoint aExpEval (e : aExp) (m : aMap) : Z :=
  match e with
    | ArgExp a => m a
    | ABinop AAdd l r =>
      (aExpEval l m) + (aExpEval r m)
    | ABinop ASub l r =>
      (aExpEval l m) - (aExpEval r m)
    | ABinop AMul l r =>
      (aExpEval l m) * (aExpEval r m)
  end.

(* Stack machine definition *)

Definition stkArg : Set := nat.

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
  intros.
  inversion H0.
  apply (StkProgEvalR_cons i nil sm1 sm2 sm1').

  assumption.
  congruence.

  apply (StkProgEvalR_cons i (i0 :: p0) sm1 sm2 sm1').

  assumption.
  congruence.
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
  apply (StkProgEvalR_cons a (p1 ++ p2) sm1 sm2 sm1'0).

  assumption.

  specialize (IHp1 p2 sm1'0 sm2 sm1').
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
  eapply ex_intro. split.

  apply (StkProgEvalR_nil sm1).

  assumption.

  (* Inductive step *)
  intros.

  rewrite <- app_comm_cons in H.

  inversion H.
  specialize (IHp1 p2 sm1' sm2).
  apply IHp1 in H5. inversion H5. inversion H6.
  clear H6. clear H5.

  eapply ex_intro.

  split.

  apply (StkProgEvalR_cons a p1 sm1 x sm1'). assumption.

  assumption.

  assumption.
Qed.

(* Compilation of aExps to stackPrograms *)

Definition initStkArgMap (m : aMap) : stkArg -> Z :=
  fun x => m (mkAArg x).

Definition initStackMachine (a : aMap) : stkMachine :=
  Build_stkMachine (initStkArgMap a) nil.

Definition aBopToSBop (b : aBop) : sBop :=
  match b with
    | AAdd => SAdd
    | ASub => SSub
    | AMul => SMul
  end.

Fixpoint aExpToStackProgram (a : aExp) : stkProgram :=
  match a with
    | ArgExp arg => Push (aArgName arg) :: nil
    | ABinop b l r =>
      (aExpToStackProgram l) ++ (aExpToStackProgram r) ++ (SBinop (aBopToSBop b) :: nil)
  end.

Eval compute in aExpToStackProgram (ArgExp (mkAArg 23%nat)).
Eval compute in
    aExpToStackProgram (ABinop AAdd (ArgExp (mkAArg 23%nat)) (ArgExp (mkAArg 76%nat))).

(* Correctness of the translation *)

Lemma aExpBinop_correct :
  forall b e1 e2 m stk,
    stkInstrEvalR
      (Build_stkMachine (initStkArgMap m)
                        ((aExpEval e1 m) :: (aExpEval e2 m) :: stk))
      (SBinop (aBopToSBop b))
      (Build_stkMachine (initStkArgMap m) ((aExpEval (ABinop b e2 e1) m :: stk))).
Proof.
  intros;
  simpl aExpEval; destruct b; apply StkInstrEval_SBinop;
  simpl aBopToSBop; auto using sBopEvalR_add, sBopEvalR_sub, sBopEvalR_mul.
Qed.

Lemma stkProgram_cons_nil :
  forall i sm1 sm2,
    stkInstrEvalR sm1 i sm2 ->
    stkProgEvalR sm1 (i :: nil) sm2.
Proof.
  intros.
  apply (StkProgEvalR_cons i nil sm1 sm2 sm2).
  
  assumption.

  apply StkProgEvalR_nil.
Qed.

Theorem aExpToStackProgram_top_is_correct :
  forall e m stk,
    stkProgEvalR
      (Build_stkMachine (initStkArgMap m) stk)
      (aExpToStackProgram e)
      (Build_stkMachine (initStkArgMap m) ((aExpEval e m) :: stk)).
Proof.
  induction e.

  (* Base case *)
  intros; unfold aExpToStackProgram;
  eauto using StkProgEvalR_cons, StkProgEvalR_nil, StkInstrEvalR_Push.

  (* Inductive step *)
  intros. unfold aExpToStackProgram. fold aExpToStackProgram.
  
  specialize (IHe1 m stk).
  specialize (IHe2 m ((aExpEval e1 m) :: stk)).

  pose proof stkProgram_concat.
  specialize (H (aExpToStackProgram e1) (aExpToStackProgram e2)
                (Build_stkMachine (initStkArgMap m) stk)
                (Build_stkMachine (initStkArgMap m)
                                    ((aExpEval e2 m) :: (aExpEval e1 m) :: stk))
                (Build_stkMachine (initStkArgMap m)
                                    ((aExpEval e1 m) :: stk))).
  apply H in IHe1.
  clear H.

  (* Handle binop *)
  pose proof aExpBinop_correct.
  specialize (H a e2 e1 m stk).

  pose proof stkProgram_cons_nil.
  specialize (H0 (SBinop (aBopToSBop a))
                 (Build_stkMachine
                    (initStkArgMap m) ((aExpEval e2 m) :: (aExpEval e1 m) :: stk))
                 (Build_stkMachine
                    (initStkArgMap m) ((aExpEval (ABinop a e1 e2) m) :: stk))).
  apply H0 in H.
  clear H0.
  
  pose proof stkProgram_concat.

  specialize (H0 (aExpToStackProgram e1 ++ aExpToStackProgram e2)
                 (SBinop (aBopToSBop a) :: nil)
                 (Build_stkMachine (initStkArgMap m) stk)
                 (Build_stkMachine
                    (initStkArgMap m)
                    (aExpEval (ABinop a e1 e2) m :: stk))
                 (Build_stkMachine
                    (initStkArgMap m)
                    (aExpEval e2 m :: aExpEval e1 m :: stk))).
  apply H0 in IHe1.

  rewrite <- app_assoc in IHe1.
  assumption.

  assumption.

  assumption.
Qed.

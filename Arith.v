Require Import ZArith.
Require Import List.

Require Import StkMachine.
Require Import X86.

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
  specialize (IHe2 m (aExpEval e1 m :: stk)).

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
                    (initStkArgMap m) (aExpEval e2 m :: aExpEval e1 m :: stk))
                 (Build_stkMachine
                    (initStkArgMap m) (aExpEval (ABinop a e1 e2) m :: stk))).
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
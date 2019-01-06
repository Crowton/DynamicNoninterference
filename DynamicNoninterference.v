Set Implicit Arguments.

Require Export Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.ZArith.Int.
Import Z_as_Int.

Require Import Omega.

Require Export Datatypes.

(* Strong induction 
   Taken from the strong induction library *)
Lemma le_S :
  forall n m : nat,
    n <= S m -> n <= m \/ n = S m.
Proof.
  intros.
  inversion H.
  right. reflexivity.
  left. assumption.
Qed.

Theorem strongind_aux : forall P: nat -> Prop,
  P 0 ->
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n, (forall m, ((m <= n) -> P m)).
Proof.
  induction n as [ | n' IHn' ].
    intros m H1.
    inversion H1.
    assumption.
    intros.
    assert (m <= n' \/ m = S n'). apply le_S. assumption.
    inversion H2.
    apply IHn'; assumption.
    rewrite H3.
    apply (H0 n'); assumption.
Qed.

Lemma weaken : forall P : nat -> Prop,
  (forall n, (forall m, ((m <= n) -> P m))) -> (forall n, P n).
Proof.
  intros P H n.
  apply (H n n).
  apply le_n.
Qed.

Theorem strongind : forall P : nat -> Prop,
  P 0 ->
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n, P n.
Proof.
  intros.
  apply weaken.
  apply strongind_aux; assumption.
Qed.



(* Setup *)
(* The levels used - Public and Secret for now *)
Inductive level : Set :=
  | Public : level
  | Secret : level.

(* The expressions *)
Inductive exp : Type :=
  | ENum : nat -> exp
  | EId : string -> exp
  | EPlus : exp -> exp -> exp.

(* The command types *)
Inductive cmd : Type :=
  | CStop : cmd
  | CSkip : cmd
  | CAss  : string  -> exp -> cmd
  | CSeq  : cmd -> cmd -> cmd
  | CIf   : exp -> cmd -> cmd -> cmd
  | CJoin : cmd
  | CWhile: exp -> cmd -> cmd.

Notation "'STOP'" := CStop.
Notation "'SKIP'" := CSkip.
Notation "x '::=' a" :=(CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'JOIN'" := CJoin.

(* The state is the memory of the steps
   This is build as nested functions from strings to a tuple
   of the value and level associated with that string *)
Definition state := string -> nat * level.
Definition st_empty: state := fun _ => (0 , Public).
Definition st_update (st: state) (x: string) (v: nat) (l: level) :=
  fun x' => if string_dec x x' then (v, l) else st x'.

(* The definition that two memories agree on public variables *)
Definition memory_agree (m1 m2: state) : Prop :=
  forall x v, m1(x) = (v, Public) <-> m2(x) = (v, Public).
Notation "m1 '~~' m2" := (memory_agree m1 m2) (at level 42).

(* The semantics for the expressions *)
Inductive eval : exp -> state -> nat -> level -> Prop :=
   | eval_const : forall n st,
        eval (ENum n) st n Public
   | eval_id: forall x st u l,
        st x = (u, l) ->
        eval (EId x) st u l
   | eval_plus_public : forall e1 e2 st u v z l1 l2,
        eval e1 st u l1 ->
        eval e2 st v l2 ->
        z = u + v ->
        l1 = Public ->
        l2 = Public ->
        eval (EPlus e1 e2) st z Public
  | eval_plus_secret : forall e1 e2 st u v z l1 l2,
        eval e1 st u l1 ->
        eval e2 st v l2 ->
        z = u + v ->
        (l1 = Secret \/ l2 = Secret) ->
        eval (EPlus e1 e2) st z Secret.

(* A tuple containing a command, a state and a list of levels *)
Inductive config : Type :=
   | Config
       ( c : cmd)
       ( st: state)
       ( lv: list level).
Notation "'〈' c ',' st ',' lv '〉'" := (Config c st lv) (at level 0).

(* Basic definitions for finding the stacklevel and level of strings
   Used in the semantics of the step *)
Definition levelof (st: state) (x: string) : level :=
match st x with
| (_, l) => l
end.

Definition joinLevels (l1 l2: level): level :=
match (l1, l2) with
| (Public, Public) => Public
| _ => Secret
end.

Fixpoint stacklevel (lv: list level) : level :=
match lv with
| [] => Public
| l :: tail => joinLevels l (stacklevel tail)
end.

(* The semantics of the step relation
   Note that the dynamic check is build into these
   This is especially seen in the 'step_assign' rule
   In the IF and JOIN semantics the level of the enviroment is handled,
   so that the assign can check this *)
Reserved Notation "cfg '⇒' cfg'" (at level 40).
Inductive step : config -> config -> Prop :=
  | step_skip : forall st lv,
      〈 SKIP, st, lv 〉 ⇒ 〈 STOP, st, lv 〉
  | step_assign: forall x e v v' st st' lv l,
       eval e st v l ->
       st x = (v', l) ->
       l <> Public \/ stacklevel lv = Public ->
       st' = st_update st x v l ->
      〈 x ::= e, st, lv 〉 ⇒  〈 STOP, st', lv〉
  | step_seq1 : forall c1 c2 st st' lv lv',
      〈 c1, st, lv 〉⇒ 〈 STOP, st', lv' 〉->
      〈 c1 ;; c2, st, lv 〉⇒ 〈 c2, st', lv' 〉
  | step_seq2 : forall c1 c1' c2 st st' lv lv',
      〈 c1, st, lv 〉⇒ 〈 c1', st', lv' 〉->
      c1' <> STOP ->
      〈 c1 ;; c2, st, lv 〉⇒ 〈 c1' ;; c2, st', lv' 〉
  | step_if1 : forall e u c1 c2 st lv l,
       eval e st u l -> u <> 0 ->
      〈 IFB e THEN c1 ELSE c2 FI, st, lv 〉⇒〈 c1 ;; JOIN, st, l::lv 〉
  | step_if2 : forall e c1 c2 st lv l,
       eval e st 0 l ->
      〈 IFB e THEN c1 ELSE c2 FI, st, lv 〉⇒〈 c2 ;; JOIN, st, l::lv 〉
  | step_join: forall st lv l,
      〈 JOIN, st, l::lv 〉 ⇒ 〈 STOP, st, lv 〉
  | step_while : forall e c st lv,
      〈 WHILE e DO c END, st, lv 〉⇒
          〈 IFB e THEN c ;; WHILE e DO c END ELSE SKIP FI, st, lv 〉
where "cfg '⇒' cfg' " := (step cfg cfg').


(* Inductive types used in the definition of well formedness *)
Inductive join_free: cmd -> Prop :=
  | jf_skip : 
    join_free SKIP
  | jf_stop :
    join_free STOP
  | jf_assign : forall x e,
    join_free (x ::= e)
  | jf_seq : forall c1 c2,
    join_free c1 ->
    join_free c2 ->
    join_free (c1 ;; c2)
  | jf_if : forall e c1 c2,
    join_free c1 ->
    join_free c2 ->
    join_free (IFB e THEN c1 ELSE c2 FI)
  | jf_while : forall e c,
    join_free c ->
    join_free (WHILE e DO c END).

Inductive is_not_seq: cmd -> Prop :=
  | skip_not_seq : 
    is_not_seq SKIP
  | stop_not_seq :
    is_not_seq STOP
  | assign_not_seq : forall x e,
    is_not_seq (x ::= e)
  | if_not_seq : forall e c1 c2,
    is_not_seq (IFB e THEN c1 ELSE c2 FI)
  | while_not_seq : forall e c,
    is_not_seq (WHILE e DO c END)
  | join_not_seq :
    is_not_seq JOIN.

Inductive stop_free: cmd -> Prop :=
  | skip_stop_free : 
    stop_free SKIP
  | assign_stop_free : forall x e,
    stop_free (x ::= e)
  | seq_stop_free : forall c1 c2,
    stop_free c1 ->
    stop_free c2 ->
    stop_free (c1 ;; c2)
  | if_stop_free : forall e c1 c2,
    stop_free c1 ->
    stop_free c2 ->
    stop_free (IFB e THEN c1 ELSE c2 FI)
  | while_stop_free : forall e c,
    stop_free c ->
    stop_free (WHILE e DO c END)
  | join_stop_free :
    stop_free JOIN.

(* The inductive semantics for the well formedness
   Used when the command is not STOP
   The number is the amount of JOIN's in the command
   The well formedness also does not allow any STOP commands
   and JOIN's that are nested in something else that seq *)
Inductive well_formed_stop_free: cmd -> Z -> Prop :=
  | wf_join :
    well_formed_stop_free JOIN 1
  | wf_join_free : forall c,
    is_not_seq c ->
    stop_free c ->
    join_free c ->
    well_formed_stop_free c 0
  | wf_seq : forall c1 c2 k1 k2,
    well_formed_stop_free c1 k1 ->
    well_formed_stop_free c2 k2 ->
    (k1 >= 0)%Z ->
    (k2 >= 0)%Z ->
    well_formed_stop_free (c1 ;; c2) (k1 + k2).

(* The definition of well formedness inclueding that STOP is well formed under 0
   This is as the preservation of well formed does not work without it
   0 is here the number for STOP, as the well formed count the amount of JOIN's *)
Definition well_formed (c: cmd) (k: Z):  Prop :=
  (c = STOP /\ k = 0%Z)
    \/
  (well_formed_stop_free c k).

(* Basic lemmas with properties of the well formedness *)
Lemma well_formed_positive: forall (c: cmd) (n: Z),
  well_formed c n ->
  (n >= 0)%Z.
Proof.
  induction c; intros; auto;
    destruct H as [H_left | H_right];
    try inversion H_left;
    try inversion H_right;
    omega.
Qed.

Lemma well_formed_stop_free_is_stop_free: forall (c: cmd) (k: Z),
  well_formed_stop_free c k -> stop_free c.
Proof.
  intros.
  induction H.
  - constructor.
  - trivial.
  - subst.
    constructor;
    assumption.
Qed.

Lemma well_formed_convertion: forall (c: cmd) (k: Z),
  well_formed_stop_free c k <-> well_formed c k /\ stop_free c.
Proof.
  split; intros.
  - assert (well_formed c k).
    + unfold well_formed.
      right.
      assumption.
    + apply well_formed_stop_free_is_stop_free in H.
      auto.
  - destruct H.
    unfold well_formed in H.
    destruct H.
    + destruct H; subst.
      inversion H0.
    + assumption.
Qed.

(* Ltac used to invert over a hypothesis of well formed
   Used to the remove the invertion saying that the command is STOP
   Converts well_formed to well_formed_stop_free *)
Ltac inversion_wf :=
  match goal with
      | [ Hw : well_formed ?cmd ?k |- _ ] =>
          inversion Hw;
          [ match goal with
          | [H_and : ?cmd = STOP /\ ?k = 0%Z |- _ ] =>
              inversion H_and;
              match goal with
              | [H_stop : ?cmd = STOP |- _ ] =>
                  inversion H_stop
              end
          end |
          match goal with
          | [ H_wf : well_formed_stop_free ?cmd ?k |- _ ] =>
              inversion H_wf
          end ]
      end.

(* Same as above, but with a specific 'k' for when there
   are more than one well_formed hypothesis *)
Ltac inversion_wf_k k :=
  match goal with
      | [ Hw : well_formed ?cmd k |- _ ] =>
          inversion Hw;
          [ match goal with
          | [H_and : ?cmd = STOP /\ k = 0%Z |- _ ] =>
              inversion H_and;
              match goal with
              | [H_stop : ?cmd = STOP |- _ ] =>
                  inversion H_stop
              end
          end |
          match goal with
          | [ H_wf : well_formed_stop_free ?cmd k |- _ ] =>
              inversion H_wf
          end ]
      end.


(* Lemma saying that if a command is stop and join free, then it must always be well_formed under 0
   Used in combination with the lemma below, to prove that the given number must be 0 *)
Lemma join_free_wf: forall (c: cmd),
  stop_free c ->
  join_free c ->
  well_formed c 0.
Proof.
  intro c.
  intro H_c_stop_free.
  intro H_c_join_free.
  induction c; intros;
    repeat match goal with
    | [ _: context [join_free STOP] |- _ ] =>
      unfold well_formed;
        left;
        auto
    | [ _: context [join_free SKIP] |- _ ] =>
      unfold well_formed;
        right;
        repeat constructor
    | [ _: context [join_free (?x ::= ?e)] |- _ ] =>
      unfold well_formed;
        right;
        repeat constructor
    end.
  
  - unfold well_formed.
    right.
    assert (0 + 0 = 0)%Z as H_zero by omega.
    rewrite <- H_zero.
    apply wf_seq.
    + inversion H_c_stop_free.
      inversion H_c_join_free.
      apply well_formed_convertion.
      split.
      * apply IHc1; repeat assumption.
      * assumption.
    + inversion H_c_stop_free.
      inversion H_c_join_free.
      apply well_formed_convertion.
      split.
      * apply IHc2; repeat assumption.
      * assumption.
    + omega.
    + omega.

  - unfold well_formed.
    right.
    constructor;
    try apply if_not_seq;
    try assumption.

  - unfold well_formed.
    right.
    inversion H_c_join_free.

  - unfold well_formed.
    right.
    constructor;
    try apply while_not_seq;
    try assumption.
Qed.

(* Lemma stating the the number in the well formedness is deterministic *)
Lemma wf_det: forall (c: cmd) (n m: Z),
  well_formed c n ->
  well_formed c m ->
  n = m.
Proof.
  induction c; intros.
  - inversion H.
    inversion H0.
    + assert (n = 0%Z) by (apply H1).
      assert (m = 0%Z) by (apply H2).
      omega.
    + inversion H2.
      inversion H4.
    + inversion H1.
      inversion H3.

  - inversion_wf_k n.
    inversion_wf_k m.
    trivial.

  - inversion_wf_k n.
    inversion_wf_k m.
    trivial.

  - inversion_wf_k n.
    inversion H2.

    inversion_wf_k m.
    inversion H10.

    subst.

    assert (k1 = k0).
    + apply IHc1.
      * unfold well_formed.
        right.
        assumption.
      * unfold well_formed.
        right.
        assumption.
    + subst.
      assert (k2 = k3).
      * apply IHc2.
        -- unfold well_formed.
           right.
           assumption.
        -- unfold well_formed.
           right.
           assumption.
      * subst.
        trivial.

  - inversion_wf_k n.
    inversion_wf_k m.
    trivial.

  - inversion_wf_k n.
    inversion_wf_k m.
    trivial.
    inversion H6.
    inversion H4.

  - inversion_wf_k n.
    inversion_wf_k m.
    trivial.
Qed.


(* Fixpoint for finding the length of the list of levels in the config *)
Fixpoint stack_size (lv: list level) : Z :=
match lv with
| [] => 0
| _ :: tail => 1 + (stack_size tail)
end.
Notation "'|' lv '|'" := (stack_size lv) (at level 42).

(* Lemma to extrack a one from the stack size *)
Lemma stack_size_one: forall (l: level) (lv: list level),
  |l :: lv| = (1%Z + |lv|)%Z.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

(* Basic omega lemma to get a plus into the well formedness
   Used for invertion of seq well formed, as that requires two numbers *)
Lemma add_paren: forall (a b c: Z),
  (a + b - c)%Z = (a + (b - c))%Z.
Proof.
  intros.
  omega.
Qed.


(* Lemma proofing the preservation of the well formedness when a command takes a step
   Here the well formedness is descriping the amount of joins in the command
   This is compared to the before stack, to see that they match
   In the seq case, the first command takes a step, using the stack of the whole
   configuration. However the JOINS might be in the second command, so we subtract some number
   'k' denoting this error.
   Here the important fact is that this is the same 'k' before and after the step. *)
Lemma preservation_of_well_formedness: forall (c c': cmd) (st st': state) (lv lv': list level) (n: Z),
  well_formed c (|lv| - n) ->
 〈 c, st, lv 〉⇒〈 c', st', lv' 〉->
  well_formed c' (|lv'| - n).
Proof.
  induction c.
  + intros.
    inversion H0.
  + intros.
    inversion H0.
    subst.
    left.
    split.
    - trivial.
    - inversion_wf.
      trivial.
  + intros.
    inversion H0.
    subst.
    left.
    split.
    - trivial.
    - inversion_wf.
      trivial.
  + intros.
    inversion H0.
    subst.
    - inversion_wf.
      inversion H4.
      subst.
      assert (k2 = (|lv'| - n)%Z).
      * assert (well_formed STOP (|lv'| - (n + k2))).
        -- apply IHc1 with st st' lv.
           ++ assert (k1 = (|lv| - (n + k2))%Z) by omega.
              rewrite <- H3.
              right.
              assumption.
           ++ assumption.
        -- assert ((| lv' | - (n + k2))%Z = 0%Z).
           ++ inversion H3.
              ** apply H4.
              ** inversion H4.
                 inversion H12.
          ++ omega.
      * rewrite <- H3.
        right.
        assumption.
    - subst.
      inversion_wf.
      inversion H4.
      subst.
      assert (well_formed c1' ((| lv' | - n - k2)%Z)).
      * assert ((|lv'| - (n + k2))%Z = (|lv'| - n - k2)%Z) by omega.
        rewrite <- H2.
        apply IHc1 with st st' lv.
        -- assert ((| lv | - (n + k2))%Z = k1) as H_eq by omega.
           rewrite -> H_eq.
           right.
           assumption.
        -- assumption.
      * assert ((| lv' | - n)%Z = ((| lv' | - n - k2) + k2)%Z) by omega.
        rewrite -> H4.
        right.
        apply wf_seq.
        -- inversion H2.
           inversion H11.
           contradiction.
           assumption.
        -- assumption.
        -- apply well_formed_positive with c1'.
           assumption.
        -- assumption.
  + intros.
    inversion H0.
    subst.
    - inversion_wf.
      inversion H5.
      inversion H7.
      subst.
      pose (size := wf_det H (join_free_wf (if_stop_free e H11 H13) (jf_if e H16 H18))).
      assert ((| l :: lv | - n)%Z = (0 + 1)%Z).
      * rewrite -> stack_size_one.
        rewrite -> add_paren.
        rewrite -> size.
        simpl.
        reflexivity.
      * rewrite -> H6.
        right.
        apply wf_seq.
        -- apply well_formed_convertion.
           split.
           apply join_free_wf.
           assumption.
           assumption.
           assumption.
        -- apply wf_join.
        -- omega.
        -- omega.
    - inversion_wf.
      inversion H13.
      inversion H15.
      subst.
      pose (size := wf_det H (join_free_wf (if_stop_free e H18 H20) (jf_if e H23 H25))).
      assert ((| l :: lv | - n)%Z = (0 + 1)%Z).
      * rewrite -> stack_size_one.
        rewrite -> add_paren.
        rewrite -> size.
        simpl.
        reflexivity.
      * rewrite -> H1.
        right.
        apply wf_seq.
        -- apply well_formed_convertion.
           split.
           apply join_free_wf.
           assumption.
           assumption.
           assumption.
        -- apply wf_join.
        -- omega.
        -- omega.
  + intros.
    left.
    inversion H0.
    subst.
    split.
    - trivial.
    - assert (well_formed JOIN 1).
      * right.
        constructor.
      * assert ((| l :: lv' | - n)%Z = 1%Z).
        -- apply wf_det with JOIN;
           repeat assumption.
        -- rewrite -> stack_size_one in H2.
           omega.
  + intros.
    inversion_wf.
    inversion H0.
    subst.
    rewrite <- H2.
    apply join_free_wf.
    apply if_stop_free.
    apply seq_stop_free.
    inversion H4.
    assumption.
    assumption.
    apply skip_stop_free.
    apply jf_if.
    - apply jf_seq.
      * inversion H6.
        assumption.
      * assumption.
    - apply jf_skip.
Qed.





(* Semantics for events *)
Inductive event :=
  | EmptyEvent : event
  | AssignmentEvent : string -> nat -> event.

(* Augmented step semantics containing the event that the given step made *)
Inductive event_step : config -> event -> config -> Prop :=
  (* Assignments *)
  | event_step_assign_public: forall x e v v' st st' lv l,
       eval e st v l ->
       st x = (v', l) ->
       l = Public /\ stacklevel lv = Public ->
       st' = st_update st x v l ->
       event_step〈 x ::= e, st, lv 〉(AssignmentEvent x v)〈 STOP, st', lv〉
  | event_step_assign_secret: forall x e v v' st st' lv l,
       eval e st v l ->
       st x = (v', l) ->
       l <> Public ->
       st' = st_update st x v l ->
       event_step〈 x ::= e, st, lv 〉EmptyEvent〈 STOP, st', lv〉

  (* Sequential *)
  | event_step_seq1 : forall c1 c2 st st' lv lv' ev,
       event_step 〈 c1, st, lv 〉ev 〈 STOP, st', lv' 〉->
       event_step 〈 c1 ;; c2, st, lv 〉ev 〈 c2, st', lv' 〉
  | event_step_seq2 : forall c1 c1' c2 st st' lv lv' ev,
       event_step 〈 c1, st, lv 〉ev 〈 c1', st', lv' 〉->
       c1' <> STOP ->
       event_step 〈 c1 ;; c2, st, lv 〉ev 〈 c1' ;; c2, st', lv' 〉

  (* Trivial cases *)
  | event_step_skip : forall st lv,
       event_step〈 SKIP, st, lv 〉EmptyEvent〈 STOP, st, lv 〉
  | event_step_if1 : forall e u c1 c2 st lv l,
       eval e st u l -> u <> 0 ->
       event_step〈 IFB e THEN c1 ELSE c2 FI, st, lv 〉EmptyEvent〈 c1 ;; JOIN, st, l::lv 〉
  | event_step_if2 : forall e c1 c2 st lv l,
       eval e st 0 l ->
       event_step〈 IFB e THEN c1 ELSE c2 FI, st, lv 〉EmptyEvent〈 c2 ;; JOIN, st, l::lv 〉
  | event_step_join: forall st lv l,
       event_step〈 JOIN, st, l::lv 〉EmptyEvent〈 STOP, st, lv 〉
  | event_step_while : forall e c st lv,
       event_step〈 WHILE e DO c END, st, lv 〉EmptyEvent
          〈 IFB e THEN c ;; WHILE e DO c END ELSE SKIP FI, st, lv 〉.

(* Lemma allowing for conversion between the regular and augmented semantics *)
Lemma same_semantics : forall (c1 c2: config),
  c1 ⇒ c2 <-> exists ev, event_step c1 ev c2.
Proof.
  split.
  - intro.
    induction H.
    + exists EmptyEvent.
      constructor.
    + destruct l.
      * inversion H1.
        contradiction.
        exists (AssignmentEvent x v).
        apply event_step_assign_public with v' Public.
        assumption.
        assumption.
        split.
        trivial.
        assumption.
        assumption.
      * exists EmptyEvent.
        apply event_step_assign_secret with v v' Secret.
        assumption.
        assumption.
        unfold not.
        intros.
        inversion H3.
        assumption.
    + inversion IHstep.
      exists x.
      constructor.
      assumption.
    + inversion IHstep.
      exists x.
      constructor.
      assumption.
      assumption.
    + exists EmptyEvent.
      apply event_step_if1 with u.
      assumption.
      assumption.
    + exists EmptyEvent.
      apply event_step_if2.
      assumption.
    + exists EmptyEvent.
      constructor.
    + exists EmptyEvent.
      constructor.
  - intro.
    inversion H.
    induction H0.
    + apply step_assign with v v' l.
      assumption.
      assumption.
      right.
      inversion H2.
      assumption.
      assumption.
    + apply step_assign with v v' l.
      assumption.
      assumption.
      left.
      assumption.
      assumption.
    + constructor.
      apply IHevent_step.
      exists ev.
      assumption.
    + constructor.
      * apply IHevent_step.
        exists ev.
        assumption.
      * assumption.
    + constructor.
    + apply step_if1 with u.
      assumption.
      assumption.
    + apply step_if2.
      assumption.
    + constructor.
    + constructor.
Qed.

(* Lemma showing that the augmented semantics also preserve the well formedness *)
Lemma preservation_of_well_formedness_for_event_step: forall (c c': cmd) (st st': state) (lv lv': list level)
                                                             (n: Z) (ev: event),
  well_formed c (|lv| - n) ->
  event_step 〈 c, st, lv 〉ev〈 c', st', lv' 〉->
  well_formed c' (|lv'| - n).
Proof.
(* Directly from lemma 1 and 2 *)
  intros.
  apply preservation_of_well_formedness with c st st' lv.
  assumption.
  apply same_semantics.
  exists ev.
  assumption.
Qed.


(* Semantics for bridge
   Used to 'run' the command until something of interest happens
   This is when there was an public assignment (as this is the only
   thing that can change the memory agreeing)
   or the command terminates (becomes STOP) *)
Inductive bridge : config -> event -> nat -> config -> Prop :=
  | bridge_stop: forall c st st' lv lv',
       event_step 〈 c, st, lv 〉EmptyEvent 〈 STOP, st', lv' 〉->
       bridge 〈 c, st, lv 〉EmptyEvent 0 〈 STOP, st', lv' 〉
  | bridge_public: forall c c' x v st st' lv lv',
       event_step 〈 c, st, lv 〉(AssignmentEvent x v)〈 c', st', lv' 〉->
       bridge 〈 c, st, lv 〉(AssignmentEvent x v) 0 〈 c', st', lv' 〉
  | bridge_multi: forall c c' c'' st st' st'' lv lv' lv'' ev n,
       event_step 〈 c, st, lv 〉EmptyEvent〈 c', st', lv' 〉->
       c' <> STOP ->
       bridge 〈 c', st', lv' 〉ev n 〈 c'', st'', lv'' 〉 ->
       bridge 〈 c, st, lv 〉ev (n+1) 〈 c'', st'', lv'' 〉.


(* Lemma stating that bridging over seq must first execute the first command to STOP
   and then the second command. Here either the first command produces the event,
   or it terminates silently, and then the second command fire the event *)
Lemma bridge_seq: forall (n: nat) (c1 c2 c': cmd) (n': Z) (st st': state) (lv lv': list level) (ev: event),
  well_formed (c1 ;; c2) (|lv| - n')%Z ->
  bridge 〈 c1 ;; c2, st, lv 〉 ev n 〈 c', st', lv' 〉 ->
  (* (2) *) (exists c1', ev <> EmptyEvent /\
              bridge 〈 c1, st, lv 〉 ev n 〈 c1', st', lv' 〉 /\
              (c1' <> STOP -> c' = (c1' ;; c2)) /\
              (c1' =  STOP  -> c' = c2))
          \/
  (* (1) *) (exists k' st1' lv1', n > 0 /\ k' < n /\
              bridge 〈 c1, st, lv 〉 EmptyEvent k' 〈 STOP, st1', lv1' 〉 /\
              bridge 〈 c2, st1', lv1' 〉 ev (n-k'-1) 〈 c', st', lv' 〉).
Proof.
  intros n.
  induction n.
  - left.
    inversion_wf.
    inversion H3.
    subst.
    inversion H0; subst.
    + inversion H11.
      subst.
      inversion H6.
      inversion H3.
    + inversion H11;
      subst.
      * exists STOP.
        repeat split.
        -- discriminate.
        -- apply bridge_public.
           assumption.
        -- intros.
           contradiction.
      * exists c1'.
        repeat split.
        -- discriminate.
        -- apply bridge_public.
           assumption.
        -- intros.
           subst.
           contradiction.
    + omega.
  - intros.
    inversion H0.
    subst.
    inversion H7;
    subst.
    + right.
      exists 0.
      exists st'0.
      exists lv'0.
      repeat (split; try omega).
      * constructor.
        assumption.
      * subst.
        assert (n0 = n0 + 1 - 0 - 1) as Hnum by omega.
        rewrite <- Hnum.
        assumption.
    + assert (n0 = n) by omega.
      clear H4.
      subst.
      specialize (IHn c1' c2 c' n' st'0 st' lv'0 lv' ev).
      subst.
      destruct IHn.
      * apply preservation_of_well_formedness_for_event_step with (c1;;c2) st st'0 lv EmptyEvent;
        repeat assumption.
      * assumption.
      * left.
        destruct H1.
        destruct H1.
        destruct H2.
        destruct H3.
        exists x.
        repeat split.
        -- assumption.
        -- apply bridge_multi with c1' st'0 lv'0;
           assumption.
        -- assumption.
        -- assumption.
      * right.
        destruct H1.
        destruct H1.
        destruct H1.
        destruct H1.
        destruct H2.
        destruct H3.
        exists (x + 1).
        exists x0.
        exists x1.
        repeat split.
        -- omega.
        -- omega.
        -- apply bridge_multi with c1' st'0 lv'0;
           assumption.
        -- assert ((n + 1 - (x + 1) - 1) = (n - x - 1)) as Hnum by omega.
           rewrite Hnum.
           assumption.
Qed.


(* Tons of helping lemmas for the master bridge theorem *)
(* Memory agree properties *)
Lemma memory_self_agree: forall (st: state),
  st ~~ st.
Proof.
  intros.
  unfold memory_agree.
  intros.
  split.
  - intros.
    assumption.
  - intros.
    assumption.
Qed.

Lemma memory_commutative: forall (st st': state),
  st ~~ st' ->
  st' ~~ st.
Proof.
  intros.
  unfold memory_agree.
  intros.
  unfold memory_agree in H.
  split.
  apply H.
  apply H.
Qed.

Lemma memory_transitivity: forall (st st' st'': state),
  st ~~ st' ->
  st' ~~ st'' ->
  st ~~ st''.
Proof.
  intros.
  unfold memory_agree.
  intros.
  unfold memory_agree in H.
  unfold memory_agree in H0.
  specialize (H x v).
  specialize (H0 x v).
  split.
  - intros.
    apply H0.
    apply H.
    assumption.
  - intros.
    apply H.
    apply H0.
    assumption.
Qed.

Lemma memory_secret_update_agree: forall (st: state) (x: string) (v0 v: nat),
  st x = (v0, Secret) ->
  st ~~ st_update st x v Secret.
Proof.
  intros.
  unfold memory_agree.
  intros.
  split.
  - intros.
    assert (x <> x0).
    + unfold not.
      intros.
      subst.
      rewrite -> H in H0.
      inversion H0.
    + unfold st_update.
      case_eq (string_dec x x0).
      * intros.
        contradiction.
      * intros.
        assumption.
  - intros.
    unfold st_update in H0.
    case_eq (string_dec x x0).
    + intros.
      subst.
      rewrite H1 in H0.
      inversion H0.
    + intros.
      rewrite H1 in H0.
      assumption.
Qed.

(* Secret enviroment and EmptyEvents makes the memory agree *)
Lemma secret_branches_does_not_change_the_memory: forall (c c': cmd) (st st': state) (lv lv': list level) (ev: event),
  stacklevel lv = Secret ->
  event_step 〈 c, st, lv 〉 ev 〈 c', st', lv' 〉 ->
  st ~~ st'.
Proof.
  intro c.
  induction c; intros.
  - inversion H0.
  - inversion H0.
    apply memory_self_agree.
  - inversion H0;
    subst.
    + inversion H11.
      rewrite H2 in H.
      inversion H.
    + destruct l.
      * contradiction.
      * apply memory_secret_update_agree with v'.
        assumption.
  - inversion H0;
    subst.
    + apply IHc1 with STOP lv lv' ev;
      assumption.
    + apply IHc1 with c1' lv lv' ev;
      assumption.
  - inversion H0;
    apply memory_self_agree.
  - inversion H0.
    apply memory_self_agree.
  - inversion H0.
    apply memory_self_agree.
Qed.

Lemma secret_assign_same_memory: forall (c c': cmd) (st st': state) (lv lv': list level),
  event_step 〈 c, st, lv 〉 EmptyEvent 〈 c', st', lv' 〉 ->
  st ~~ st'.
Proof.
  intro c.
  induction c;
  intros.
  - inversion H.
  - inversion H.
    apply memory_self_agree.
  - inversion H.
    subst.
    destruct l.
    contradiction.
    unfold memory_agree.
    intros.
    unfold st_update.
    destruct (string_dec s x).
    + split.
      * intros.
        subst.
        rewrite H8 in H0.
        inversion H0.
      * intros.
        inversion H0.
    + split; intros; assumption.
  - inversion H;
    subst.
    + apply IHc1 with STOP lv lv'.
      assumption.
    + apply IHc1 with c1' lv lv'.
      assumption.
  - inversion H;
    apply memory_self_agree.
  - inversion H.
    apply memory_self_agree.
  - inversion H.
    apply memory_self_agree.
Qed.

(* Properties of the eval *)
(* The evaluated public values must be the same *)
Lemma eval_public_agree: forall (e: exp) (st st': state) (v v': nat),
  st ~~ st' ->
  eval e st v Public ->
  eval e st' v' Public ->
  v = v'.
Proof.
  intro e.
  induction e;
  intros.
  - inversion H0.
    inversion H1.
    subst.
    trivial.
  - inversion H0.
    inversion H1.
    subst.
    unfold memory_agree in H.
    specialize (H s v).
    apply H in H3.
    rewrite H3 in H8.
    inversion H8.
    trivial.
  - inversion H0.
    inversion H1.
    subst.
    assert (u = u0).
    apply IHe1 with st st';
    assumption.
    assert (v0 = v1).
    apply IHe2 with st st';
    assumption.
    omega.
Qed.

(* The level a given expression have is deterministic if the memories agree *)
Lemma eval_deterministic_level: forall (e: exp) (st st': state) (v v': nat) (l l': level),
  st ~~ st' ->
  eval e st v l ->
  eval e st' v' l' ->
  l = l'.
Proof.
  intro e.
  induction e;
  intros.
  - inversion H0.
    inversion H1.
    trivial.
  - inversion H0.
    inversion H1.
    subst.
    unfold memory_agree in H.
    destruct l.
    + specialize (H s v).
      destruct H.
      assert (st' s = (v, Public)) by (apply H; assumption).
      rewrite H4 in H8.
      inversion H8.
      trivial.
    + destruct l'.
      * specialize (H s v').
        destruct H.
        assert (st s = (v', Public)) by (apply H2; assumption).
        rewrite H3 in H4.
        inversion H4.
      * trivial.
  - inversion H0;
    inversion H1;
    subst.
    + trivial.
    + specialize (IHe1 st st' u u0 Public l0).
      assert (Public = l0) by (apply IHe1; assumption).
      specialize (IHe2 st st' v0 v1 Public l3).
      assert (Public = l3) by (apply IHe2; assumption).
      destruct H20; subst; discriminate.
    + specialize (IHe1 st st' u u0 l1 Public).
      assert (l1 = Public) by (apply IHe1; assumption).
      specialize (IHe2 st st' v0 v1 l2 Public).
      assert (l2 = Public) by (apply IHe2; assumption).
      destruct H10; subst; discriminate.
    + trivial.
Qed.

(* If the state is the same, then both the level and the value is deterministic *)
Lemma eval_deterministic: forall (e: exp) (st: state) (v v': nat) (l l': level),
  eval e st v l ->
  eval e st v' l' ->
  v = v' /\ l = l'.
Proof.
  intro e.
  induction e;
  intros.
  - inversion H.
    inversion H0.
    subst.
    split;
    trivial.
  - inversion H.
    inversion H0.
    subst.
    rewrite H2 in H7.
    inversion H7.
    split;
    trivial.
  - inversion H;
    inversion H0;
    subst.
    + assert (u = u0 /\ Public = Public) by (apply IHe1 with st; assumption).
      assert (v0 = v1 /\ Public = Public) by (apply IHe2 with st; assumption).
      destruct H1.
      destruct H2.
      subst.
      split;
      trivial.
    + destruct H19;
      subst.
      * assert (u = u0 /\ Public = Secret) by (apply IHe1 with st; assumption).
        destruct H1.
        discriminate.
      * assert (v0 = v1 /\ Public = Secret) by (apply IHe2 with st; assumption).
        destruct H1.
        discriminate.
    + destruct H9;
      subst.
      * assert (u = u0 /\ Secret = Public) by (apply IHe1 with st; assumption).
        destruct H1.
        discriminate.
      * assert (v0 = v1 /\ Secret = Public) by (apply IHe2 with st; assumption).
        destruct H1.
        discriminate.
    + assert (u = u0 /\ l1 = l0) by (apply IHe1 with st; assumption).
      assert (v0 = v1 /\ l2 = l3) by (apply IHe2 with st; assumption).
      destruct H1.
      destruct H2.
      subst.
      split;
      trivial.
Qed.


(* Lemmas used to extract the well formedness of the two branches of a IF command
   This is used in the secret bridge lemma *)
Lemma if_c1_well_formed: forall (e: exp) (c1 c2: cmd) (st: state) (lv: list level) (l: level) (ev: event),
  well_formed (IFB e THEN c1 ELSE c2 FI) 0 ->
  event_step 〈 IFB e THEN c1 ELSE c2 FI, st, lv 〉 ev 〈 c1 ;; JOIN, st, l :: lv 〉 ->
  well_formed c1 0.
Proof.
  intros.
  assert (well_formed (c1 ;; JOIN) (|l :: lv| - |lv|)%Z).
  apply preservation_of_well_formedness_for_event_step with (IFB e THEN c1 ELSE c2 FI) st st lv ev.
  assert ((| lv | - | lv |)%Z = 0%Z) as Hnum by omega.
  rewrite Hnum.
  assumption.
  assumption.
  assert (| l :: lv | = (1 + |lv|)%Z) as Hnum2 by (apply stack_size_one).
  rewrite Hnum2 in H1.
  assert ((1 + | lv | - | lv |)%Z = 1%Z) as Hnum3 by omega.
  rewrite Hnum3 in H1.
  inversion_wf_k 1%Z.
  subst.
  inversion H7.
  subst.
  assert (k1 = 0%Z) by omega.
  subst.
  unfold well_formed.
  right.
  assumption.
  inversion H10.
Qed.

Lemma if_c2_well_formed: forall (e: exp) (c1 c2: cmd) (st: state) (lv: list level) (l: level) (ev: event),
  well_formed (IFB e THEN c1 ELSE c2 FI) 0 ->
  event_step 〈 IFB e THEN c1 ELSE c2 FI, st, lv 〉 ev 〈 c2 ;; JOIN, st, l :: lv 〉 ->
  well_formed c2 0.
Proof.
  intros.
  assert (well_formed (c2 ;; JOIN) (|l :: lv| - |lv|)%Z).
  apply preservation_of_well_formedness_for_event_step with (IFB e THEN c1 ELSE c2 FI) st st lv ev.
  assert ((| lv | - | lv |)%Z = 0%Z) as Hnum by omega.
  rewrite Hnum.
  assumption.
  assumption.
  assert (| l :: lv | = (1 + |lv|)%Z) as Hnum2 by (apply stack_size_one).
  rewrite Hnum2 in H1.
  assert ((1 + | lv | - | lv |)%Z = 1%Z) as Hnum3 by omega.
  rewrite Hnum3 in H1.
  inversion_wf_k 1%Z.
  subst.
  inversion H7.
  subst.
  assert (k1 = 0%Z) by omega.
  subst.
  unfold well_formed.
  right.
  assumption.
  inversion H10.
Qed.

(* Lemma stating that if a command is well formed under 0 (join free)
   and the stacklevel is secret, then it must hold that the bridge does 
   not make any public assignments, keeps the same list level, produces
   the EmptyEvent and terninates to STOP.
   Made using a definition, to apply strong induction *)
Definition secret_joinfree_bridge_makes_no_event_id (n: nat) : Prop :=
  forall (c c': cmd) (st st': state) (lv lv': list level) (ev: event),
    well_formed c 0 ->
    stacklevel lv = Secret ->
    bridge 〈 c, st, lv 〉 ev n 〈 c', st', lv' 〉 ->
    c' = STOP /\ st ~~ st' /\ lv = lv' /\ ev = EmptyEvent.

Lemma secret_joinfree_bridge_makes_no_event: forall (n: nat),
  secret_joinfree_bridge_makes_no_event_id (n).
Proof.
  apply strongind;
  unfold secret_joinfree_bridge_makes_no_event_id;
  induction c;
  intros.
  - inversion H1.
    inversion H6.
    inversion H6.
    omega.
  - inversion H1;
    subst.
    + inversion H6.
      do 3 split; trivial.
    + inversion H6.
    + omega.
  - inversion H1;
    subst.
    + split. trivial.
      split.
      apply secret_assign_same_memory with (s ::= e) STOP lv lv'.
      assumption.
      split.
      inversion H6.
      trivial.
      trivial.
    + inversion H6.
      subst.
      destruct H14.
      rewrite H0 in H3.
      discriminate.
    + omega.
  - inversion H1;
    subst.
    + inversion H6.
      subst.
      inversion_wf.
      inversion H3.
      subst.
      inversion H9.
      inversion H4.
    + apply bridge_seq with 0 c1 c2 c' (|lv|) st st' lv lv' (AssignmentEvent x v) in H1.
      destruct H1.
      * do 2 destruct H1.
        destruct H2.
        assert (x0 = STOP /\ st ~~ st' /\ lv = lv' /\ (AssignmentEvent x v) = EmptyEvent).
        apply IHc1.
        inversion_wf.
        inversion H5.
        rewrite H8.
        assert (k1 = 0%Z) by omega.
        subst.
        unfold well_formed.
        right.
        assumption.
        assumption.
        assumption.
        destruct H4.
        destruct H5.
        destruct H7.
        discriminate.
      * do 4 destruct H1.
        omega.
      * assert ((| lv | - | lv |)%Z = 0%Z) as Hnum by omega.
        rewrite Hnum.
        assumption.
    + omega.
  - inversion H1;
    subst.
    + inversion H6.
    + inversion H6.
    + omega.
  - inversion_wf.
    inversion H5.
  - inversion H1;
    subst.
    + inversion H6.
    + inversion H6.
    + omega.

  (* Induction Case *)
  - inversion H2.
    subst.
    inversion H9.
  - inversion H2.
    subst.
    inversion H9.
    subst.
    contradiction.
  - inversion H2.
    subst.
    inversion H9.
    subst.
    contradiction.
  - apply bridge_seq with (S n) c1 c2 c' (|lv|) st st' lv lv' ev in H2.
    destruct H2.
    + do 2 destruct H2.
      destruct H3.
      assert (x = STOP /\ st ~~ st' /\ lv = lv' /\ ev = EmptyEvent).
      apply IHc1.
      inversion_wf.
      inversion H6.
      rewrite H8.
      assert (k1 = 0%Z) by omega.
      subst.
      unfold well_formed.
      right.
      assumption.
      assumption.
      assumption.
      destruct H5.
      destruct H6.
      destruct H7.
      subst.
      contradiction.
    + do 4 destruct H2.
      destruct H3.
      destruct H4.
      assert (STOP = STOP /\ st ~~ x0 /\ lv = x1 /\ EmptyEvent = EmptyEvent).
      apply H with x c1.
      omega.
      inversion_wf.
      inversion H7.
      rewrite H9.
      assert (k1 = 0%Z) by omega.
      subst.
      unfold well_formed.
      right.
      assumption.
      assumption.
      assumption.
      destruct H6.
      destruct H7.
      destruct H8.
      subst.
      assert (c' = STOP /\ x0 ~~ st' /\ x1 = lv' /\ ev = EmptyEvent).
      apply H with (S n - x - 1) c2.
      omega.
      inversion_wf.
      inversion H10.
      rewrite H12.
      assert (k2 = 0%Z) by omega.
      subst.
      unfold well_formed.
      right.
      assumption.
      assumption.
      assumption.
      destruct H8.
      destruct H10.
      destruct H11.
      split.
      assumption.
      split.
      apply memory_transitivity with x0;
      assumption.
      split;
      assumption.
    + assert ((| lv | - | lv |)%Z = 0%Z) as Hnum by omega.
      rewrite Hnum.
      assumption.
  - inversion H2.
    subst.
    inversion H9;
    subst.
    assert (n = n0) by omega.
    subst.
    + apply bridge_seq with n0 c1 JOIN c' (|lv|) st'0 st' (l :: lv) lv' ev in H13.
      destruct H13.
      * do 2 destruct H3.
        destruct H4.
        assert (x = STOP /\ st'0 ~~ st' /\ (l :: lv) = lv' /\ ev = EmptyEvent).
        apply H with n0 c1.
        omega.
        apply if_c1_well_formed with e c2 st'0 lv l EmptyEvent;
        assumption.
        simpl.
        rewrite H1.
        destruct l; simpl; trivial.
        assumption.
        destruct H8.
        destruct H10.
        destruct H11.
        subst.
        contradiction.
      * do 4 destruct H3.
        destruct H4.
        destruct H7.
        inversion H8;
        subst.
        -- assert (x = (n0 - 1)) by omega.
           subst.
           assert (STOP = STOP /\ st'0 ~~ x0 /\ (l :: lv) = x1 /\ EmptyEvent = EmptyEvent).
           apply H with (n0 - 1) c1.
           omega.
           apply if_c1_well_formed with e c2 st'0 lv l EmptyEvent;
           assumption.
           simpl.
           rewrite H1.
           destruct l; simpl; trivial.
           assumption.
           destruct H10.
           destruct H11.
           destruct H13.
           subst.
           inversion H15.
           subst.
           split.
           trivial.
           split.
           assumption.
           split.
           trivial.
           trivial.
        -- inversion H15.
        -- inversion H18.
           subst.
           contradiction.
      * apply preservation_of_well_formedness_for_event_step with (IFB e THEN c1 ELSE c2 FI) st'0 st'0 lv EmptyEvent.
        -- assert ((| lv | - | lv |)%Z = 0%Z) as Hnum by omega.
           rewrite Hnum.
           assumption.
        -- assumption.
    + apply bridge_seq with n0 c2 JOIN c' (|lv|) st'0 st' (l :: lv) lv' ev in H13.
      destruct H13.
      * do 2 destruct H3.
        destruct H5.
        assert (x = STOP /\ st'0 ~~ st' /\ (l :: lv) = lv' /\ ev = EmptyEvent).
        apply H with n0 c2.
        omega.
        apply if_c2_well_formed with e c1 st'0 lv l EmptyEvent;
        assumption.
        simpl.
        rewrite H1.
        destruct l; simpl; trivial.
        assumption.
        destruct H8.
        destruct H10.
        destruct H11.
        subst.
        contradiction.
      * do 4 destruct H3.
        destruct H5.
        destruct H7.
        inversion H8;
        subst.
        -- assert (x = (n0 - 1)) by omega.
           subst.
           assert (STOP = STOP /\ st'0 ~~ x0 /\ (l :: lv) = x1 /\ EmptyEvent = EmptyEvent).
           apply H with (n0 - 1) c2.
           omega.
           apply if_c2_well_formed with e c1 st'0 lv l EmptyEvent;
           assumption.
           simpl.
           rewrite H1.
           destruct l; simpl; trivial.
           assumption.
           destruct H10.
           destruct H11.
           destruct H13.
           subst.
           inversion H15.
           subst.
           split.
           trivial.
           split.
           assumption.
           split.
           trivial.
           trivial.
        -- inversion H15.
        -- inversion H17.
           subst.
           contradiction.
      * apply preservation_of_well_formedness_for_event_step with (IFB e THEN c1 ELSE c2 FI) st'0 st'0 lv EmptyEvent.
        -- assert ((| lv | - | lv |)%Z = 0%Z) as Hnum by omega.
           rewrite Hnum.
           assumption.
        -- assumption.
  - inversion_wf.
    inversion H6.
  - inversion H2.
    subst.
    inversion H9.
    subst.
    apply H with n0 (IFB e THEN c;; WHILE e DO c END ELSE SKIP FI).
    + omega.
    + assert (0%Z = (|lv'0| - |lv'0|)%Z) as Hnum by omega.
      rewrite Hnum in H0.
      rewrite Hnum.
      apply preservation_of_well_formedness_for_event_step with (WHILE e DO c END) st'0 st'0 lv'0 EmptyEvent;
      assumption.
    + assumption.
    + assert (n0 = n) by omega.
      subst.
      assumption.
Qed.


(* Lemma stating that if the top of the stack is
   Secret then the stacklevel is secret *)
Lemma secret_onstack_makes_level_secret: forall (lv: list level),
  stacklevel (Secret :: lv) = Secret.
Proof.
  intros.
  simpl.
  unfold joinLevels.
  trivial.
Qed.

(* Lemma saying the IF can only be well formed under 0 *)
Lemma if_well_formed_zero: forall (e: exp) (c1 c2: cmd) (lv: list level) (k: Z),
  well_formed (IFB e THEN c1 ELSE c2 FI) (|lv| - k)%Z ->
  well_formed (IFB e THEN c1 ELSE c2 FI) 0.
Proof.
  intros.
  inversion_wf.
  rewrite <- H1 in H.
  assumption.
Qed.


(* Theorem prooving noninterferrence for bridge
   If a command is well formed, and makes two different bridges
   with agreeing memories, then the resulting configuration is the same,
   the ending memories agree, and the stack and events are the same.
   Is made with defintion to apply strong induction *)
Definition bridge_noninterference_id (n: nat) : Prop :=
  forall (c c1' c2': cmd) (n2: nat) (st1 st1' st2 st2': state)
         (lv lv1' lv2': list level) (k: Z) (ev1 ev2: event),
  well_formed c (|lv| - k) ->
  bridge 〈 c, st1, lv 〉 ev1 n 〈 c1', st1', lv1' 〉 ->
  bridge 〈 c, st2, lv 〉 ev2 n2 〈 c2', st2', lv2' 〉 ->
  st1 ~~ st2 ->
  (c1' = c2' /\ st1' ~~ st2' /\ lv1' = lv2' /\ ev1 = ev2).

Theorem bridge_noninterference: forall (n: nat),
  bridge_noninterference_id (n).
Proof.
  apply strongind;
  unfold bridge_noninterference_id;
  induction c;
  intros.

  (* Base case *)
  - inversion H0;
    subst.
    inversion H7.
    inversion H7.
    omega.
  - inversion H0.
    inversion H1;
    subst.
    inversion H7.
    inversion H16.
    + split.
      trivial.
      split.
      subst.
      assumption.
      split.
      subst.
      trivial.
      trivial.
    + inversion H16.
    + inversion H17.
      subst.
      contradiction.
    + subst.
      inversion H7.
    + subst.
      omega.

  - inversion H0;
    inversion H1;
    subst.
    + split.
      trivial.
      split.
      assert (st1 ~~ st1').
      apply secret_assign_same_memory with (s ::= e) STOP lv lv1'.
      assumption.
      assert (st2 ~~ st2').
      apply secret_assign_same_memory with (s ::= e) STOP lv lv2'.
      assumption.
      apply memory_transitivity with st1.
      apply memory_commutative.
      assumption.
      apply memory_transitivity with st2.
      assumption.
      assumption.
      split.
      inversion H7.
      inversion H16.
      subst.
      trivial.
      trivial.
    + inversion H7.
      subst.
      inversion H16.
      subst.
      unfold memory_agree in H2.
      specialize (H2 x v'0).
      destruct H19.
      subst.
      destruct l.
      contradiction.
      apply H2 in H18.
      rewrite H18 in H11.
      inversion H11.
    + inversion H17.
      subst.
      contradiction.
    + inversion H7.
      inversion H16.
      subst.
      unfold memory_agree in H2.
      specialize (H2 x v').
      destruct H15.
      subst.
      destruct l0.
      contradiction.
      apply H2 in H14.
      rewrite H14 in H25.
      inversion H25.
    + inversion H7.
      inversion H16.
      subst.
      destruct H15.
      destruct H29.
      subst.
      assert (v = v0).
      apply eval_public_agree with e st1 st2;
      assumption.
      subst.
      split.
      trivial.
      split.
      unfold st_update.
      intros x'.
      intros.
      destruct (string_dec x0 x').
      split; intros; assumption.
      unfold memory_agree in H2.
      specialize (H2 x' v).
      assumption.
      split.
      trivial.
      trivial.
    + inversion H17.
      subst.
      contradiction.
    + omega.
    + omega.
    + omega.

  - inversion_wf.
    inversion H5.
    subst.
    apply bridge_seq with 0 c1 c2 c1' k st1 st1' lv lv1' ev1 in H0.
    destruct H0.
    + do 2 destruct H0.
      destruct H4.
      apply bridge_seq with n2 c1 c2 c2' k st2 st2' lv lv2' ev2 in H1.
      destruct H1.
      * do 2 destruct H1.
        destruct H11.
        assert (x = x0 /\ st1' ~~ st2' /\ lv1' = lv2' /\ ev1 = ev2).
        apply IHc1 with n2 st1 st2 lv (|lv| - k1)%Z.
        -- assert ((| lv | - (| lv | - k1))%Z = k1) as Hnum by omega.
           rewrite Hnum.
           unfold well_formed.
           right.
           assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- destruct H13.
           destruct H14.
           destruct H15.
           subst.
           split.
           ++ destruct H5.
              destruct H12.
              destruct x0. (* TODO make this repeat match or try *)
              ** destruct H15.
                 trivial.
                 apply H13.
                 trivial.
              ** destruct H12.
                 discriminate.
                 apply H5.
                 discriminate.
              ** destruct H12.
                 discriminate.
                 apply H5.
                 discriminate.
              ** destruct H12.
                 discriminate.
                 apply H5.
                 discriminate.
              ** destruct H12.
                 discriminate.
                 apply H5.
                 discriminate.
              ** destruct H12.
                 discriminate.
                 apply H5.
                 discriminate.
              ** destruct H12.
                 discriminate.
                 apply H5.
                 discriminate.
           ++ split.
              assumption.
              split;
              trivial.
      * do 4 destruct H1.
        destruct H11.
        destruct H12.
        assert (x = STOP /\ st1' ~~ x1 /\ lv1' = x2 /\ ev1 = EmptyEvent).
        apply IHc1 with x0 st1 st2 lv (|lv| - k1)%Z.
        assert ((| lv | - (| lv | - k1))%Z = k1) as Hnum by omega.
        rewrite Hnum.
        unfold well_formed.
        right.
        assumption.
        assumption.
        assumption.
        assumption.
        destruct H14.
        destruct H15.
        destruct H16.
        subst.
        contradiction.
      * assumption.
    + do 4 destruct H0.
      omega.
    + assumption.

  - inversion H0.
    inversion H7.
    inversion H7.
    omega.

  - inversion H0.
    inversion H1.
    subst.
    inversion H7.
    inversion H16.
    + split.
      trivial.
      split.
      subst.
      assumption.
      split.
      subst.
      inversion H10.
      trivial.
      trivial.
    + subst.
      inversion H16.
    + subst.
      inversion H17.
      subst.
      contradiction.
    + subst.
      inversion H7.
    + subst.
      omega.

  - inversion H0;
    subst.
    inversion H7.
    inversion H7.
    omega.

  (* Inductive case *)
  - inversion H1.
    subst.
    inversion H10.

  - inversion H1.
    subst.
    inversion H10.
    subst.
    contradiction.

  - inversion H1.
    subst.
    inversion H10.
    subst.
    contradiction.

  - apply bridge_seq with (S n) c1 c2 c1' k st1 st1' lv lv1' ev1 in H1.
    destruct H1.
    + apply bridge_seq with n2 c1 c2 c2' k st2 st2' lv lv2' ev2 in H2.
      destruct H2.
      * do 2 destruct H1.
        destruct H4.
        do 2 destruct H2.
        destruct H6.
        inversion_wf.
        inversion H10.
        assert (x = x0 /\ st1' ~~ st2' /\ lv1' = lv2' /\ ev1 = ev2).
        apply IHc1 with n2 st1 st2 lv (|lv| - k1)%Z.
        -- assert ((| lv | - (| lv | - k1))%Z = k1) as Hnum by omega.
           rewrite Hnum.
           unfold well_formed.
           right.
           assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- destruct H16.
           destruct H17.
           destruct H18.
           split.
           subst.
           destruct H5.
           destruct H7.
           ++ destruct x0. (* TODO make this match and repeat *)
              ** rewrite H10.
                 apply H9.
                 trivial.
                 trivial.
              ** rewrite H7.
                 apply H5.
                 discriminate.
                 discriminate.
              ** rewrite H7.
                 apply H5.
                 discriminate.
                 discriminate.
              ** rewrite H7.
                 apply H5.
                 discriminate.
                 discriminate.
              ** rewrite H7.
                 apply H5.
                 discriminate.
                 discriminate.
              ** rewrite H7.
                 apply H5.
                 discriminate.
                 discriminate.
              ** rewrite H7.
                 apply H5.
                 discriminate.
                 discriminate.
           ++ split. assumption.
              split; assumption.
      * do 2 destruct H1.
        destruct H4.
        do 4 destruct H2.
        destruct H6.
        destruct H7.
        inversion_wf.
        inversion H11.
        subst.
        assert (x = STOP /\ st1' ~~ x1 /\ lv1' = x2 /\ ev1 = EmptyEvent).
        apply IHc1 with x0 st1 st2 lv (|lv| - k1)%Z.
        assert ((| lv | - (| lv | - k1))%Z = k1) as Hnum by omega.
        rewrite Hnum.
        unfold well_formed.
        right.
        assumption.
        assumption.
        assumption.
        assumption.
        destruct H10.
        destruct H11.
        destruct H17.
        subst.
        contradiction.
      * assumption.
    + apply bridge_seq with n2 c1 c2 c2' k st2 st2' lv lv2' ev2 in H2.
      destruct H2.
      * do 4 destruct H1. (* Should be do-able by the inner hypothesis *)
        destruct H4.
        destruct H5.
        do 2 destruct H2.
        destruct H7.
        assert (STOP = x2 /\ x0 ~~ st2' /\ x1 = lv2' /\ EmptyEvent = ev2).
        inversion_wf.
        inversion H11.
        subst.
        apply H with x c1 n2 st1 st2 lv (|lv| - k1)%Z.
        omega.
        assert ((| lv | - (| lv | - k1))%Z = k1) as Hnum by omega.
        rewrite Hnum.
        unfold well_formed.
        right.
        assumption.
        assumption.
        assumption.
        assumption.
        destruct H9.
        destruct H10.
        destruct H11.
        subst.
        contradiction.
      * do 4 destruct H1.
        destruct H4.
        destruct H5.
        do 4 destruct H2.
        destruct H7.
        destruct H8.
        inversion_wf.
        inversion H12.
        subst.
        assert (STOP = STOP /\ x0 ~~ x3 /\ x1 = x4 /\ EmptyEvent = EmptyEvent).
        apply H with x c1 x2 st1 st2 lv (|lv| - k1)%Z.
        omega.
        assert ((| lv | - (| lv | - k1))%Z = k1) as Hnum by omega.
        rewrite Hnum.
        unfold well_formed.
        right.
        assumption.
        assumption.
        assumption.
        assumption.
        destruct H11.
        destruct H12.
        destruct H18.
        subst.
        apply H with (S n - x - 1) c2 (n2 - x2 - 1) x0 x3 x4 (|x4| - k2)%Z.
        omega.
        assert ((| x4 | - (| x4 | - k2))%Z = k2) as Hnum by omega.
        rewrite Hnum.
        unfold well_formed.
        right.
        assumption.
        assumption.
        assumption.
        assumption.
      * assumption.
    + assumption.

  - inversion H1.
    inversion H2;
    subst.
    inversion H20.
    inversion H20.
    inversion H10;
    inversion H21;
    subst.
    + assert (l = l0).
      apply eval_deterministic_level with e st' st'0 u u0;
      assumption.
      subst.
      assert (n = n0) by omega.
      subst.
      assert (n0 <= n0) as Hnum by omega.
      specialize (H n0 Hnum (c1;; JOIN) c1' c2' n1 st' st1' st'0 st2' (l0 :: lv) lv1' lv2' k ev1 ev2).
      apply H.
      * apply preservation_of_well_formedness_for_event_step with (IFB e THEN c1 ELSE c2 FI) st' st' lv EmptyEvent;
        assumption.
      * assumption.
      * assumption.
      * assumption.
    + destruct l.
      * assert (Public = l0).
        apply eval_deterministic_level with e st' st'0 u 0;
        assumption.
        subst.
        assert (u = 0).
        apply eval_public_agree with e st' st'0;
        assumption.
        contradiction.
      * assert (Secret = l0).
        apply eval_deterministic_level with e st' st'0 u 0;
        assumption.
        subst.
        apply bridge_seq with n0 c1 JOIN c1' k st' st1' (Secret :: lv) lv1' ev1 in H14.
        destruct H14.
        -- do 2 destruct H4.
           destruct H5.
           assert (x = STOP /\ st' ~~ st1' /\ (Secret :: lv) = lv1' /\ ev1 = EmptyEvent).
           ++ apply secret_joinfree_bridge_makes_no_event with n0 c1.
              ** apply if_well_formed_zero in H0.
                 apply if_c1_well_formed with e c2 st' lv Secret EmptyEvent;
                 assumption.
              ** apply secret_onstack_makes_level_secret.
              ** assumption.
           ++ destruct H9. destruct H11. destruct H12.
              subst.
              contradiction.
        -- do 4 destruct H4.
           destruct H5.
           destruct H8.
           inversion H9;
           subst.
           ++ apply bridge_seq with n1 c2 JOIN c2' k st'0 st2' (Secret :: lv) lv2' ev2 in H25.
              destruct H25.
              ** do 2 destruct H11.
                 destruct H12.
                 assert (x2 = STOP /\ st'0 ~~ st2' /\ (Secret :: lv) = lv2' /\ ev2 = EmptyEvent).
                 --- apply secret_joinfree_bridge_makes_no_event with n1 c2.
                     +++ apply if_well_formed_zero in H0.
                         apply if_c2_well_formed with e c1 st'0 lv Secret EmptyEvent;
                         assumption.
                     +++ apply secret_onstack_makes_level_secret.
                     +++ assumption.
                 --- destruct H15. destruct H20. destruct H22.
                     subst.
                     contradiction.
              ** do 4 destruct H11.
                 destruct H12.
                 destruct H14.
                 inversion H15;
                 subst.
                 --- assert (STOP = STOP /\ st' ~~ x0 /\ (Secret :: lv) = x1 /\ EmptyEvent = EmptyEvent).
                     apply secret_joinfree_bridge_makes_no_event with x c1.
                     apply if_well_formed_zero in H0.
                     apply if_c1_well_formed with e c2 st' lv Secret EmptyEvent;
                     assumption.
                     apply secret_onstack_makes_level_secret.
                     assumption.
                     assert (STOP = STOP /\ st'0 ~~ x3 /\ (Secret :: lv) = x4 /\ EmptyEvent = EmptyEvent).
                     apply secret_joinfree_bridge_makes_no_event with x2 c2.
                     apply if_well_formed_zero in H0.
                     apply if_c2_well_formed with e c1 st'0 lv Secret EmptyEvent;
                     assumption.
                     apply secret_onstack_makes_level_secret.
                     assumption.
                     destruct H20. destruct H23. destruct H25.
                     destruct H22. destruct H29. destruct H30.
                     subst.
                     inversion H16.
                     inversion H26.
                     subst.
                     split.
                     trivial.
                     split.
                     apply memory_commutative in H23.
                     apply memory_transitivity with st'.
                     assumption.
                     apply memory_transitivity with st'0.
                     assumption.
                     assumption.
                     split.
                     trivial.
                     trivial.
                 --- inversion H26.
                 --- inversion H28.
                     subst.
                     contradiction.
              ** apply preservation_of_well_formedness_for_event_step with (IFB e THEN c1 ELSE c2 FI) st'0 st'0 lv EmptyEvent;
                 assumption.
           ++ inversion H16.
           ++ inversion H20.
              subst.
              contradiction.
        -- apply preservation_of_well_formedness_for_event_step with (IFB e THEN c1 ELSE c2 FI) st' st' lv EmptyEvent;
           assumption.
    + destruct l. (* Same as 2 - TODO make inline Ltac? *)
      * assert (Public = l0).
        apply eval_deterministic_level with e st' st'0 0 u;
        assumption.
        subst.
        assert (0 = u).
        apply eval_public_agree with e st' st'0;
        assumption.
        subst.
        contradiction.
      * assert (Secret = l0).
        apply eval_deterministic_level with e st' st'0 0 u;
        assumption.
        subst.
        apply bridge_seq with n0 c2 JOIN c1' k st' st1' (Secret :: lv) lv1' ev1 in H14.
        destruct H14.
        -- do 2 destruct H4.
           destruct H6.
           assert (x = STOP /\ st' ~~ st1' /\ (Secret :: lv) = lv1' /\ ev1 = EmptyEvent).
           ++ apply secret_joinfree_bridge_makes_no_event with n0 c2.
              ** apply if_well_formed_zero in H0.
                 apply if_c2_well_formed with e c1 st' lv Secret EmptyEvent;
                 assumption.
              ** apply secret_onstack_makes_level_secret.
              ** assumption.
           ++ destruct H9. destruct H11. destruct H12.
              subst.
              contradiction.
        -- do 4 destruct H4.
           destruct H6.
           destruct H8.
           inversion H9;
           subst.
           ++ apply bridge_seq with n1 c1 JOIN c2' k st'0 st2' (Secret :: lv) lv2' ev2 in H25.
              destruct H25.
              ** do 2 destruct H11.
                 destruct H12.
                 assert (x2 = STOP /\ st'0 ~~ st2' /\ (Secret :: lv) = lv2' /\ ev2 = EmptyEvent).
                 --- apply secret_joinfree_bridge_makes_no_event with n1 c1.
                     +++ apply if_well_formed_zero in H0.
                         apply if_c1_well_formed with e c2 st'0 lv Secret EmptyEvent;
                         assumption.
                     +++ apply secret_onstack_makes_level_secret.
                     +++ assumption.
                 --- destruct H15. destruct H18. destruct H20.
                     subst.
                     contradiction.
              ** do 4 destruct H11.
                 destruct H12.
                 destruct H14.
                 inversion H15;
                 subst.
                 --- assert (STOP = STOP /\ st' ~~ x0 /\ (Secret :: lv) = x1 /\ EmptyEvent = EmptyEvent).
                     apply secret_joinfree_bridge_makes_no_event with x c2.
                     apply if_well_formed_zero in H0.
                     apply if_c2_well_formed with e c1 st' lv Secret EmptyEvent;
                     assumption.
                     apply secret_onstack_makes_level_secret.
                     assumption.
                     assert (STOP = STOP /\ st'0 ~~ x3 /\ (Secret :: lv) = x4 /\ EmptyEvent = EmptyEvent).
                     apply secret_joinfree_bridge_makes_no_event with x2 c1.
                     apply if_well_formed_zero in H0.
                     apply if_c1_well_formed with e c2 st'0 lv Secret EmptyEvent;
                     assumption.
                     apply secret_onstack_makes_level_secret.
                     assumption.
                     destruct H18. destruct H22. destruct H23.
                     destruct H20. destruct H28. destruct H30.
                     subst.
                     inversion H16.
                     inversion H25.
                     subst.
                     split.
                     trivial.
                     split.
                     apply memory_commutative in H22.
                     apply memory_transitivity with st'.
                     assumption.
                     apply memory_transitivity with st'0.
                     assumption.
                     assumption.
                     split.
                     trivial.
                     trivial.
                 --- inversion H25.
                 --- inversion H27.
                     subst.
                     contradiction.
              ** apply preservation_of_well_formedness_for_event_step with (IFB e THEN c1 ELSE c2 FI) st'0 st'0 lv EmptyEvent;
                 assumption.
           ++ inversion H16.
           ++ inversion H18.
              subst.
              contradiction.
        -- apply preservation_of_well_formedness_for_event_step with (IFB e THEN c1 ELSE c2 FI) st' st' lv EmptyEvent;
           assumption.
    + assert (l = l0). (* Same as 1 - TODO make inline Ltac? *)
      apply eval_deterministic_level with e st' st'0 0 0;
      assumption.
      subst.
      assert (n = n0) by omega.
      subst.
      assert (n0 <= n0) as Hnum by omega.
      specialize (H n0 Hnum (c2;; JOIN) c1' c2' n1 st' st1' st'0 st2' (l0 :: lv) lv1' lv2' k ev1 ev2).
      apply H.
      * apply preservation_of_well_formedness_for_event_step with (IFB e THEN c1 ELSE c2 FI) st' st' lv EmptyEvent;
        assumption.
      * assumption.
      * assumption.
      * assumption.

  - inversion H1.
    subst.
    inversion H10.
    subst.
    contradiction.

  - inversion H1.
    subst.
    inversion H10.
    subst.
    apply H with n0 (IFB e THEN c;; WHILE e DO c END ELSE SKIP FI) (n2 - 1) st' st2 lv' k.
    + omega.
    + apply preservation_of_well_formedness_for_event_step with (WHILE e DO c END) st' st' lv' EmptyEvent.
      * assumption.
      * assumption.
    + assert (n = n0) by omega.
      subst.
      assumption.
    + inversion H2;
      subst.
      * inversion H11.
      * inversion H11.
      * inversion H12.
        subst.
        assert (n1 + 1 - 1 = n1) as Hnum by omega.
        rewrite Hnum.
        assumption.
    + assumption.
Qed.


(* Semantics for allowing a command to make 'n' steps *)
Inductive step_times : config -> nat -> config -> Prop :=
  | step_zero: forall c st lv,
        step_times〈 c, st, lv 〉 0 〈 c, st, lv 〉
  | step_multi: forall c c' c'' st st' st'' lv lv' lv'' n,
       〈 c, st, lv 〉 ⇒ 〈 c', st', lv' 〉->
       step_times 〈 c', st', lv' 〉 n 〈 c'', st'', lv'' 〉 ->
       step_times 〈 c, st, lv 〉 (n+1) 〈 c'', st'', lv'' 〉.

(* Lemma stating that when taking multiple steps,
   this could also be achieved by first making a bridge
   and multi step from there *)
Lemma bridge_adequacy: forall (n: nat) (c: cmd) (st st'': state) (lv lv'': list level) (k': Z),
  well_formed c (|lv| - k') ->
  step_times 〈 c, st, lv 〉 n 〈 STOP, st'', lv'' 〉 ->
  (c = STOP \/
   exists c' st' lv' ev k n', k + n' + 1 = n /\
   bridge 〈 c, st, lv 〉 ev k 〈 c', st', lv' 〉 /\
   step_times 〈 c', st', lv' 〉 n' 〈 STOP, st'', lv'' 〉).
Proof.
  intro n.
  induction n;
  intros.
  - inversion H0;
    subst.
    + left.
      trivial.
    + omega.
  - inversion H0.
    subst.
    assert (n = n0) as Hnum by omega.
    subst.
    apply same_semantics in H3.
    destruct H3.
    destruct x.
    + destruct n0.
      * inversion H9;
        subst.
        -- right.
           exists STOP.
           exists st''.
           exists lv''.
           exists EmptyEvent.
           exists 0.
           exists 0.
           split.
           omega.
           split.
           apply bridge_stop.
           assumption.
           assumption.
        -- omega.
      * specialize (IHn c' st' st'' lv' lv'' k').
        assert (c' = STOP \/ exists (c'0 : cmd) (st'0 : state) (lv'0 : list level) (ev : event) (k n' : nat),
                k + n' + 1 = S n0 /\
                bridge 〈 c', st', lv' 〉 ev k 〈 c'0, st'0, lv'0 〉 /\
                step_times 〈 c'0, st'0, lv'0 〉 n' 〈 STOP, st'', lv'' 〉).
        apply IHn.
        apply preservation_of_well_formedness_for_event_step with c st st' lv EmptyEvent.
        assumption.
        assumption.
        assumption.
        destruct H2.
        subst.
        inversion H9.
        subst.
        inversion H4.
        do 7 destruct H2.
        destruct H3.
        right.
        exists x.
        exists x0.
        exists x1.
        exists x2.
        exists (x3 + 1).
        exists x4.
        split.
        omega.
        split.
        apply bridge_multi with c' st' lv'.
        assumption.
        destruct c'.
        inversion H3;
           subst.
           inversion H12.
           inversion H12.
           inversion H13.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
        assumption.
        assumption.
    + right.
      exists c'.
      exists st'.
      exists lv'.
      exists (AssignmentEvent s n).
      exists 0.
      exists n0.
      split.
      omega.
      split.
      apply bridge_public.
      assumption.
      assumption.
Qed.


(* Lemma stating a bridge also preserves the well formedness
   by repeating the preservation of well formedness for event steps *)
Lemma preservation_of_well_formedness_for_bridge: forall (n: nat) (k: Z) (c c': cmd) (st st': state) (lv lv': list level) (ev: event),
  well_formed c (|lv| - k)%Z ->
  bridge 〈 c, st, lv 〉 ev n 〈 c', st', lv' 〉 ->
  well_formed c' (|lv'| - k)%Z.
Proof.
  intro n.
  induction n;
  intros.
  - inversion H0;
    subst.
    + apply preservation_of_well_formedness_for_event_step with c st st' lv EmptyEvent;
      assumption.
    + apply preservation_of_well_formedness_for_event_step with c st st' lv (AssignmentEvent x v);
      assumption.
    + omega.
  - inversion H0.
    subst.
    assert (n = n0) by omega.
    subst.
    apply IHn with c'0 st'0 st' lv'0 ev.
    + apply preservation_of_well_formedness_for_event_step with c st st'0 lv EmptyEvent;
      assumption.
    + assumption.
Qed.


(* The master proof, proofing the if a command takes multiple steps
   with start agreeing memories and stack, the the resulting memories
   also agrees.
   This thus gives us the final property; that the dynamic step semantics
   gives us noninterferrence.
   Made with definition to allow for strong induction *)
Definition step_noninterference_id (n: nat) : Prop :=
  forall m c st1 st1' st2 st2' lv lv1' lv2' k,
  well_formed c (|lv| - k) ->
  st1 ~~ st2 ->
  step_times 〈 c, st1, lv 〉 n 〈 STOP, st1', lv1' 〉 ->
  step_times 〈 c, st2, lv 〉 m 〈 STOP, st2', lv2' 〉 ->
  st1' ~~ st2'.

Theorem step_noninterference: forall n,
  step_noninterference_id (n).
Proof.
  apply strongind;
  unfold step_noninterference_id;
  intros.
  - inversion H1;
    subst.
    + inversion H2;
      subst.
      * assumption.
      * inversion H7.
    + omega.
  - assert (c = STOP \/
            exists c' st' lv' ev k n', k + n' + 1 = S n /\
            bridge 〈 c, st1, lv 〉 ev k 〈 c', st', lv' 〉 /\
            step_times 〈 c', st', lv' 〉 n' 〈 STOP, st1', lv1' 〉).
    apply bridge_adequacy with k;
    assumption.
    destruct H4.
    + subst.
      inversion H2.
      subst.
      inversion H6.
    + do 7 destruct H4.
      destruct H5.
      assert (c = STOP \/
              exists c' st' lv' ev k n', k + n' + 1 = m /\
              bridge 〈 c, st2, lv 〉 ev k 〈 c', st', lv' 〉 /\
              step_times 〈 c', st', lv' 〉 n' 〈 STOP, st2', lv2' 〉).
      apply bridge_adequacy with k;
      assumption.
      destruct H7.
      * subst.
        inversion H2.
        subst.
        inversion H9.
      * do 7 destruct H7.
        destruct H8.
        assert (x = x5 /\ x0 ~~ x6 /\ x1 = x7 /\ x2 = x8).
        eapply bridge_noninterference;
        eassumption.
        destruct H10.
        destruct H11.
        destruct H12.
        subst.
        specialize (H x4).
        apply H with x10 x5 x0 x6 x7 lv1' lv2' k.
        omega.
        apply preservation_of_well_formedness_for_bridge with x3 c st1 x0 lv x8;
        assumption.
        assumption.
        assumption.
        assumption.
Qed.



(* Non indexed multi step relation *)
Inductive steps_to : config -> config -> Prop :=
  | steps_to_zero: forall c st lv,
        steps_to〈 c, st, lv 〉 〈 c, st, lv 〉
  | steps_to_multi: forall c c' c'' st st' st'' lv lv' lv'',
       〈 c, st, lv 〉 ⇒ 〈 c', st', lv' 〉->
       steps_to 〈 c', st', lv' 〉 〈 c'', st'', lv'' 〉 ->
       steps_to 〈 c, st, lv 〉 〈 c'', st'', lv'' 〉.

(* Conversion lemma between the indexed and non indexed step relation *)
Lemma steps_to_same_as_step_times: forall c c' st st' lv lv',
  steps_to 〈 c, st, lv 〉〈 c', st', lv'〉 <-> exists n, step_times 〈 c, st, lv 〉n〈 c', st', lv'〉.
Proof.
  split;
  intros.
  - induction H.
    + exists 0.
      constructor.
    + destruct IHsteps_to.
      exists (x+1).
      apply step_multi with c'0 st'0 lv'0;
      assumption.
  - destruct H.
    induction H.
    + constructor.
    + apply steps_to_multi with c'0 st'0 lv'0;
      assumption.
Qed.


(* Noninterference for the nonindexed step relation *)
Theorem step_noninterferrence: forall c st1 st1' st2 st2' lv lv1' lv2' k,
  well_formed c (|lv| - k) ->
  st1 ~~ st2 ->
  steps_to 〈 c, st1, lv 〉 〈 STOP, st1', lv1' 〉 ->
  steps_to 〈 c, st2, lv 〉 〈 STOP, st2', lv2' 〉 ->
  st1' ~~ st2'.
Proof.
  intros.
  apply steps_to_same_as_step_times in H1.
  destruct H1.
  apply steps_to_same_as_step_times in H2.
  destruct H2.
  eapply step_times_noninterference;
  eassumption.
Qed.











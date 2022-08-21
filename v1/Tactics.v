From LF Require Export Poly.

Theorem silly1: forall (n m o p : nat),
  n = m -> [n;o] = [n;p] -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1. apply eq2. (* Hypothesis and the goal is the same. *)
Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m -> (n = m -> [n;o] = [m;p]) -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. (* Replace the goal with the predicate of eq2. *)
  apply eq1.
Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q, q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly_ex :
  (forall n, even n = true -> odd (S n) = true) ->
  even 2 = true -> odd 3 = true.
Proof.
  intros eq1 eq2. apply eq1. apply eq2. Qed
.

Theorem silly3_firsttry : forall (n : nat),
  true = (n =? 5) ->
  (S (S n)) =? 7 = true.
Proof.
  intros n H. symmetry. (* Swap left and right of the goal. *)
  simpl. apply H. Qed
.

Theorem rev_injective : forall (l l' : list nat),
  rev l = rev l' -> l = l'.
Proof.
  intros l l' H.
  rewrite <- rev_involutive. rewrite <- H. symmetry. apply rev_involutive.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros. rewrite -> H. symmetry. apply rev_involutive.
Qed
.

Example trans_eq_example : forall (a b c d e f : nat),
 [a;b] = [c;d] -> [c;d]=[e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity. Qed
.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed
.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.
Qed
.

Example trans_eq_example'' : forall (a b c d e f : nat),
  [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d]. (* transitivity tactic accomplishes the same purpose as applying trans_eq. *)
  apply eq1. apply eq2.
Qed
.

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  transitivity m. apply eq2. apply eq1. Qed
.

Theorem S_injective : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.

(* Any constructors are injective. *)
(* injection tactic makes use of injectivity of constructors. *)
Theorem S_injective' : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as Hnm. (* generate all equations that it can infer from H using the injectivity of consturctors. i.e (H: S n = S m) -> (Hnm: n m). *)
  apply Hnm.
Qed
.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity. Qed
.

Theorem injection_ex2 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. (* All the equations are turned into hypotheses at the beginning of the goal. *)
  intros H1 H2. rewrite H1. rewrite H2. reflexivity. Qed
.

Example inejction_ex3: forall (X: Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j -> j = z :: l -> x = y.
Proof.
  intros X x y z l j eq1 eq2.
  injection eq1 as eq11 eq12.
  assert (H : y :: l = z :: l). {
    transitivity j.
    apply eq12. apply eq2.
  }
  injection H as H1.
  rewrite eq11. rewrite H1. reflexivity. Qed
.

Theorem eqb_0_1 : forall n,
  0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - simpl. intros H. discriminate H. (* principle of explosion *)
Qed.
Theorem discriminate_ex1 : forall n : nat,
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
Qed.

Example discriminate_ex2: forall n m : nat,
  false = true -> [n] = [m].
Proof.
  intros. discriminate H.
Qed.

Example discriminate_ex3: forall (X:Type) (x y z:X) (l j : list X),
  x :: y :: l = [] -> x = z.
Proof.
  intros. discriminate H.
Qed
.


Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof.
  intros A B f x y eq. rewrite eq. reflexivity. Qed
.

Theorem eq_implies_succ_equal : forall n m : nat,
  n = m -> S n = S m.
Proof.
  intros. apply f_equal. apply H. Qed.

(* f_equal tactic: Given the goal f a1 ... an = g b1 ... bn, it produce subgoals f = g, a1 = b1, ..., an = bn. *)
Theorem eq_implies_succ_equal' : forall n m : nat,
  n = m -> S n = S m.
Proof.
  intros n m H.
  f_equal. apply H. Qed
.

(* Using Tactics on Hypotheses *)
Theorem S_inj : forall (n m : nat) (b:bool),
  (S n) =? (S m) = b -> n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed
.

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed
.

Theorem double_injective_FAILED : forall n m,
double n = double m ->
n = m.
Proof.
intros n m. induction n as [| n' IHn'].
- (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
  + (* m = O *) reflexivity.
  + (* m = S m' *) discriminate eq.
- (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
  + (* m = O *) discriminate eq.
  + (* m = S m' *) apply f_equal. Abort
.

Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
  Proof.
  induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - simpl. intros m eq. destruct m as [|m'] eqn:E.
    + discriminate eq.
    + f_equal. apply IHn'. simpl in eq. injection eq as goal. apply goal.
Qed
.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  induction n as [|n' IHn'].
  - destruct m as [|m'].
    + reflexivity.
    + intros H. simpl in H. discriminate H.
  - destruct m as [|m'].
    + intros H. simpl in H. discriminate H.
    + simpl. intros H. apply IHn' in H. rewrite H. reflexivity.
Qed
.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m -> n = m.
Proof.
  induction n as [|n' IHn'].
  - destruct m as [|m'].
    + reflexivity.
    + simpl. intros H. simpl in H. discriminate H.
  - destruct m as [|m'].
    + simpl. intros H. discriminate H.
    + simpl. intros H. injection H as H1. rewrite <- plus_n_Sm in H1. symmetry. rewrite <- plus_n_Sm in H1. injection H1 as H2. apply IHn' in H2. rewrite H2. reflexivity.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros eq. destruct n as [|n'] eqn:E.
    + discriminate eq.
    + f_equal. Abort
.

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. (* Context: n, m: nat, Goal: double n = double m -> n = m *)
  generalize dependent n. (* Context: m : nat, Goal: forall n : nat, double n = double m -> n = m *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros n eq. destruct n as [|n'] eqn:E.
    + discriminate eq.
    + f_equal. apply IHm'. simpl in eq. injection eq as goal. apply goal. Qed
.

Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| h t IHl'].
  - intros H. simpl. reflexivity.
  - intros n H. simpl in H. simpl. destruct n.
    + discriminate H.
    + apply IHl'. injection H as H1. apply H1. Qed
.

(* Unfolding Definitinos *)
Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert (H: n*m*n = n*n*m). { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity. Qed
.


Definition foo (x : nat) := 5.
Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
  Qed
.

Definition bar x :=
  match x with | O => 5 | S _ => 5 end
.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl.
Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn: E.
  - reflexivity.
  - reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n:nat) : bool := 
  if n =? 3 then false
  else if n =? 5 then false
  else false
.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
  - reflexivity.
  - destruct (n =? 5) eqn: E2.
    + reflexivity.
    + reflexivity. Qed
.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l l1 l2 H.
  generalize dependent l2.
  generalize dependent l1.
  induction l as [|h t IH].
  - unfold split. simpl. intros l1 l2 H. injection H as H1 H2. rewrite <- H1. rewrite <- H2. reflexivity.
  - intros l1 l2. destruct h as [x y]. intros H. simpl in H. destruct (split t) as [xt yt]. destruct l1 as [|h1 t1].
    + discriminate H.
    + destruct l2 as [|h2 t2].
      * discriminate H.
      * simpl. f_equal.
        ** injection H as H1 H2. rewrite H1. rewrite H. reflexivity.
        ** apply IH. injection H as H1 H2. rewrite H2. rewrite H0. reflexivity.
Qed
.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

  Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true -> odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  - Abort
.

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true -> odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:E.
  - apply eqb_true in E. rewrite E. reflexivity.
  - destruct (n =? 5) eqn:E5.
    + apply eqb_true in E5.
      rewrite E5. reflexivity.
    + discriminate eq. Qed
.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f true) eqn:Et.
  - destruct (f false) eqn:Ef.
    + destruct b.
      * rewrite Et. rewrite Et. rewrite Et. reflexivity.
      * rewrite Ef. rewrite Et. rewrite Et. reflexivity.
    + destruct b.
      * rewrite Et. rewrite Et. rewrite Et. reflexivity.
      * rewrite Ef. rewrite Ef. rewrite Ef. reflexivity.
  - destruct (f false) eqn:Ef.
  + destruct b.
    * rewrite Et. rewrite Ef. rewrite Et. reflexivity.
    * rewrite Ef. rewrite Et. rewrite Ef. reflexivity.
  + destruct b.
    * rewrite Et. rewrite Ef. rewrite Ef. reflexivity.
    * rewrite Ef. rewrite Ef. rewrite Ef. reflexivity.
Qed
.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  induction n as [| n' IHn'].
  - destruct m as [| m'].
    + reflexivity.
    + reflexivity.
  - destruct m as [| m'].
    + reflexivity.
    + simpl. apply IHn'.
Qed
.

Theorem eqb_trans : forall n m p,
  n =? m = true -> m =? p = true -> n =? p = true.
Proof.
  intros n m p H1 H2.
  apply eqb_true in H1. apply eqb_true in H2.
  rewrite H1. rewrite H2. rewrite eqb_refl. reflexivity.
Qed
.

Definition split_combine_statement : Prop := 
  forall X Y (l1: list X) (l2:list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  unfold split_combine_statement.
  intros X Y.
  induction l1 as [| h1 t1 IH1].
  - simpl. destruct l2 as [| h2 t2].
    + reflexivity.
    + simpl. discriminate.
  - simpl. destruct l2 as [| h2 t2].
    + simpl. discriminate.
    + simpl. intro H. injection H as H'. apply IH1 in H'. rewrite H'. reflexivity.
Qed.

Fixpoint forallb {X:Type} (test:X->bool) (l:list X) : bool := 
  match l with 
  | nil => true
  | x::t => match test x with
    | true => forallb test t
    | false => false
  end
  end
.

Fixpoint existsb {X:Type} (test:X->bool) (l:list X) : bool := 
  match l with 
  | nil => false
  | x::t => match test x with
    | true => true
    | false => existsb test t
  end
  end
.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X:Type} (test:X->bool) (l:list X) : bool :=
  negb (forallb (fun x => negb (test x)) l)
.

Example test_existsb_1' : existsb' (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2' : existsb' (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3' : existsb' odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4' : existsb' even [] = false.
Proof. reflexivity. Qed.

Theorem existsb_existsb' : forall (X:Type) (test:X->bool) (l:list X),
  existsb test l = existsb' test l.
Proof.
  induction l as [| h t IHl].
  - reflexivity.
  - simpl. destruct (test h) eqn: eq.
    + unfold existsb'. simpl. rewrite eq. reflexivity.
    + unfold existsb'. simpl. rewrite eq. simpl. unfold existsb' in IHl. apply IHl.
Qed.


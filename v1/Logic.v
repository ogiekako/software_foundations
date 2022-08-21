Set Warnings "-notation-overridden,-parsing".
From LF Require Export Tactics.

Check 3 = 3: Prop.


Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

Definition injective {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y
.

Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
  Qed
.

Check @eq : forall A : Type, A -> A -> Prop.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed
.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

Example and_exercise : forall n m : nat , n + m = 0 -> n= 0 /\ m = 0.
Proof.
 split.
 - destruct n.
  + reflexivity.
  + discriminate H.
 - destruct m.
  + reflexivity.
  + rewrite <- plus_n_Sm in H. discriminate.
Qed
.

Example add_example2:
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Example add_example2':
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Example add_example3:
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm]  .
  rewrite Hn. 
  reflexivity.
Qed.

Lemma proj1: forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP.
  Qed
.

Lemma proj2: forall P Q : Prop, P /\ Q -> Q.
Proof.
  intros P Q HPQ.
  destruct HPQ as [_ HP].
  apply HP.
  Qed
.

Theorem add_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP. Qed
.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed
.

(* A /\ B is a syntactic sugar for and A B. *)
Check and : Prop -> Prop -> Prop.

Lemma eq_mult_0 : forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O. reflexivity.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed
.
Lemma or_intro_r : forall A B : Prop, B -> A \/ B.
Proof.
  intros A B HB.
  right.
  apply HB.
Qed
.

Lemma zero_or_succ :
forall n : nat, n = O \/ n = S (pred n).
Proof.
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed
.

Module MyNot.
Definition not (P : Prop) := P -> False.
Notation "- x" := (not x) : type_scope.
Check not : Prop -> Prop.
End MyNot.

Theorem ex_falso_eudlibet : forall P : Prop,
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Fact not_implies_our_not : forall P:Prop,
  ~P -> (forall Q:Prop, P -> Q).
Proof.
  intros P H Q HP.
  unfold not in H. apply H in HP. destruct HP. Qed
.

Notation "x <> y" := (~ (x = y)).

Theorem zero_not_one : 0 <> 1.
Proof. unfold not. intros contra. discriminate contra.
Qed
.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed
.

Theorem contradition_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed
.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H. Qed
.


Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros P Q HPQ.
  unfold not. intros HQ. intros HP.
  apply HQ. apply HPQ. apply HP.
Qed
.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P. unfold not. intros [HP HNP]. apply HNP. apply HP.
Qed
.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn: HE.
  - unfold not in H.
    apply ex_falso_eudlibet. (* exfalso . *)
    apply H. reflexivity.
  - reflexivity.
Qed
.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso.
    apply H. reflexivity.
  - reflexivity.
Qed
.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
  (at level 95, no associativity) : type_scope.
End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - apply HBA.
  - apply HAB.
  Qed
.

Lemma not_true_iff_false : forall b, b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros H. rewrite H. intros H'. discriminate H'.
Qed.

Theorem or_distribute_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [H1|[H2 H3]].
    + split.
      * left. apply H1.
      * left. apply H1.
    + split.
      * right. apply H2.
      * right. apply H3.
  - intros [[] []].
   + left. apply H.
   + left. apply H.
   + left. apply H0.
   + right. split.
    * apply H.
    * apply H0.
Qed.

Theorem and_distribute_over_or : forall P Q R : Prop,
  P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
  intros P Q R. split.
  - intros [H1 [H2|H3]].
    + left. split.
      * apply H1.
      * apply H2.
    + right. split.
      * apply H1.
      * apply H3.
  - intros [[H1 H2]|[H1 H2]].
   + split.
    * apply H1.
    * left. apply H2.
   + split.
    * apply H1.
    * right. apply H2.
Qed.

(* Setoids and Logical Equivalence *)
From Coq Require Import Setoids.Setoid. (* allows to use rewrite and reflexivity with iff statements, not just equalities. *)

Theorem mult_eq_0 : forall n m , n * m = 0 -> n = 0 \/ m = 0.
Proof. intros [] [] H.
  - right. reflexivity.
  - left. reflexivity.
  - right. reflexivity.
  - simpl in H. discriminate H.
Qed
.


Lemma mult_0 : forall n m , n * m = 0 <-> n = 0 \/ m = 0.
Proof.
    split.
    - apply mult_eq_0.
    - apply eq_mult_0.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.  
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 : forall n m p, n * m * p = 0 <-> n = 0 \/  m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc. reflexivity. Qed
.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H. Qed
.

(* Existential Quantification *)
Definition Even x := exists n : nat, x = double n.

Lemma four_is_even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example : forall n,
  (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

Theorem dist_not_exists : forall (X:Type) (P:X->Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H. unfold not. intros [x H2]. apply H2. apply H. Qed
.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x [HP|HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP]|[x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ.
Qed
.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | nil => False
  | x' :: l' => x' = x \/ In x l'
  end
.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.
Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl. intros []. (* [] destructs False. *)
  - simpl.  intros [H|H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed
.

Check or_intro_r : forall A B : Prop, B -> A \/ B.

Theorem In_map_iff : forall A B (f : A -> B) (l : list A) (y : B),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. induction l as [|x l IHl].
  - simpl. split.
    + intros [].
    + intros [_ [_ []]].
  - simpl. split.
    + intros [H1|H2].
      * exists x. split.
        ** apply H1.
        ** left. reflexivity.
      * apply IHl in H2. destruct H2 as [x' [H1 H2]].
        exists x'. split.
        ** apply H1.
        ** right. apply H2.
    + intros [x' [H1 [H2|H2]]].
      * left. rewrite H2. apply H1.
      * right. rewrite IHl. exists x'. split.
        ** apply H1.
        ** apply H2.
Qed.

Theorem In_app_iff : forall A l l' (a : A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [| a' l' IH].
  - simpl. split.
    + intros H. right. apply H.
    + intros [[]|H].
      apply H.
  - intros l1 a. simpl. rewrite IH. apply or_assoc.
Qed
.

Fixpoint All {T:Type} (P:T->Prop) (l : list T) : Prop :=
  match l with
  | nil => True
  | h :: t => P h /\ All P t end
.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l. split.
  - intros H. induction l as [|h t IHl].
    + reflexivity.
    + simpl. split.
      * apply H. simpl. left. reflexivity.
      * apply IHl. intro H1. intro H2. apply H. simpl. right. apply H2.
  - (* <- *)intros HA x H. generalize dependent l. induction l as [|h t IH].
    + simpl. intros. destruct H.
    + simpl. intros [H1 H2]. intros [H3|H4].
      * rewrite <- H3. apply H1.
      * apply IH.
        ** apply H2.
        ** apply H4.
Qed
.

(* Exercise: 2 stars, standard, optional (combine_odd_even) *)
Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  . Abort.

  (* TODO: solve the exercise. *)


(* Applying Theorems to Arguments *)

(* Proofs are first-class objects in Coq. *)

Check add_comm : forall n m : nat, n + m = m + n.
(* The type of the proof object is the proposition which it is a proof of. *)

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z. (* x + (y + z) *)
  rewrite add_comm. (* y + z + x *)
  rewrite (add_comm y z). (* z + y + x. Proofs can be applied *)
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intros Hl.
  rewrite Hl in H. simpl in H. apply H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat , In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Lemma in_not_nil_42_take3 :
  forall l : list nat , In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

Lemma in_not_nil_42_take4 :
  forall l : list nat , In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5 :
  forall l : list nat , In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H). (* Use theorem as a function to map H and apply the returned value (Prop). *)
Qed.

Check proj1 : forall P Q : Prop, P /\ Q -> P.

Definition mult_n_0 := mult_n_O.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
    as [m [Hm _]].
  rewrite <- mult_n_0 in Hm. rewrite <- Hm. reflexivity.
Qed.

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof.
  reflexivity.
Qed.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

(* Prints Axioms theorems rely on. *)
Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | x :: l1' => rev_append l1' (x :: l2) end
.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l []
.

Lemma rev_append_const : forall X (l1 l2 : list X),
  rev_append l1 l2 = rev_append l1 [] ++ l2.
Proof.
  intros X.
  induction l1.
  - intros l2. reflexivity.
  - intros l2. simpl. rewrite IHl1. symmetry. rewrite IHl1.
    rewrite <- app_assoc. reflexivity.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  induction x as [| h x' IHx].
  - reflexivity.
  - simpl. rewrite <- IHx. unfold tr_rev. simpl.
    (* rev_append x' [h] = rev_append x' [] ++ [h] *)
    apply rev_append_const.
Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
  induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Lemma even_double_conv : forall n : nat, exists k : nat,
 n = if even n then double k else S (double k).
Proof.
  induction n as [|n' IHn].
  - exists 0. reflexivity.
  - destruct (even n') eqn:E.
    + (* n' is Even *) destruct IHn as [k IHn].
      exists k. rewrite even_S. rewrite E. simpl. rewrite IHn. reflexivity.
    + (* n' is odd *) destruct IHn as [k IHn].
      exists (S k). rewrite even_S. rewrite E. simpl. rewrite IHn. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as[k Hk].
    rewrite H in Hk. rewrite Hk. exists k. reflexivity.
  - intros [k H]. rewrite H. apply even_double.
Qed.

Search eqb.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. symmetry. rewrite eqb_refl. reflexivity.
Qed.

Example not_even_1001 : even 1001 = false.
Proof.
  reflexivity.
Qed.

Example not_even_1001' : ~ (Even 1001).
Proof.
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intros H.
  discriminate H.
Qed.

Lemma plus_eqb_example: forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(*
Note the complementary strengths of booleans and general propositions. Being able to cross back and forth between the boolean and propositional worlds will often be conveninent.
*)

Theorem andb_true_iff : forall b1 b2: bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  split.
  - intros H. destruct b1.
    + split.
      * reflexivity.
      * destruct b2.
        ** reflexivity.
        ** simpl in H. apply H.
    + split.
      * simpl in H. apply H.
      * simpl in H. discriminate H.
  - intros [H1 H2]. rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  split.
  - intros H. destruct b1.
    + left. reflexivity.
    + simpl in H. right. apply H.
  - intros [H|H].
    + rewrite H. reflexivity.
    + rewrite H. destruct b1.
      * reflexivity.
      * reflexivity.
Qed.

Check not_true_iff_false : forall b : bool, b <> true <-> b = false.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  split.
  - intros H. rewrite <- not_true_iff_false in H. unfold not in H. unfold not. intros H2. apply H. rewrite eqb_eq. apply H2.
  - intros H. rewrite <- not_true_iff_false. unfold not in H. unfold not. intros H2. apply H. rewrite eqb_eq in H2. apply H2.
Qed.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | h1::l1', h2::l2' => if eqb h1 h2 then eqb_list eqb l1' l2' else false
    end
.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2)
    -> forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H. induction l1 as [| n1 l1' IHl1].
  - simpl. split.
    + destruct l2.
      * reflexivity.
      * discriminate.
    + intro H2. rewrite <- H2. reflexivity.
  - split.
    + simpl. destruct l2 as [|n2 l2'].
      * discriminate.
      * destruct (eqb n1 n2) eqn:E.
        ** intros H2. apply H in E. rewrite E. rewrite IHl1 in H2. rewrite H2. reflexivity.
        ** discriminate.
    + intros H2. rewrite <- H2. simpl. assert (E: eqb n1 n1 = true). {
      rewrite H. reflexivity.
    }
      rewrite E. rewrite IHl1. reflexivity.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
end
.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  induction l as [|n l' IHl].
  - split.
    + reflexivity.
    + reflexivity.
  - simpl. rewrite andb_true_iff. rewrite IHl. reflexivity.
Qed.

(** Classicla vs. Constructive Logic **)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P. (* Not provable !! *)


(* If P is reflected to some boolean term b... *)
Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. discriminate.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n=m) (n=?m)).
  symmetry.
  apply eqb_eq.
Qed.

(* In Coq, existential conditions are constructive. i.e. For exists x, P x, it's always possible to exhibit a value of x for which we can prove P x.
Such logics are referred to as constructive logics.

Move conventional logical systems such as ZFC, in which the excluded middle does hold for arbitrary propositions, are referred to as classical.
*)

(*
~( P \/ ~P ) 
( ~P \/ ~~P )

*)
Theorem excluded_middle_irrefutable : forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros P H.
  assert (HP: P -> False). {
    intro H2.
    apply H.
    left.
    apply H2.
  }
  apply H. right. apply HP.
Qed.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P: X -> Prop),
  ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold not.
  intros EM X P H x.
  assert (HP: (P x -> False) -> False). {
    intros H1.
    apply H.
    exists x. apply H1.
  }
  assert (EM2: P x \/ ~ P x). {
    apply EM.
  }
  unfold not in EM2.
  destruct EM2 as [EM2|EM2].
  - apply EM2.
  - apply HP in EM2. destruct EM2.
Qed.

Definition peirce := forall P Q : Prop, ((P -> Q) -> P) -> P.
Definition double_negation_elimination := forall P : Prop, ~~P -> P.
Definition de_morgan_not_and_not := forall P Q : Prop,
  ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q : Prop,
  (P -> Q) -> (~P \/ Q).

Theorem excluded_middle_peirce : excluded_middle -> peirce.
Proof.
  unfold excluded_middle, peirce.
  intros EM P Q H.
  destruct (EM P) as [HP|HP].
  - apply HP.
  - apply H. intros P2. exfalso. apply HP. apply P2.
Qed.


Theorem peirce_double_negation_elimination : peirce -> double_negation_elimination.
Proof.
  unfold peirce, double_negation_elimination, not.
  intros HP P NNP.
  apply (HP P False). intros H. destruct (NNP H).
Qed.

Theorem double_negation_elimination_de_morgan_not_and_not : double_negation_elimination -> de_morgan_not_and_not.
Proof.
  unfold double_negation_elimination, de_morgan_not_and_not, not.
  intros HP P Q H. apply HP. intros HPQ. apply H. split.
  - intros P2. apply HPQ. left. apply P2.
  - intros Q2. apply HPQ. right. apply Q2.
Qed.

Theorem de_morgan_not_and_not_implies_to_or : de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not, implies_to_or, not.
  intros HP P Q HPQ. apply HP. intros [H1 H2]. apply H1. intro P2.
  apply H2, HPQ, P2.
Qed.

Lemma or_symmetry : forall A B : Prop, A \/ B <-> B \/ A.
Proof.
  split.
  - intros [HA|HB].
    + right. apply HA.
    + left. apply HB.
  - intros [HB|HA].
    + right. apply HB.
    + left. apply HA.
Qed.

Theorem implies_to_or_excluded_middle : implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or, excluded_middle, not.
  intros HP P. rewrite or_symmetry. apply HP. intro P2. apply P2.
Qed.

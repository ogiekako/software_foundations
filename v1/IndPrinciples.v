(* Basics *)

Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n
.

Theorem mul_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros. simpl. rewrite H. reflexivity.
Qed.

Inductive time : Type :=
  | day
  | night.
Check time_ind :
  forall P : time -> Prop,
    P day ->
    P night ->
    forall t : time, P t
.

Inductive rgb : Type :=
  | red
  | green
  | blue.

(*
forall P : rgb -> Prop,
  P red ->
  P green ->
  P blue ->
  forall t : rgb, P t
*)
Check rgb_ind.

Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).
Check natlist_ind :
  forall P : natlist -> Prop,
    P nnil ->
    (forall (n : nat) (l : natlist),
        P l -> P (ncons n l)) ->
    forall l : natlist, P l
.

Inductive natlist' : Type :=
  | nnil'
  | nsnoc (l : natlist') (n : nat)
.

Check natlist'_ind :
  forall P : natlist' -> Prop,
    P nnil' ->
    (forall l : natlist', P l -> forall n : nat, P (nsnoc l n)) ->
    forall n : natlist', P n
.

Inductive booltree : Type :=
  | bt_empty
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).
(* What is the induction principle for booltree? Of course you could
   ask Coq, but try not to do that. Instead, write it down yourself on
   paper. Then look at the definition of booltree_ind_type, below.
   It has three missing pieces, which are provided by the definitions
   in between here and there. Fill in those definitions based on what
   you wrote on paper. *)
Definition booltree_property_type : Type := booltree -> Prop.
Definition base_case (P : booltree_property_type) : Prop
  := P bt_empty.
Definition leaf_case (P : booltree_property_type) : Prop
  := (forall b: bool, P (bt_leaf b)).
Definition branch_case (P : booltree_property_type) : Prop
  := (forall b: bool, forall t1: booltree, P t1 -> forall t2: booltree, P t2 ->
  P (bt_branch b t1 t2)).
Definition booltree_ind_type :=
  forall (P : booltree_property_type),
    base_case P ->
    leaf_case P ->
    branch_case P ->
    forall (b : booltree), P b
.

Theorem booltree_ind_type_correct : booltree_ind_type.
Proof. exact booltree_ind.
Qed.

Inductive Toy : Type :=
  | con1 (b: bool)
  | con2 (n: nat) (t: Toy)
.

Theorem Toy_correct : exists f g,
  forall P : Toy -> Prop,
    (forall b : bool, P (f b)) ->
    (forall (n : nat) (t : Toy), P t -> P (g n t)) ->
    forall t : Toy, P t.
Proof. exists con1, con2. exact Toy_ind. Qed.

(* Polymorphism *)
Inductive tree (X:Type): Type :=
  | leaf (x: X)
  | node (t1 t2: tree X).
Check tree_ind:
  forall (X: Type) (P: tree X -> Prop),
    (forall (x: X), P (leaf X x)) ->
    (forall (t1: tree X), P t1 ->
     forall (t2: tree X), P t2 -> P (node X t1 t2)) ->
    (forall t: tree X, P t).

Inductive mytype (X:Type): Type :=
  | constr1 (x: X)
  | constr2 (n: nat)
  | constr3 (m: mytype X) (n: nat)
.

Check mytype_ind:
  forall (X: Type) (P: mytype X -> Prop),
    (forall x: X, P (constr1 X x)) ->
    (forall n: nat, P (constr2 X n)) ->
    (forall m: mytype X, P m ->
      forall n: nat, P (constr3 X m n)) ->
     forall m: mytype X, P m
.

Inductive foo (X Y: Type): Type :=
  | bar (x: X)
  | baz (y: Y)
  | quux (f1: nat -> foo X Y)
.

Check foo_ind:
  forall (X Y: Type) (P: foo X Y -> Prop),
    (forall x: X, P (bar X Y x)) ->
    (forall y: Y, P (baz X Y y)) ->
    (forall f1: nat -> foo X Y,
      (forall n: nat, P (f1 n)) -> P (quux X Y f1)) ->
     forall f2: foo X Y, P f2
.

Inductive foo' (X: Type): Type :=
  | c1 (l: list X) (f: foo' X)
  | c2
.

Check foo'_ind:
  forall (X: Type) (P: foo' X -> Prop),
    (forall (l: list X) (f: foo' X),
      P f -> P (c1 X l f)) ->
    (P (c2 X)) ->
    forall f: foo' X, P f
.

Definition P_m0r (n: nat): Prop :=
  n * 0 = 0.

Theorem mul_0_r'': forall n: nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n IHn.
    unfold P_m0r in *. apply IHn.
Qed.

Definition P_add_assoc' (n m p: nat): Prop :=
  n + (m + p) = (n + m) + p
.

Check nat_ind:
  forall P: nat -> Prop,
  P 0 -> (forall n: nat, P n -> P (S n)) -> forall n: nat, P n
.

Theorem add_assoc': forall n m p: nat, P_add_assoc' n m p.
Proof.
  intros n m p.
  apply (nat_ind (fun n => P_add_assoc' n m p)).
  - unfold P_add_assoc'. reflexivity.
  - clear n. intros n H. unfold P_add_assoc' in *. simpl.
    rewrite H. reflexivity.
Qed.

Definition P_add_comm'' (n m: nat): Prop :=
  n + m = m + n
.

Lemma add_0_r: forall n, n + 0 = n. Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_comm'': forall n m: nat, P_add_comm'' n m.
Proof.
  intros n m.
  apply (nat_ind (fun n => P_add_comm'' n m)).
  - unfold P_add_comm''. rewrite add_0_r. reflexivity.
  - clear n. intros n H. unfold P_add_comm'' in *. simpl.
    rewrite H. rewrite <- plus_n_Sm. reflexivity.
Qed.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n))
.

Check ev_ind:
  forall P: nat -> Prop,
    P 0 ->
    (forall n: nat, ev n -> P n -> P (S (S n))) ->
  forall n: nat, ev n -> P n
.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).
Theorem ev_ev' : forall n, ev n -> ev' n.
Proof.
  apply ev_ind.
  - (* ev_0 *)
    apply ev'_0.
  - (* ev_SS *)
    intros m Hm IH.
    apply (ev'_sum 2 m).
    + apply ev'_2.
    + apply IH.
Qed.


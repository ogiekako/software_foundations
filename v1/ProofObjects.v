Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Theorem ev_8: ev 8.
Proof.
  repeat apply ev_SS. apply ev_0.
Qed.
Print ev_8.

Definition ev_8': ev 8 := ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4' := 
fun (n : nat) (H : ev n) => ev_SS (S (S n)) (ev_SS n H).

Definition add1: nat -> nat.
intros n.
apply S.
apply n.
Defined.

Compute add1 2.

Module Props.

Module And.

Inductive and (P Q: Prop) : Prop :=
  | conj: P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

Theorem proj1': forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.

Lemma and_comm: forall P Q: Prop, P/\Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

End And.

Definition and_comm'_aux P Q (H: P/\Q): Q/\P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q: P/\Q <-> Q/\P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Definition conj_fact P Q R (HPQ: P/\Q) (HQR: Q/\R): P/\R :=
  match HPQ with
  | conj HP _ => match HQR with
    | conj _ HR => conj HP HR
    end
  end.

Module Or.

Inductive or (P Q: Prop): Prop :=
  | or_introl: P -> or P Q
  | or_intror: Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q): type_scope.

Definition inj_l: forall (P Q: Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.

Theorem inj_l': forall (P Q: Prop), P -> P \/ Q.
Proof.
  intros P Q HP. left. apply HP.
Qed.

Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.
Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
Qed.
End Or.

Definition or_commut': forall P Q, P \/ Q -> Q \/ P :=
  fun P Q HPQ =>
    match HPQ with
    | or_introl HP => or_intror HP
    | or_intror HQ => or_introl HQ
    end.

Module Ex.

Inductive ex {A: Type} (P: A -> Prop): Prop :=
  | ex_intro (x: A) (H: P x): ex P.

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.

End Ex.

Check ex (fun n => ev n): Prop.

Definition some_nat_is_even: exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Definition ex_ev_Sn: ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).

Inductive True: Prop :=
  | I: True.

Definition p_implies_true: forall P, P -> True :=
  fun p => (fun p => I).

Inductive False: Prop := .

Fail Definition contra: False := 0 = 1.

Definition false_implies_zero_eq_one: False -> 0 = 1 :=
  fun contra => match contra with end.

Definition ex_falso_quodlibet': forall P, False -> P :=
  fun p => fun contra => match contra with end.

End Props.

Module EqualityPlayground.

Inductive eq {X:Type}: X -> X -> Prop :=
  | eq_refl: forall x, eq x x.

Notation "x == y" := (eq x y)
                     (at level 70, no associativity): type_scope.

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[] :=
  fun (X:Type) (x:X) => eq_refl [x].

Definition eq_add : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2) :=
  fun n1 n2 Heq =>
    match Heq with
    | eq_refl n => eq_refl (S n)
    end.

Theorem eq_add' : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2).
Proof.
  intros n1 n2 Heq.
  Fail rewrite Heq.
  destruct Heq.
  Fail reflexivity.
  apply eq_refl.
Qed.

Definition eq_cons: forall (X:Type) (h1 h2: X) (t1 t2: list X),
  h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2 :=
  fun X h1 h2 t1 t2 Hheq Hteq => match Hheq with
  | eq_refl h => match Hteq with
    | eq_refl t => eq_refl (h :: t)
    end
  end.

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall (P : X -> Prop), P x -> P y.
Proof.
  intros X x y p P Px. destruct p. apply Px.
Qed.

Definition equality__leibniz_equality_term : forall (X : Type) (x y: X),
    x == y -> forall P : (X -> Prop), P x -> P y :=
  fun X x y Hxy => match Hxy with
    | eq_refl n => fun P Px => Px
    end
.

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
  intros. apply H. apply eq_refl.
Qed.

(* More Exercises *)
Definition and_assoc: forall P Q R: Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R :=
  fun P Q R HP_QR => match HP_QR with
  | conj HP HQR => match HQR with
    | conj HQ HR => conj (conj HP HQ) HR
    end
  end
.

Definition or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R) :=
    fun P Q R => conj (fun HP_QR => match HP_QR with
    | or_introl HP => conj (or_introl HP) (or_introl HP)
    | or_intror HQR => match HQR with
      | conj HQ HR => conj (or_intror HQ) (or_intror HR)
      end
    end
    ) (fun HPQ_PR => match HPQ_PR with
    | conj HPQ HPR => match HPQ with
      | or_introl HP => or_introl HP
      | or_intror HQ => match HPR with
        | or_introl HP => or_introl HP
        | or_intror HR => or_intror (conj HQ HR)
        end
      end
    end
    ).

Definition double_neg : forall P : Prop,
    P -> ~~P :=
    fun P HP HPF => HPF HP.

Definition contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q :=
    fun P Q HPNP => match HPNP with
    | conj HP HNP => match HNP HP with end
    end.

Definition de_morgan_not_or : forall P Q : Prop,
    ~(P \/ Q) -> ~P /\ ~Q :=
    fun P Q HN_PQ => conj
    (fun HP => HN_PQ (or_introl HP))
    (fun HQ => HN_PQ (or_intror HQ))
.

Definition curry : forall P Q R : Prop,
    ((P /\ Q) -> R) -> (P -> (Q -> R)) :=
    fun P Q R HPQ_R => (fun HP => (fun HQ => 
      HPQ_R (conj HP HQ)
    )).

Definition uncurry : forall P Q R : Prop,
    (P -> (Q -> R)) -> ((P /\ Q) -> R) :=
    fun P Q R HP_QR => (fun HPQ => match HPQ with
    | conj HP HQ => (HP_QR HP) HQ
    end
    )
.

(* Proof Irrelevance *)

Definition propositional_extensionality : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

Theorem pe_implies_or_eq:
  propositional_extensionality ->
  forall (P Q : Prop), (P \/ Q) = (Q \/ P).
Proof.
  intros. apply H. split. intros. destruct H0. right. apply H0. left. apply H0.
  intros. destruct H0. right. apply H0. left. apply H0.
Qed.

Lemma pe_implies_true_eq :
  propositional_extensionality ->
  forall (P : Prop), P -> True = P.
Proof.
  intros ex P HP. apply ex. split. intros. apply HP. intros. apply I.
Qed.

Definition proof_irrelevance : Prop :=
  forall (P : Prop) (pf1 pf2 : P), pf1 = pf2.

Theorem pe_implies_pi :
  propositional_extensionality -> proof_irrelevance.
Proof.
  intros ex. unfold proof_irrelevance. intros. apply (pe_implies_true_eq ex P)
  in pf1 as H. destruct H. destruct pf1, pf2. reflexivity.
Qed.

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
From Coq Require Export Lia.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0 (* evidence constructor. Type ev 0 can be created means ev 0 is provable. Has the same status as proven theorems. *)
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Check ev : nat -> Prop.
Check ev 0: Prop.
Check ev_0: ev 0.
Check ev_SS: forall n : nat, ev n -> ev (S (S n)).

Fail
Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).


Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed
.
Theorem ev_4' : ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)). Qed
.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed
.

Theorem ev_double : forall n,
  ev (double n).
Proof.
  induction n as [|n IHn].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed
.

Theorem ev_inversion :
  forall (n:nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - left. reflexivity.
  - right. exists n'. split. reflexivity. apply E'.
Qed.

Theorem ev_minus2 : forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed
.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E.
  (* E: ev (S (S n)) *)
  destruct E as [| n' E' ] eqn:EE.
  - (* E: ev 0. The term replaced S (S n)) is not mentioned anywhere. *)
Abort
.

Theorem evSS_ev_remember : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E.
  (* E: ev (S (S n)) *)
  remember (S (S n)) as k eqn:Hk.
  (* E: ev k *)
  destruct E as [| n' E' ] eqn:EE.
  - discriminate Hk.
  - injection Hk as Heq. rewrite <- Heq. apply E'.
Qed.

Check ev_inversion :
  forall (n:nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H.
  apply ev_inversion in H.
  destruct H as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq. rewrite Heq. apply Hev.
Qed
.

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  (* E: ev (S (S n)) *)

  (* | ev_SS (n : nat) (H : ev n) : ev (S (S n)). *)
  inversion E as [|n' (* nat *) H (* ev n *) Heq (* n' = n *)].
  apply H.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [| [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
  intros H. inversion H. Qed
.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. inversion H as [|n' H' E']. inversion H' as [|n'' H'' E''].
  apply H''. Qed
.

Theorem ev5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H. inversion H1. inversion H3.
Qed.

Theorem inversion_ex1 : forall n m o : nat,
  [n;m] = [o;o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed
.

Theorem inversion_ex2 : forall n : nat,
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra.
Qed.

Lemma ev_even_firsttry : forall n,
  ev n -> Even n.
Proof.
  intros n E. inversion E as [EQ' | n' E' EQ'].
  - exists 0. reflexivity.
  - simpl.
    generalize dependent E'.
Abort.

(* Induction on Evidence *)
Lemma ev_even : forall n,
  ev n -> Even n.
Proof.
  intros n E (* = ev n *).
  (* 
    E: ev n
    Goal: Even n 
  *)
  induction E as [
    (* E = ev_0 : ev 0. *)
      |
    (*
      The value (E : ev n) is destructed, together with the type parameter n.
      E = ev_SS n' (E':ev n') : ev (S (S n'))
      IH: Even n'  (* The goal for smaller type parameters can be assumed. *)
    *)
      n' E' IH
  ].
  - (* E = ev_0 *) exists 0. reflexivity.
  - unfold Even in IH. destruct IH as [k Hk].
    rewrite Hk. exists (S k). reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - apply ev_even.
  - unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m En Em. induction En as [|n' En' IHEn'].
  - simpl. apply Em.
  - simpl. apply ev_even_iff. apply ev_even_iff in IHEn'. destruct IHEn' as [k H]. exists (S k). simpl. rewrite H. reflexivity.
Qed.

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum n m (Hn : ev' n) (Hm: ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  - intros E. induction E as [].
    + apply ev_0.
    + apply (ev_SS 0 ev_0).
    + apply (ev_sum n m IHE1 IHE2).
  - intros E. induction E as [|n' E' IHE].
    + apply ev'_0.
    + apply (ev'_sum 2 n' ev'_2 IHE).
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m H1 H2.
  induction H2 as [|n' H2 IH2].
  - simpl in H1. apply H1.
  - apply IH2. simpl in H1. apply evSS_ev. apply H1.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p Hnm Hnp.
  assert (H: ev ((n+m) + (n+p))). {
    rewrite <- ev'_ev.
    rewrite <- ev'_ev in Hnm.
    rewrite <- ev'_ev in Hnp.
    apply (ev'_sum (n+m) (n+p) Hnm Hnp).
  }
  rewrite add_assoc in H. assert (H2: (double n) + (m + p) = n + m + n + p). {
    Check add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
    (*
      (n + n) + (m + p)
      ((n + n) + m) + p
      ((n + m) + n) + p
    *)
    rewrite double_plus. rewrite add_assoc.
    rewrite <- (add_assoc n m n). rewrite <- (add_assoc n n m).
    rewrite (add_comm n m).
    reflexivity.
  }
  rewrite <- H2 in H.
  apply (ev_ev__ev (double n) (m+p)).
  - apply H.
  - apply ev_double.
Qed.

Module Playground.

Inductive le : nat -> nat -> Prop :=
| le_n (n : nat) : le n n
| le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

Theorem test_le1 : 3 <= 3. Proof. apply (le_n 3). Qed
.
Theorem test_le2 : 3 <= 6. Proof.
  apply (le_S 3 5 (le_S 3 4 (le_S 3 3 (le_n 3)))).
Qed
.
Theorem test_le3 : 2 <= 1 -> 2 + 2 = 5. Proof.
  intros H. inversion H. inversion H2.
Qed
.


Definition lt (n m : nat) := le (S n) m.
Notation "m < n" := (lt m n).

End Playground.

Inductive square_of : nat -> nat -> Prop :=
| sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
| nn n : next_nat n (S n).

Inductive next_ev : nat -> nat -> Prop :=
| ne_1 n (H:ev (S n)) : next_ev n (S n)
| ne_2 n (H:ev (S (S n))) : next_ev n (S (S n)).

(* Exercises *)
Inductive total_relation : nat -> nat -> Prop :=
| tot n m : total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .


Theorem O_le_n : forall n, O <= n.
Proof.
  induction n as [|n' IHn].
  - apply (le_n 0).
  - apply (le_S 0 n' IHn).
Qed.

(* 
Definition lt (n m : nat) := le (S n) m.
Notation "m < n" := (lt m n).
*)
Lemma lt_le : forall n m,
  n < m -> n <= m. (*  S n <= m -> n <= m  *)
Proof.
  induction n.
  - intros. apply O_le_n.
  - intros m H. induction H.
    + apply le_S, le_n.
    + apply le_S, IHle.
Qed.

Theorem n_le_m___Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m' H.
  induction H.
  - apply (le_n (S n)).
  - apply (le_S (S n) (S m) IHle).
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m' H.
  inversion H.
  - apply (le_n (m')).
  - apply (lt_le _ _ H1).
Qed
.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2.
  induction H1 as[|n' E1 IH1].
  - apply H2.
  - apply IH1. apply lt_le. apply H2.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction a.
  - simpl. apply O_le_n.
  - rewrite plus_Sn_m. apply (n_le_m___Sn_le_Sm _ _ IHa).
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m -> n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m H1.
  split.
  - assert (H2: n1 <= n1 + n2). { apply le_plus_l. }
    apply (le_trans _ _ _ H2 H1).
  - assert (H2: n2 <= n1 + n2). { rewrite add_comm. apply le_plus_l. }
    apply (le_trans _ _ _ H2 H1).
Qed.

Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  induction n as [| n IHn].
  - intros m p q H. left. apply O_le_n.
  - intros m p q H.
    rewrite plus_Sn_m, add_comm, <-plus_Sn_m, add_comm in H.
    destruct p.
    + right. simpl in H. assert (H2: m <= n + S m). {
      rewrite add_comm, plus_Sn_m, add_comm, <-plus_Sn_m, add_comm. apply le_plus_l.
    }
    apply (le_trans _ _ _ H2 H).
    + rewrite plus_Sn_m, (add_comm p q), <- plus_Sn_m, (add_comm (S q) p) in H.
      apply IHn in H. destruct H.
      * left. apply n_le_m___Sn_le_Sm. apply H.
      * right. apply Sn_le_Sm__n_le_m. apply H.
Qed.

Theorem lt_S : forall n m,
  n < m -> n < S m.
Proof.
  unfold lt.
  intros n m H. apply (le_trans _ _ _ H (le_S _ _ (le_n m))).
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros n1 n2 m H.
  split.
  - assert (H2: S n1 <= S (n1 + n2)). {
    apply n_le_m___Sn_le_Sm. apply le_plus_l.
  }
    apply (le_trans _ _ _ H2 H).
  - assert (H2: S n2 <= S (n1 + n2)). {
    apply n_le_m___Sn_le_Sm. rewrite add_comm. apply le_plus_l.
  }
    apply (le_trans _ _ _ H2 H).
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  induction n as [|n IHn].
  - intros m H. apply O_le_n.
  - intros m H. destruct m.
    + discriminate H.
    + simpl in H. apply IHn in H. apply n_le_m___Sn_le_Sm, H.
Qed.

Theorem leb_correct : forall n m,
  n <= m -> n <=? m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  - intros. inversion H. reflexivity.
  - intros n H. destruct n.
    + reflexivity.
    + simpl. apply IHm. apply (Sn_le_Sm__n_le_m _ _ H).
Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o H1 H2.
  apply leb_correct. apply leb_complete in H1. apply leb_complete in H2.
  apply (le_trans _ _ _ H1 H2).
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Module R.

Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H: R m n o) : R (S m) n (S o)
  | c3 m n o (H: R m n o) : R m (S n) (S o)
  | c4 m n o (H: R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H: R m n o) : R n m o
.

Definition fR : nat -> nat -> nat
  := (fun x => (fun y => x + y)).

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  unfold fR.
  split.
  - intros H. induction H.
    + reflexivity.
    + rewrite plus_Sn_m. rewrite IHR. reflexivity.
    + rewrite <- plus_n_Sm. rewrite IHR. reflexivity.
    + rewrite plus_Sn_m in IHR. injection IHR as IHR. rewrite <- plus_n_Sm in IHR. injection IHR as IHR. apply IHR.
    + rewrite add_comm. apply IHR.
  - generalize dependent m. generalize dependent n. generalize dependent o.
    induction o.
    + intros n m H. apply Plus.plus_is_O in H. destruct H as [H1 H2]. rewrite H1, H2. apply c1.
    + induction n.
      * intros m H. rewrite add_comm in H. simpl in H. rewrite H. 
        assert (H2: R o 0 o). {
          apply IHo. rewrite add_comm. reflexivity.
        }
        apply (c2 _ _ _ H2).
      * intros m H.
        assert (H2: R m n o). {
          apply IHo.
          rewrite <- plus_n_Sm in H. injection H as H. apply H.
        }
        apply (c3 _ _ _ H2).
Qed.

End R.

Module SubseqExercise.

Inductive prefseq {T}: list T -> list T -> Prop :=
| pref_nil (l : list T) : prefseq [] l
| pref_add (x : T) (l1 l2 : list T) (H : prefseq l1 l2): prefseq (x::l1) (x::l2)
.

(* Wrong definition!! *)
Inductive subseq {T}: list T -> list T -> Prop :=
| subseq_pref (l1 l2 : list T) (H: prefseq l1 l2): subseq l1 l2
| subseq_add (x : T) (l1 l2 : list T) (H: subseq l1 l2): subseq l1 (x::l2)
.

Theorem prefseq_refl : forall l : list nat, prefseq l l.
Proof.
  induction l.
  - apply pref_nil.
  - apply pref_add. apply IHl.
Qed.

Theorem subseq_refl : forall l : list nat, subseq l l.
  intros l.
Proof.
  apply subseq_pref, prefseq_refl.
Qed
.

Theorem subseq_nil : forall l : list nat, subseq [] l.
Proof. induction l. apply subseq_pref, pref_nil. apply subseq_add, IHl. Qed
.

Lemma cons_app : forall T (x : T) (l : list T),
  x :: l = [x] ++ l.
Proof.
  intros T x l. reflexivity.
Qed
.

Theorem subseq_exists_prefseq : forall l1 l2 : list nat,
  subseq l1 l2 -> exists l3 l4 : list nat, prefseq l1 l4 /\ l3 ++ l4 = l2.
Proof.
  intros l L Hsubseq.
  induction Hsubseq as [l L Hpref|x l L' Hsubseq [L1' [L2' [IH1 IH2]]]].
  - exists nil, L. split. apply Hpref. reflexivity.
  - assert (H: subseq l (x :: L')). {
    apply subseq_add, Hsubseq.
  }
    exists (x::L1'), L2'. split. apply IH1. rewrite cons_app, <- app_assoc, <- cons_app. rewrite IH2. reflexivity.
Qed.

Theorem prefseq_app : forall l1 l2 l3 : list nat,
  prefseq l1 l2 -> prefseq l1 (l2 ++ l3).
Proof.
  induction l1 as [|x l IH].
  - intros L App H. apply pref_nil.
  - intros L App Hpref. inversion Hpref as [|x' l' L' Hx HxLL]. simpl.
    apply pref_add. apply IH. apply Hx.
Qed.

Theorem prefseq_app_exists : forall l1 l2 L : list nat,
  prefseq (l1 ++ l2) L -> exists L' : list nat, prefseq l2 L' /\
    l1 ++ L' = L.
Proof.
  induction l1 as [|x l IH].
  - intros. exists L. split. apply H. reflexivity.
  - intros. simpl in H. inversion H. simpl. apply IH in H3. destruct H3 as [L'' []]. exists L''. split. apply H3. rewrite H4. reflexivity.
Qed.

Theorem prefseq_subseq : forall l1 l2 : list nat,
  prefseq l1 l2 -> forall l3 : list nat, subseq l1 (l3 ++ l2).
Proof.
  intros l1 l2. induction l3.
  - simpl. apply subseq_pref. apply H.
  - apply subseq_add, IHl3.
Qed.

Theorem subseq_app : forall l1 l2 l3 : list nat,
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros l L App H. apply subseq_exists_prefseq in H. destruct H as [L1 [L2 [H1 H2]]]. assert (Hpref: prefseq l (L2 ++ App)). {
    apply prefseq_app, H1.
  }
  rewrite <- H2. rewrite <-app_assoc. apply prefseq_subseq, Hpref.
Qed.

Theorem prefseq_iff : forall l1 l2 : list nat,
  prefseq l1 l2 <-> exists l3, l1 ++ l3 = l2.
Proof.
  split.
  - intros H. induction H.
    + exists l. reflexivity.
    + simpl. destruct IHprefseq. exists x0. rewrite H0. reflexivity.
  - generalize dependent l2. generalize dependent l1. induction l1.
    + intros l2. intros H. apply pref_nil.
    + simpl. intros l2 H. destruct H as [l3 H]. rewrite <- H. apply pref_add. apply IHl1. exists l3. reflexivity.
Qed.

Lemma app_nil_nil : forall T (l1 l2 : list T), l1 ++ l2 = nil -> l1 = nil /\ l2 = nil.
Proof. intros T l1 l2 H. destruct l1.
  - split. reflexivity. destruct l2. reflexivity. simpl in H. discriminate H.
  - simpl in H. discriminate H.
Qed.

Theorem subseq_iff : forall l1 l2 : list nat,
  subseq l1 l2 <-> exists l3 l4, l3 ++ l1 ++ l4 = l2.
Proof.
  split.
  - generalize dependent l1. induction l2.
    + intros l1 H. exists [], []. inversion H. inversion H0. reflexivity.
    + intros l1 H. inversion H.
      * apply prefseq_iff in H0. destruct H0 as [l3']. exists nil, l3'. rewrite H0. reflexivity.
      * apply IHl2 in H2. destruct H2 as [l3' [l4' H2]]. exists (x::l3'), l4'. rewrite <- H2. reflexivity.
  - generalize dependent l1. induction l2.
    + intros l1 H. destruct H as [l3 [l4 H]]. apply app_nil_nil in H. destruct H. apply app_nil_nil in H0. destruct H0. rewrite H0. apply subseq_pref, pref_nil.
    + intros l1 H. destruct H as [l3 [l4 H]]. destruct l3.
      * simpl in H. apply subseq_pref. apply prefseq_iff. exists l4. apply H.
      * simpl in H. injection H as []. apply subseq_add. apply IHl2. exists l3, l4. apply H.
Qed.

Theorem subseq_trans : forall l1 l2 l3 : list nat,
  subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros l1 l2 l3 H1 H2.
  apply subseq_iff in H1. apply subseq_iff in H2.
  destruct H1 as [l1_l [l1_r H1]].
  destruct H2 as [l2_l [l2_r H2]].
  rewrite <- H2. rewrite <- H1. apply subseq_iff. exists (l2_l ++ l1_l), (l1_r ++ l2_r).
  rewrite <- app_assoc. rewrite (app_assoc _ l1 l1_r l2_r).
  rewrite (app_assoc _ l1_l (l1 ++ l1_r) l2_r). reflexivity.
Qed.

End SubseqExercise.

Inductive reg_exp (T : Type) : Type :=
  | EmptySet (* No match *)
  | EmptyStr (* Matches the empty string [] *)
  | Char (t : T) (* Mathes [t] *)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T)
.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2 (H1 : s1 =~ re1) (H2 : s2 =~ re2)
      : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2 (H1 : s1 =~ re1) : s1 =~ (Union re1 re2)
  | MUnionR s1 re1 re2 (H2 : s1 =~ re2) : s1 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re (H1 : s1 =~ re) (H2 : s2 =~ (Star re))
      : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Lemma quiz : forall T (s:list T), ~(s =~ EmptySet).
Proof. intros T s Hc. inversion Hc. Qed
.

Example re_exp_ex1 : [1] =~ Char 1.
Proof. apply (MChar 1). Qed
.

Example re_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof. apply (MApp [1] (Char 1) [2] (Char 2) (MChar 1) (MChar 2)). Qed
.

Example reg_exp_ex3 : ~ ([1;2] =~ Char 1).
Proof. intros H. inversion H. Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end
.

Example reg_exp_ex4 : [1 ; 2 ; 3 ] =~ reg_exp_of_list [1;2;3].
Proof. apply (MApp [1]). apply MChar. apply (MApp [2]). apply MChar.
  apply (MApp [3]). apply MChar. apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : reg_exp T), s =~ re -> s =~ Star re.
Proof.
  intros T s re H. replace s with (s ++ nil). apply MStarApp. apply H. apply MStar0. apply app_nil_r.
Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H. inversion H.
Qed
.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 -> s =~ Union re1 re2.
Proof.
  intros T s re1 re2 H. destruct H as [H|H].
  - apply MUnionL, H.
  - apply MUnionR, H.
Qed
.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H. induction ss.
  - simpl. apply MStar0.
  - simpl. assert (H0: x =~ re). { apply H. simpl. left. reflexivity. }
    apply MStarApp. { apply H0. } apply IHss. intros s H2. apply H. simpl. right. apply H2.
Qed
.

Lemma reg_exp_of_list__spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  split.
  - generalize dependent s1. induction s2.
    + intros l H. simpl in H. inversion H. reflexivity.
    + intros l H. simpl in H. inversion H. inversion H3. simpl. replace s0 with s2.
      reflexivity.
      apply IHs2 in H4. symmetry. apply H4.
  - generalize dependent s1. induction s2.
    + intros s1 H. simpl. rewrite H. apply MEmpty.
    + intros s1 H. simpl. rewrite H. apply (MApp [x]). apply (MChar x). apply IHs2. reflexivity.
Qed.

Fixpoint re_chars {T} (re :reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end
.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re -> In x s -> In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [ | x'
    | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
    | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
    | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - simpl in Hin. destruct Hin.
  - simpl. simpl in Hin. apply Hin.
  - simpl. rewrite In_app_iff in *. destruct Hin as [Hin|Hin].
    + left. apply IH1, Hin.
    + right. apply IH2, Hin.
  - simpl. rewrite In_app_iff. left. apply IH, Hin.
  - simpl. rewrite In_app_iff. right. apply IH, Hin.
  - destruct Hin.
  - simpl. rewrite In_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply IH1, Hin.
    + apply IH2, Hin.
Qed
.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => (re_not_empty re1) && (re_not_empty re2)
  | Union re1 re2 => (re_not_empty re1) || (re_not_empty re2)
  | Star re => true
  end
.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split.
  - intros H. destruct H as [s H]. generalize dependent s. induction re.
    + intros s H. inversion H.
    + intros s H. reflexivity.
    + intros s H. reflexivity.
    + intros s H. simpl. inversion H. apply IHre1 in H3. apply IHre2 in H4. rewrite H3, H4. reflexivity.
    + intros s H. simpl. inversion H.
      * apply IHre1 in H2. rewrite H2. reflexivity.
      * apply IHre2 in H1. rewrite H1. destruct (re_not_empty re1). reflexivity. reflexivity.
    + intros s H. simpl. reflexivity.
  - intros H. induction re.
    + discriminate H.
    + exists nil. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply IHre1 in H1. apply IHre2 in H2. destruct H1 as [s1], H2 as [s2]. exists (s1 ++ s2). apply MApp. apply H. apply H0.
    + simpl in H. apply orb_true_iff in H. destruct H as [H|H].
      * apply IHre1 in H. destruct H as [s]. exists s. apply MUnionL. apply H.
      * apply IHre2 in H. destruct H as [s]. exists s. apply MUnionR. apply H.
    + exists []. apply MStar0.
Qed.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].  
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - injection Heqre' as Heqre''. intros s H. apply H.
  - injection Heqre' as Heqre''. intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite Heqre''. reflexivity.
      * apply H1.
Qed
.

Lemma Mstar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re -> exists ss : list (list T),
    s = fold app ss [] /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H. remember (Star re) as re'.
  induction H.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists nil. split. reflexivity. intros s' H. inversion H.
  - injection Heqre' as Hr. rewrite Hr in *. assert (EQsr : Star re = Star re). { reflexivity. }
    apply IHexp_match2 in EQsr. destruct EQsr as [ss [H1 H2]].
  exists (s1 :: ss). simpl. rewrite H1. split. reflexivity.
    intros s' H'. destruct H'.
    + rewrite <- H3. apply H.
    + apply H2, H3.
Qed.

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 => pumping_constant re1 + pumping_constant re2
  | Union re1 re2 => pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end
.

Lemma pumping_constant_ge_1 : forall T (re : reg_exp T), pumping_constant re >= 1.
Proof.
  Check le_trans : forall m n o : nat, m <= n -> n <= o -> m <= o.
  intros T re. induction re.
  - apply le_n.
  - apply le_n.
  - apply le_S, le_n.
  - simpl. apply le_trans with (n := pumping_constant re1). apply IHre1. apply le_plus_l.
  - simpl. apply le_trans with (n := pumping_constant re1). apply IHre1. apply le_plus_l.
  - simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false : forall T (re : reg_exp T),
  pumping_constant re = 0 -> False.
Proof.
  intros T re H. assert (Hp1 : pumping_constant re >= 1). { apply pumping_constant_ge_1. }
  inversion Hp1.
  - rewrite H in H1. discriminate.
  - rewrite H in H0. discriminate.
Qed.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | O => nil
  | S n' => l ++ napp n' l
  end
.

Lemma napp_plus : forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m  l.
Proof.
  induction n.
  - intros. reflexivity.
  - intros m l. simpl. rewrite <- app_assoc. rewrite <- IHn. reflexivity.
Qed.

Lemma napp_star : forall T m s1 s2 (re : reg_exp T),
  s1 =~ re -> s2 =~ Star re -> napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2. induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc. apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed
.

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re -> pumping_constant re <= length s -> exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\ s2 <> nil /\ forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
intros T re s Hmatch.
induction Hmatch as [
  | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
  | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
  | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
- simpl. intros contra. inversion contra.
- simpl. intros contra. inversion contra. inversion H0.
- (* MApp *) simpl. intros Hle. rewrite app_length in Hle.
apply add_le_cases in Hle. destruct Hle as [Hle|Hle].
  + apply IH1 in Hle. destruct Hle as [s3 [s4 [s5 [H1 [H2 H3]]]]]. exists s3, s4, (s5++s2). split.
    * rewrite H1. rewrite <- app_assoc, <- app_assoc. reflexivity.
    * split. apply H2. intros m. rewrite app_assoc. rewrite app_assoc. apply MApp.
      ** rewrite <- app_assoc. apply H3.
      ** apply Hmatch2.
  + apply IH2 in Hle. destruct Hle as [s3 [s4 [s5 [H1 [H2 H3]]]]].
  exists (s1++s3), s4, s5. split.
    * rewrite H1. rewrite app_assoc. reflexivity.
    * split. apply H2. intros m. rewrite <- app_assoc. apply MApp.
      ** apply Hmatch1.
      ** apply H3.
- (* MUnionL *) simpl. intros Hle. apply plus_le in Hle. destruct Hle as [Hle1 Hle2]. apply IH in Hle1. destruct Hle1 as [s2 [s3 [s4 [H1 [H2 H3]]]]]. exists s2, s3, s4. split. apply H1. split.
  + apply H2.
  + intros m. apply MUnionL. apply H3.
- (* MUnionR *) simpl. intros Hle. apply plus_le in Hle. destruct Hle as [Hle1 Hle2]. apply IH in Hle2. destruct Hle2 as [s1 [s3 [s4[H1 [H2 H3]]]]]. exists s1, s3, s4. split. apply H1. split. apply H2. intros m. apply MUnionR. apply H3.
- (* MStar0 *) simpl. intros contra. inversion contra. apply pumping_constant_0_false in H0. destruct H0.
- (* MStarApp *) simpl. intros Hle. rewrite app_length in Hle.
  destruct s1.
  + (* s1 = [] *) simpl in *. apply IH2 in Hle. destruct Hle as [s1 [s3 [s4 [H1 [H2 H3]]]]]. exists s1, s3, s4. split. apply H1. split. apply H2. apply H3.
  + (* s1 <> [] *) exists nil, (x::s1), s2. split. reflexivity. split. discriminate. intros m. simpl. apply napp_star. apply Hmatch1. apply Hmatch2.
Qed.

Lemma le_plus_trans : forall n m p : nat, n <= m -> n <= m + p.
Proof.
  induction p.
  - rewrite add_comm. simpl. intros H. apply H.
  - intros H. apply IHp in H. rewrite <- plus_n_Sm. apply le_S. apply H.
Qed.

Lemma plus_le_compat : forall n m p q : nat, n <= m -> p <= q -> n + p <= m + q.
Proof.
  intros n m p q H1. induction H1.
  - intros H2. apply leb_iff. induction n. simpl. apply <- leb_iff. apply H2. simpl. apply IHn.
  - intros H2. apply IHle in H2. simpl. apply le_S. apply H2.
Qed.

Lemma leb_false_ltb : forall n m : nat, n <=? m = false -> m <? n = true.
Proof.
  induction n.
  - discriminate.
  - intros m. induction m.
    + intros H. reflexivity.
    + simpl. apply IHn.
Qed.

Lemma ltb_leb : forall n m : nat, n <? m = true -> n <=? m = true.
Proof.
  induction n.
  - intros m H. reflexivity.
  - intros m H. induction m.
    + discriminate H.
    + simpl. apply IHn. simpl in H. apply H.
Qed.

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re -> pumping_constant re <= length s -> exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\ s2 <> [] /\ length s1 + length s2 <= pumping_constant re /\ forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch as [
    | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
    | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
    | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - simpl. intros contra. inversion contra.
  - simpl. intros contra. inversion contra. inversion H0.
  - (* MApp *) simpl. intros Hle. rewrite app_length in Hle.
  apply add_le_cases in Hle. destruct Hle as [Hle|Hle].
    + apply IH1 in Hle. destruct Hle as [s3 [s4 [s5 [H1 [H2 [H3 H4]]]]]]. exists s3, s4, (s5++s2). split.
      * rewrite H1. rewrite <- app_assoc, <- app_assoc. reflexivity.
      * split. apply H2. split. 
        ** apply le_plus_trans. apply H3.
        ** intros m. rewrite app_assoc, app_assoc. apply MApp. rewrite <- app_assoc. apply H4. apply Hmatch2.
    + apply IH2 in Hle. destruct Hle as [s3 [s4 [s5 [H1 [H2 [H3 H4]]]]]]. destruct (length s1 <=? pumping_constant re1) eqn:E.
      * (* length s1 <= pumping_constant re1 *) exists (s1++s3), s4, s5. split. rewrite H1. rewrite app_assoc. reflexivity. split. apply H2. split. rewrite app_length. rewrite <- add_assoc. apply leb_iff in E. apply plus_le_compat. apply E. apply H3. intros m. rewrite <- app_assoc. apply MApp. apply Hmatch1. apply H4.
      * (* pumping_constant re1 < length s1 *) apply leb_false_ltb in E. apply ltb_leb in E. apply leb_iff in E. apply IH1 in E. destruct E as [s6 [s7 [s8 [H5 [H6 [H7 H8]]]]]]. exists s6, s7, (s8 ++ s2). split. rewrite H5. rewrite <- app_assoc, <- app_assoc. reflexivity. split. apply H6. split. apply le_plus_trans. apply H7. intros m. rewrite app_assoc, app_assoc. apply MApp. rewrite <- app_assoc. apply H8. apply Hmatch2.
  - (* MUnionL *) simpl. intros Hle. apply plus_le in Hle. destruct Hle as [Hle1 Hle2]. apply IH in Hle1. destruct Hle1 as [s2 [s3 [s4 [H1 [H2 [H3 H4]]]]]]. exists s2, s3, s4. split. apply H1. split. apply H2. split. apply le_plus_trans. apply H3. intros m. apply MUnionL. apply H4.

  - (* MUnionR *) simpl. intros Hle. apply plus_le in Hle. destruct Hle as [Hle1 Hle2]. apply IH in Hle2. destruct Hle2 as [s1 [s3 [s4 [H1 [H2 [H3 H4]]]]]]. exists s1, s3, s4. split. apply H1. split. apply H2. split. rewrite (add_comm (pumping_constant s2)). apply le_plus_trans. apply H3. intros m. apply MUnionR. apply H4.

  - simpl. intros contra. inversion contra. 
    apply pumping_constant_0_false in H0. destruct H0.

  - (* MStarApp *) simpl. intros Hle. rewrite app_length in Hle.
    destruct s1.
    + (* s1 = [] *) simpl in *. apply IH2 in Hle. destruct Hle as [s1 [s3 [s4 [H1 [H2 [H3 H4]]]]]]. exists s1, s3, s4. split. apply H1. split. apply H2. split. apply H3. apply H4.
    + (* s1 <> [] *) destruct (pumping_constant re <=? length (x :: s1)) eqn:E.
      * apply leb_iff in E. apply IH1 in E. destruct E as [s3 [s4 [s5 [H1 [H2 [H3 H4]]]]]]. exists s3, s4, (s5 ++ s2). split. rewrite H1. rewrite <- app_assoc, <- app_assoc. reflexivity. split. apply H2. split. apply H3. intros m. rewrite app_assoc, app_assoc. apply MStarApp. rewrite <- app_assoc. apply H4. apply Hmatch2.
      * apply leb_false_ltb in E. apply ltb_leb in E. apply leb_iff in E. exists nil, (x::s1), s2. split. reflexivity. split. discriminate. split. apply E. intros m. simpl. apply napp_star. apply Hmatch1. apply Hmatch2.
Qed.

End Pumping.

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] -> In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (n =? m) eqn:H.
    + intros _. rewrite eqb_eq in H. rewrite H. left. reflexivity.
    + intros H'. right. apply IHl'. apply H'.
Qed.  
Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ~P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. inversion H.
  - split. intros p. reflexivity. intros p. apply H0.
  - split. 
    + intros p. apply H0 in p. destruct p.
    + intros p. discriminate p.
Qed.

Lemma eqbP : forall n m , reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] -> In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (eqbP n m) as [H|H].
    + intros _. rewrite H. left. reflexivity.
    + intros H'. right. apply IHl'. apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end
.

Theorem eqbP_practice : forall n l, count n l = 0 -> ~(In n l).
Proof.
  intros n. induction l.
  - simpl. intros H1 H2. destruct H2.
  - simpl. destruct (eqbP n x) as [H|H].
    + rewrite H in *. intros H1. discriminate H1.
    + simpl. intros H1 [H2|H2].
      * unfold not in H. symmetry in H2. apply H in H2. destruct H2.
      * apply IHl in H1. destruct (H1 H2).
Qed.

Inductive nostutter {X:Type} : list X -> Prop :=
  | nost_nil : nostutter nil
  | nost_one x : nostutter [x]
  | nost_add x y z (H: nostutter (y::z)) (N: x<>y): nostutter (x::y::z)
.

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. apply nost_add. apply nost_add. apply nost_add. apply nost_add. apply nost_add. apply nost_one. discriminate. discriminate. discriminate. discriminate. discriminate. Qed
.

Example test_nostutter_1': nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply eqb_neq; auto. Qed
.
Example test_nostutter_2: nostutter (@nil nat).
Proof. repeat constructor; apply eqb_neq; auto. Qed
.
Example test_nostutter_3: nostutter [5].
Proof. repeat constructor; auto. Qed
.
Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof. intro. repeat match goal with h: nostutter _ |- _ => inversion h; clear h; subst
end. contradiction; auto.
Qed.

Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  | merge_nil : merge nil nil nil
  | merge_left x l1 l2 l (H: merge l1 l2 l) : merge (x::l1) l2 (x::l)
  | merge_right x l1 l2 l (H: merge l1 l2 l) : merge l1 (x::l2) (x::l)
.

Theorem filter_challenge: forall (X:Type) (test: X->bool) (l l1 l2: list X),
  merge l1 l2 l -> (forall x: X, (In x l1) -> test x = true) -> (forall x:X, (In x l2) -> test x = false) -> filter test l = l1.
Proof.
  intros X test l l1 l2 Hmerge. induction Hmerge as [
    |x' l1 l2 l H IH|x' l1 l2 l H IH
  ].
  - intros H1 H2. reflexivity.
  - (* merge_left *) intros H1 H2. simpl in *. assert (Ht: test x' = true). {
    apply H1. left. reflexivity.
  } rewrite Ht. assert (HA: forall x : X, In x l1 -> test x = true). {
    intros H1' H2'. apply H1. right. apply H2'.
  } rewrite (IH HA H2). reflexivity.
  - intros H1 H2. simpl in *. assert (Ht: test x' = false). { apply H2. left. reflexivity. }
    rewrite Ht. assert (HA: forall x : X, In x l2 -> test x = false). { intros H1' H2'. apply H2. right. apply H2'. }
    rewrite (IH H1 HA). reflexivity.
Qed.

Inductive subseq {T}: list T -> list T -> Prop :=
| subseq_nil : subseq nil nil
| subseq_addr (x:T) (l1 l: list T) (H: subseq l1 l): subseq l1 (x::l)
| subseq_addb (x:T) (l1 l: list T) (H: subseq l1 l): subseq (x::l1) (x::l)
.

Theorem filter_challenge_2: forall (X:Type) (test: X->bool) (l l1:list X),
  (subseq l1 l) /\ (forall x:X, In x l1 -> test x = true)
  -> length l1 <= length (filter test l).
Proof.
  intros X test l l1 [H1 H2]. induction H1 as [|x' l1 l H IH|x' l1 l H IH].
  - simpl. apply le_n.
  - simpl. apply IH in H2. destruct (test x') eqn:E.
    + simpl. apply le_S. apply H2.
    + simpl. apply H2.
  - assert (Ht: test x' = true). { apply H2. left. reflexivity. }
    simpl. rewrite Ht. simpl. apply leb_iff. simpl. apply <- leb_iff. apply IH. intros x'' H''. apply H2. right. apply H''.
Qed.

Inductive pal {T}: list T -> Prop :=
  | pal_nil : pal nil
  | pal_one (x:T) : pal [x]
  | pal_add (x:T) (l: list T) (H: pal l) : pal ((x::l) ++ [x])
.

Lemma cons_app_assoc: forall T (x:T) (l1 l2:list T),
  x::l1 ++ l2 = (x::l1) ++ l2.
Proof.
  intros T x l1 l2. simpl. reflexivity.
Qed.

Theorem pal_app_rev: forall T (l:list T), pal (l ++ rev l).
Proof.
  intros T. induction l.
  - simpl. apply pal_nil.
  - simpl. rewrite app_assoc. apply pal_add. apply IHl.
Qed.

Theorem pal_rev: forall T (l:list T), pal l -> l = rev l.
Proof.
  intros T l H. induction H as [|x|x l H IH].
  - reflexivity.
  - reflexivity.
  - rewrite rev_app_distr. simpl. rewrite <- IH. reflexivity.
Qed
.

Lemma length_0_iff_nil: forall T (l:list T), length l = 0 <-> l = nil.
Proof.
  intros T l. split.
  - intros H. destruct l. reflexivity. simpl in H. inversion H.
  - intros H. rewrite H. reflexivity.
Qed.

Lemma pal_converse': forall T (n: nat) (l:list T), length l <= n -> l = rev l -> pal l.
Proof.
  intros T n. induction n as [|n IH].
  - intros l Hn Hl. inversion Hn as [Hn'|]. apply length_0_iff_nil in Hn'. rewrite Hn'. apply pal_nil.
  - intros l Hn Hl. destruct l as [|x l]. apply pal_nil. simpl in *.
      destruct (rev l) as [|x' rl'] eqn:E.
      + rewrite Hl. apply pal_one.
      + injection Hl as Hx. rewrite H. apply pal_add.
        assert (Hl: length rl' <= n). {
          apply leb_iff in Hn. simpl in Hn. apply leb_iff in Hn.
          rewrite H in Hn. rewrite app_length in Hn. simpl in Hn. rewrite add_comm in Hn. simpl in Hn.
          apply Le.le_Sn_le. apply Hn.
        }
        assert (Hr: rl' = rev rl'). {
          rewrite <- Hx in *. rewrite H in E. rewrite rev_app_distr in E. simpl in E. injection E as E. symmetry. apply E.
        }
        apply IH. apply Hl. apply Hr.
Qed.

Theorem pal_converse: forall T (l:list T), l = rev l -> pal l.
Proof.
  intros T l H. apply pal_converse' with (n := length l). apply le_n. apply H.
Qed.

Inductive disjoint {X}: (list X) -> (list X) -> Prop :=
  | disj_nil: disjoint nil nil
  | disj_l (x:X) (l1 l2:list X) (H: disjoint l1 l2) (HI: ~(In x l2)) : disjoint (x::l1) l2
  | disj_r (x:X) (l1 l2:list X) (H: disjoint l1 l2) (HI: ~(In x l1)) : disjoint l1 (x::l2)
.

Example disjoint_example1: disjoint [1;2] [3;4]. Proof.
  repeat constructor; auto.
  - unfold not. simpl. intros [|[]]. discriminate H. discriminate H. apply H.
  - unfold not. simpl. intros [|[]]. discriminate H. discriminate H. apply H.
Qed.

Inductive NoDup {X}: list X -> Prop :=
  | nodup_nil: NoDup nil
  | nodup_add (x:X) (l:list X) (H:NoDup l) (HI: ~(In x l)) : NoDup (x::l)
.

Lemma app_nil_iff {X}: forall (l1 l2 : list X), l1 ++ l2 = nil <-> l1 = nil /\ l2 = nil.
Proof. intros l1 l2. split. intros H. destruct l1. simpl in H. split. reflexivity. apply H. discriminate H.
  intros []. rewrite H, H0. reflexivity. Qed
.

Lemma disjoint_nil_l {X}: forall l:list X, disjoint nil l.
Proof. induction l. apply disj_nil. apply disj_r. apply IHl. simpl. unfold not. intros. apply H. Qed
.

Theorem app_no_dup_disjoint: forall X (l1 l2: list X),
  NoDup (l1 ++ l2) -> disjoint l1 l2.
Proof.
  intros X l1.
  induction l1 as [|x' l1].
  - intros l2 H. apply disjoint_nil_l.
  - intros l2 H. simpl in *. inversion H. apply IHl1 in H1. apply disj_l. apply H1. unfold not in *. intros. apply HI. apply In_app_iff. right. apply H3.
Qed.

Lemma in_split: forall (X:Type) (x:X) (l:list X), In x l -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l H. induction l.
  - inversion H.
  - inversion H.
    + exists nil, l. rewrite H0. reflexivity.
    + apply IHl in H0. destruct H0 as [l1 [l2 H']]. exists (x0::l1), l2. rewrite H'. reflexivity.
Qed
.

Inductive repeats {X:Type}: list X -> Prop :=
  | repeats_base (x:X) : repeats [x;x]
  | repeats_ins (l1:list X) (x:X) (l2:list X) (H: repeats (l1 ++ l2))  : repeats (l1 ++ [x] ++ l2)
.

Theorem pigeonhole_principle : forall (X:Type) (l1 l2: list X),
  (forall x, In x l1 -> In x l2) ->
    length l2 < length l1 -> repeats l1.
Proof.
  intros X l1.
  Admitted. (* TODO: prove this. *)

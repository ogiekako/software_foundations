Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
From Coq Require Export Lia.

Fixpoint div2(n:nat):=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition f(n:nat):=
  if even n then div2 n
  else (3 * n) + 1.

Inductive reaches_1: nat -> Prop :=
  | term_done: reaches_1 1
  | term_more (n:nat) : reaches_1 (f n) -> reaches_1 n.

Conjecture collatz: forall n, reaches_1 n.

Module LePlayground.

Inductive le:nat->nat->Prop:=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).
End LePlayground.

Inductive clos_trans {X: Type} (R: X->X->Prop):X->X->Prop:=
  | t_step (x y: X): R x y -> clos_trans R x y
  | t_trans (x y z: X):
    clos_trans R x y ->
    clos_trans R y z ->
    clos_trans R x z.

Inductive clos_reflex_trans {X: Type} (R: X->X->Prop):X->X->Prop:=
  | t_step' (x y: X): R x y -> clos_reflex_trans R x y
  | t_reflex' (x: X): clos_reflex_trans R x x
  | t_trans' (x y z: X):
    clos_reflex_trans R x y ->
    clos_reflex_trans R y z ->
    clos_reflex_trans R x z.

Inductive clos_reflex_symm_trans {X: Type} (R: X->X->Prop):X->X->Prop:=
  | t_step'' (x y: X): R x y -> clos_reflex_symm_trans R x y
  | t_reflex'' (x: X): clos_reflex_symm_trans R x x
  | t_symm'' (x y: X): R x y -> clos_reflex_symm_trans R y x
  | t_trans'' (x y z: X):
    clos_reflex_symm_trans R x y ->
    clos_reflex_symm_trans R y z ->
    clos_reflex_symm_trans R x z.

Inductive Perm3 {X:Type}: list X -> list X -> Prop :=
| perm3_swap12 (a b c:X):
  Perm3 [a;b;c] [b;a;c]
| perm3_swap23 (a b c:X):
  Perm3 [a;b;c] [a;c;b]
| perm3_trans (l1 l2 l3: list X):
  Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(* Evenness (yet again) *)

Inductive ev:nat -> Prop :=
 | ev_0 : ev 0
 | ev_SS (n:nat) (H:ev n): ev (S (S n)).


Theorem ev_double: forall n,
  ev (double n).
Proof.
  induction n. simpl. apply ev_0.
  simpl. apply ev_SS. apply IHn.
Qed.

Theorem ev_inversion: forall n:nat,
  ev n ->
  (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. destruct E.
  - left. reflexivity.
  - right. exists n. split. reflexivity. apply E.
Qed.

Theorem evSS_ev:forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. apply ev_inversion in H. destruct H as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq. rewrite Heq. apply Hev.
Qed.

Theorem evSS_ev': forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [|n' E' Heq]. apply E'.
Qed.

Theorem one_not_even: ~ ev 1.
Proof.
  intros H. apply ev_inversion in H. destruct H as [|[m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even': ~ ev 1.
Proof.
  intros H. inversion H.
Qed.

Theorem SSSSev__even:forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros. inversion H. inversion H1. apply H3.
Qed.

Theorem ev5_nonsense:
  ev 5 -> 2 + 2 = 9.
Proof.
  intros. inversion H. inversion H1. inversion H3.
Qed.

Theorem inversion_ex1:forall n m o:nat,
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity.
Qed.

Theorem inversion_ex2:forall n:nat,
  S n = O -> 2 + 2 = 5.
Proof.
  intros. inversion H.
Qed.

Lemma ev_Even:forall n,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - unfold Even. exists 0. reflexivity.
  - unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even. exists (S k). reflexivity.
Qed.

Theorem ev_Even_iff: forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - apply ev_Even.
  - unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum: forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm. induction Hn.
  - apply Hm.
  - replace (S (S n) + m) with (S (S (n + m))).
    + apply ev_SS. apply IHHn.
    + reflexivity.
Qed.

Inductive ev':nat->Prop:=
  | ev'_0:ev' 0
  | ev'_2:ev' 2
  | ev'_sum n m (Hn: ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev:forall n, ev' n <-> ev n.
Proof.
  induction n. split. intros. apply ev_0. intros. apply ev'_0. split.
  - intros. induction H. apply ev_0. apply (ev_SS 0 ev_0).
    apply (ev_sum n0 m IHev'1 IHev'2).
  - intros. induction H. apply ev'_0. apply (ev'_sum 2 n0 ev'_2 IHev).
Qed.

Theorem ev_ev__ev:forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m Hnm Hn. induction Hn. apply Hnm.
  inversion Hnm. apply (IHHn H0).
Qed.

Theorem ev_plus_plus:forall n m p,
  ev(n+m) -> ev(n+p) -> ev(m+p).
Proof.
  intros n m p Hnm Hnp.
  assert (ev ((n+m)+(n+p))). apply (ev_sum (n+m) (n+p) Hnm Hnp).
  replace (n+m+(n+p)) with (n+n+(m+p)) in H.
  assert (ev (n+n)). { rewrite <- (double_plus n). apply ev_double. }
  apply (ev_ev__ev (n+n) (m+p) H H0).
  rewrite add_assoc. rewrite add_assoc. replace (n+n+m) with (n+m+n).
  reflexivity. rewrite add_comm. rewrite add_assoc. reflexivity.
Qed.

(* Inductive Relations *)

Module Playground.

Inductive le:nat->nat->Prop:=
|le_n(n:nat):le n n
|le_S(n m:nat) (H:le n m): le n (S m).
Notation "n <= m" := (le n m).

Theorem test_le1: 3<=3. Proof. apply le_n. Qed.
Theorem test_le2: 3<=6. Proof. apply le_S. apply le_S. apply le_S. apply le_n.
Qed.
Theorem test_le3:(2<=1)->2+2=5. Proof. intros H. inversion H. inversion H2. Qed.

Definition lt (n m:nat) := le (S n) m.
Notation "m < n" := (lt m n).
End Playground.

Inductive total_relation:nat->nat->Prop:=
  total_r n m: total_relation n m.

Theorem total_relation_is_total:forall n m, total_relation n m.
Proof. intros. apply (total_r n m). Qed.

Inductive empty_relation:nat->nat->Prop:=.
Theorem empty_relation_is_empty: forall n m, ~ empty_relation n m.
Proof. intros n m H. inversion H. Qed.

Lemma le_trans: forall m n o, m<=n -> n <= o -> m <= o.
Proof.
  intros m n o Hmn Hno. induction Hno. apply Hmn. apply (le_S m m0 IHHno).
Qed.

Theorem O_le_n:forall n, 0 <= n.
Proof.
    induction n. apply le_n. apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm:forall n m, n <= m -> S n <= S m.
Proof.
  intros n m H. induction H. apply le_n. apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m:forall n m, S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H. apply le_n. assert (n <= S n).
  - apply le_S. apply le_n.
  - apply (le_trans _ _ _ H2 H1).
Qed.

Theorem lt_ge_cases: forall n m, n<m \/ n>=m.
Proof.
  unfold lt. unfold ge.
  induction n. induction m. right. apply le_n. left. apply n_le_m__Sn_le_Sm.
  apply O_le_n.
  induction m. right. apply O_le_n. destruct (IHn m).
  - left. apply (n_le_m__Sn_le_Sm _ _ H).
  - right. apply (n_le_m__Sn_le_Sm _ _ H).
Qed.

Theorem le_plus_l: forall a b, a <= a + b.
Proof.
  induction a. intros. apply O_le_n.
  intros b. apply (n_le_m__Sn_le_Sm _ _ (IHa b)).
Qed.

Theorem plus_le: forall n1 n2 m,
  n1 + n2 <= m -> n1 <= m /\ n2 <= m.
Proof.
  induction n1. intros. split. apply O_le_n. apply H.
  induction n2. intros. split. rewrite add_comm in H. apply H. apply O_le_n.
  intros. inversion H. split. apply le_plus_l. rewrite add_comm. apply
  le_plus_l.
  split. apply n_le_m__Sn_le_Sm. assert (n1 <= S n1 + S n2). replace (S n1) with
  (n1 + 1). rewrite <- add_assoc. apply le_plus_l. apply add_comm.
  apply (le_trans _ _ _ H2 H0).
  assert (n2 <= S n1 + S n2). replace (S n2) with (n2 + 1). rewrite add_assoc.
  replace (S n1 + n2) with (n2 + S n1). rewrite <- add_assoc. apply le_plus_l.
  apply add_comm. apply add_comm.
  apply n_le_m__Sn_le_Sm. apply (le_trans _ _ _ H2 H0).
Qed.

Theorem add_le_cases: forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  induction n. intros. left. apply O_le_n.
  intros. destruct p.
  - rewrite add_comm in H. simpl in H. assert (m <= m + S n). { apply le_plus_l.
  } right. apply (le_trans _ _ _ H0 H).
  - rewrite plus_Sn_m in H. rewrite plus_Sn_m in H. apply Sn_le_Sm__n_le_m in H.
  apply IHn in H. destruct H. left. apply n_le_m__Sn_le_Sm. apply H.
  right. apply H.
Qed.

Theorem plus_le_compat_l: forall n m p,
  n <= m -> p + n <= p + m.
Proof.
  induction p.
  - intros. apply H.
  - intros. rewrite plus_Sn_m. rewrite plus_Sn_m. apply n_le_m__Sn_le_Sm. apply
  (IHp H).
Qed.

Theorem plus_le_compat_r: forall n m p,
  n <= m -> n + p <= m + p.
Proof.
  intros. rewrite add_comm. replace (m + p) with (p + m). apply
  plus_le_compat_l. apply H. apply add_comm.
Qed.

Theorem le_plus_trans: forall n m p,
  n <= m -> n <= m + p.
Proof.
  intros. assert (m <= m + p). replace m with (m + 0). rewrite <- add_assoc.
  apply plus_le_compat_l. simpl. apply O_le_n. apply add_comm. apply (le_trans _
_  _ H H0).
Qed.

Theorem n_lt_m__n_le_m: forall n m,
  n < m -> n <= m.
Proof.
  unfold lt. intros. assert (n <= S n). apply le_S. apply le_n. apply (le_trans
  _ _ _ H0 H).
Qed.

Theorem plus_lt: forall n1 n2 m,
  n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  unfold lt. intros. destruct m. inversion H. apply Sn_le_Sm__n_le_m in H.
  apply plus_le in H. destruct H. split. apply n_le_m__Sn_le_Sm. apply H. apply
  n_le_m__Sn_le_Sm. apply H0.
Qed.

Theorem leb_complete: forall n m,
  n <=? m = true -> n <= m.
Proof.
  induction n. intros. apply O_le_n. intros. destruct m. discriminate H. simpl
  in H. apply n_le_m__Sn_le_Sm. apply IHn, H.
Qed.

Theorem leb_correct: forall n m,
  n <= m -> n <=? m = true.
Proof.
  induction n.
  - intros. simpl. reflexivity.
  - induction m. intros. inversion H. intros. apply Sn_le_Sm__n_le_m in H. apply
  IHn in H. simpl. apply H.
Qed.

Theorem leb_iff: forall n m,
  n <=? m = true <-> n <= m.
Proof.
  split. apply leb_complete. apply leb_correct.
Qed.

Theorem leb_true_trans: forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros. rewrite leb_iff in H. rewrite leb_iff in H0. rewrite leb_iff. apply
  (le_trans _ _ _ H H0).
Qed.

Module R.
  Inductive R: nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H: R m n o): R (S m) n (S o)
  | c3 m n o (H: R m n o): R m (S n) (S o)
  | c4 m n o (H: R (S m) (S n) (S (S o))): R m n o
  | c5 m n o (H: R m n o): R n m o
  .
  Definition fR (n:nat) (m:nat): nat := n + m.
  Theorem R_equiv_fR: forall n m o, R m n o <-> fR m n = o.
  Proof.
    unfold fR.
    split.
    - intros H. induction H.
      + reflexivity.
      + rewrite plus_Sn_m. rewrite IHR. reflexivity.
      + rewrite <- plus_n_Sm. rewrite IHR. reflexivity.
      + rewrite plus_Sn_m in IHR. injection IHR as IHR. rewrite <- plus_n_Sm in
    IHR. injection IHR as IHR. apply IHR.
      + rewrite add_comm. apply IHR.
    - generalize dependent m. generalize dependent n. induction o. intros. assert (m+n <= 0). replace (m+n) with 0. apply le_n.
    apply plus_le in H0. destruct H0. inversion H0. inversion H1. apply c1.
      + intros. destruct m. simpl in H. rewrite H. apply c3. apply IHo.
      reflexivity.
        apply c2. apply IHo. rewrite plus_Sn_m in H. injection H as H. apply H.
  Qed.
End R.

Inductive subseq : list nat -> list nat -> Prop :=
  | subseq0: subseq [] []
  | subseq1 (x: nat) (l1 l2: list nat) (H: subseq l1 l2): subseq l1 (x::l2)
  | subseq2 (x: nat) (l1 l2: list nat) (H: subseq l1 l2): subseq (x::l1) (x::l2)
.

Theorem subseq_refl: forall (l : list nat), subseq l l.
Proof.
  induction l.
  - apply subseq0.
  - apply (subseq2 x l l IHl).
Qed.

Lemma subseq_nil: forall l: list nat,
  subseq [] l.
Proof.
  induction l. apply subseq0. apply (subseq1 _ _ _ IHl).
Qed.

Theorem subseq_app: forall l1 l2 l3: list nat,
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  induction l1.
  - intros. apply subseq_nil.
  - intros. induction H. apply subseq_nil. simpl. apply subseq1. apply IHsubseq.
    simpl. apply subseq2. apply IHsubseq.
Qed.

Theorem subseq_trans: forall (l1 l2 l3: list nat),
  subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros. generalize dependent l1. induction H0. intros. apply H.
  - intros. apply IHsubseq in H. apply (subseq1 _ _ _ H).
  - intros. inversion H. apply subseq1. apply IHsubseq. apply H3.
    apply subseq2. apply IHsubseq. apply H3.
Qed.

(* A Digression on Notation *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).
Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

Example reg_exp_ex1: [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2: [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]). apply MChar. apply MChar.
Qed.

Example reg_exp_ex3: ~([1;2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.
Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]). apply MChar. apply (MApp [2]). apply MChar.
  apply (MApp [3]). apply MChar. apply MEmpty.
Qed.

Lemma MStar1: forall T s (re:reg_exp T),
  s =~ re -> s =~ Star re.
Proof.
  intros. rewrite <- (app_nil_r _ s). apply MStarApp. apply H. apply MStar0.
Qed.

Lemma empty_is_empty: forall T (s: list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H. inversion H.
Qed.

Lemma MUnion': forall T (s: list T) (re1 re2: reg_exp T),
  s =~ re1 \/ s =~ re2 -> s =~ Union re1 re2.
Proof.
  intros T s re1 re2 H. destruct H.
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

Lemma MStar': forall T (ss: list (list T)) (re: reg_exp T),
  (forall s, In s ss -> s =~ re) -> fold app ss [] =~ Star re.
Proof.
  intros T. induction ss.
  - intros. simpl. apply MStar0.
  - intros. simpl. apply (MStarApp x).
    + apply H. left. reflexivity.
    + apply IHss. intros. apply H. right. apply H0.
Qed.

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl. rewrite In_app_iff. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

Fixpoint re_not_empty {T: Type} (re: reg_exp T): bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => (re_not_empty re1) && (re_not_empty re2)
  | Union re1 re2 => re_not_empty re1 || re_not_empty re2
  | Star re => true
  end.

Lemma re_not_empty_correct: forall T (re: reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T. split; induction re; intros.
  - inversion H. inversion H0.
  - inversion H. simpl. reflexivity.
  - inversion H. simpl. reflexivity.
  - inversion H. simpl. inversion H0. rewrite andb_true_iff. split.
    + apply IHre1. exists s1. apply H4.
    + apply IHre2. exists s2. apply H5.
  - inversion H. simpl. rewrite orb_true_iff. inversion H0.
    + left. apply IHre1. exists x. apply H3.
    + right. apply IHre2. exists x. apply H3.
  - simpl. reflexivity.
  - inversion H.
  - exists []. apply MEmpty.
  - exists [t]. apply MChar.
  - simpl in H. apply andb_true_iff in H. destruct H. apply IHre1 in H. apply
  IHre2 in H0. inversion H. inversion H0. exists (x ++ x0). apply (MApp x).
  apply H1. apply H2.
  - simpl in H. apply orb_true_iff in H. destruct H.
    + apply IHre1 in H. inversion H. exists x. apply MUnionL. apply H0.
    + apply IHre2 in H. inversion H. exists x. apply MUnionR. apply H0.
  - exists []. apply MStar0.
Qed.

Lemma star_app: forall T (s1 s2: list T) (re: reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - injection Heqre' as Heqre''. intros. apply H.
  - injection Heqre' as Heqre''. intros. rewrite <- app_assoc.
    apply MStarApp. apply H1_. apply IHexp_match2. rewrite Heqre''. reflexivity.
    apply H.
Qed.

Lemma MStar'': forall T (s: list T) (re: reg_exp T),
  s =~ Star re -> 
  exists ss: list (list T), s = fold app ss [] /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros. remember (Star re) as re'. induction H.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists []. split. reflexivity. intros. destruct H.
  - apply IHexp_match2 in Heqre' as Heqre''. inversion Heqre''. exists (s1::x). split.
  destruct H1. simpl. rewrite H1. reflexivity. intros. simpl in H2. injection
  Heqre' as Heqre'. destruct H2. rewrite <- H2. rewrite <- Heqre'. apply H.
  destruct H1. apply H3. apply H2.
Qed.

Module Pumping.

Fixpoint pumping_constant {T} (re: reg_exp T): nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 => pumping_constant re1 + pumping_constant re2
  | Union re1 re2 => pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

Lemma pumping_constant_ge_1: forall T (re: reg_exp T), pumping_constant re >= 1.
Proof.
  intros. induction re.
  - apply le_n.
  - apply le_n.
  - apply le_S. apply le_n.
  - simpl. apply le_trans with (n := pumping_constant re1). apply IHre1. apply le_plus_l.
  - simpl. apply le_trans with (n := pumping_constant re1). apply IHre1. apply
  le_plus_l.
  - simpl. apply IHre.
Qed.

Lemma pumping_consant_0_false: forall T (re: reg_exp T), pumping_constant re = 0
-> False.
Proof.
  intros. assert (pumping_constant re >= 1). apply pumping_constant_ge_1.
  inversion H0. rewrite <- H2 in H. discriminate H. rewrite <- H1 in H.
  discriminate H.
Qed.

Fixpoint napp {T} (n: nat) (l: list T): list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
end.

Lemma napp_star:
  forall T m s1 s2 (re: reg_exp T), s1 =~ re -> s2 =~ Star re -> napp m s1 ++ s2
  =~ Star re.
Proof.
  intros T. induction m. intros.
  - simpl. apply H0.
  - intros. simpl. rewrite <- app_assoc. apply MStarApp. apply H. apply IHm.
  apply H. apply H0.
Qed.

Lemma weak_pumping: forall T (re: reg_exp T) s,
  s =~ re -> pumping_constant re <= length s -> exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\ s2 <> [] /\ forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch.
  - simpl. intros contra. inversion contra.
  - simpl. intros contra. inversion contra. inversion H0.
  - simpl. intros. rewrite app_length in H. apply add_le_cases in H. destruct H.
    + apply IHHmatch1 in H. destruct H. destruct H. destruct H. destruct H.
    destruct H0. exists x. exists x0. exists (x1 ++ s2). split.
      * rewrite H. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
      * split. apply H0. intros. rewrite app_assoc. rewrite app_assoc. apply
      MApp. rewrite <- app_assoc. apply H1. apply Hmatch2.
    + apply IHHmatch2 in H. destruct H. destruct H. destruct H. destruct H.
    destruct H0. exists (s1++x). exists x0. exists x1. split.
      * rewrite H. rewrite app_assoc. reflexivity.
      * split. apply H0. intros. assert (s1 ++ (x ++ napp m x0 ++ x1) = (s1 ++ x)
      ++ napp m x0 ++ x1). rewrite app_assoc. reflexivity. rewrite <- H2. apply
      MApp. apply Hmatch1. apply H1.
  - simpl. intros. apply plus_le in H. destruct H. apply IHHmatch in H. destruct
  H. destruct H. destruct H. destruct H. destruct H1. exists x. exists x0.
  exists x1. split. apply H. split. apply H1. intros. apply MUnionL. apply H2.
  - simpl. intros. apply plus_le in H. destruct H. apply IHHmatch in H0. destruct
  H0. destruct H0. destruct H0. destruct H0. destruct H1. exists x. exists x0.
  exists x1. split. apply H0. split. apply H1. intros. apply MUnionR. apply H2.
  - simpl. intros contra. inversion contra. apply pumping_consant_0_false in H0.
  destruct H0.
  - simpl. intros. rewrite app_length in H. simpl in IHHmatch2. destruct s1.
    + simpl. simpl in H. apply IHHmatch2 in H. destruct H. destruct H. destruct
    H. exists x. exists x0. exists x1. apply H.
    + simpl. exists []. exists (x :: s1). exists s2. split. reflexivity. split.
    intros contra. discriminate. intros. simpl. apply napp_star. apply Hmatch1.
    apply Hmatch2.
Qed.

Lemma pumping: forall T (re: reg_exp T) s,
  s =~ re -> pumping_constant re <= length s -> exists s1 s2 s3,
    s = s1 ++  s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch.
  - simpl. intros contra. inversion contra.
  - simpl. intros contra. inversion contra. inversion H0.
  - simpl. intros. rewrite app_length in H. apply add_le_cases in H. destruct H.
    + apply IHHmatch1 in H. destruct H as [s3[s4[s5[H[H0[]]]]]].
    exists s3, s4, (s5 ++ s2). split. rewrite H. rewrite <- app_assoc. rewrite
    <- app_assoc. reflexivity. split. apply H0. split. apply le_plus_trans.
    apply H1. intros. rewrite app_assoc. rewrite app_assoc. apply MApp. rewrite
    <- app_assoc. apply H2. apply Hmatch2.
    + apply IHHmatch2 in H. destruct H as [s3[s4[s5[H[H0[]]]]]]. destruct
    (lt_ge_cases (pumping_constant re1) (length s1)).
      * apply n_lt_m__n_le_m in H3. apply IHHmatch1 in H3. destruct H3 as [s6[s7[s8[H4[H5[]]]]]].
    exists s6, s7, (s8 ++ s2). split. rewrite H4. rewrite <- app_assoc. rewrite
    <- app_assoc. reflexivity. split. apply H5. split. apply le_plus_trans.
    apply H3. intros. rewrite app_assoc. rewrite app_assoc. apply MApp. rewrite
    <- app_assoc. apply H6. apply Hmatch2.
      * exists (s1 ++ s3), s4, s5. split. rewrite H. rewrite app_assoc.
      reflexivity. split. apply H0. rewrite app_length. split. apply le_trans
      with (n := (pumping_constant re1) + (length s3 + length s4)). rewrite <-
      add_assoc. apply plus_le_compat_r. apply H3. apply plus_le_compat_l. apply
      H1. intros. replace ((s1 ++ s3) ++ napp m s4 ++ s5) with (s1 ++ (s3 ++
      napp m s4 ++ s5)). apply MApp. apply Hmatch1. apply H2. apply app_assoc.
  - simpl. intros. apply plus_le in H. destruct H. apply IHHmatch in H. destruct
  H as [s2[s3[s4[H[H1[]]]]]]. exists s2, s3, s4. split. apply H. split. apply
  H1. split. apply le_plus_trans. apply H2. intros. apply MUnionL. apply H3.
  - simpl. intros. apply plus_le in H. destruct H. apply IHHmatch in H0. destruct
  H0 as [s3[s4[s5[H0[H1[]]]]]]. exists s3, s4, s5. split. apply H0. split. apply
  H1. split. replace (pumping_constant re1 + pumping_constant re2) with
  (pumping_constant re2 + pumping_constant re1). apply le_plus_trans. apply H2.
  apply add_comm. intros. apply MUnionR. apply H3.
  - intros. inversion H. apply pumping_consant_0_false in H1. inversion H1.
  - simpl. intros. rewrite app_length in H. simpl in IHHmatch2. destruct
  (lt_ge_cases (pumping_constant re) (length s1)).
    + apply n_lt_m__n_le_m in H0. apply IHHmatch1 in H0. destruct H0 as
    [s3[s4[s5[H0[H1[]]]]]]. exists s3, s4, (s5 ++ s2). split. rewrite H0.
    rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. split. apply H1.
    split. apply H2. intros. rewrite app_assoc. rewrite app_assoc. apply
    MStarApp. rewrite <- app_assoc. apply H3. apply Hmatch2.
    + destruct s1. simpl in H. apply IHHmatch2 in H. destruct H as
    [s3[s4[s5[H[H1[]]]]]]. exists s3, s4, s5. split. apply H. split. apply H1.
    split. apply H2. apply H3.
      exists [], (x :: s1), s2. split. reflexivity. split. intros contra.
      inversion contra. split. apply H0. intros. apply napp_star. apply Hmatch1.
      apply Hmatch2.
Qed.

End Pumping.

Inductive reflect (P: Prop): bool -> Prop :=
  | ReflectT (H: P): reflect P true
  | ReflectF (H: ~P): reflect P false.

Theorem iff_reflect: forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Theorem reflect_iff: forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. split. intros. destruct H. reflexivity. apply H in H0. inversion
  H0. destruct H. intros. apply H. intros. discriminate.
Qed.

Lemma eqbP: forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In: forall n l,
  filter (fun x => n =? x) l <> [] -> In n l.
Proof.
  intros n l. induction l as [|m l'].
  - simpl. intros. apply H. reflexivity.
  - simpl. destruct (eqbP n m).
    + intros _. rewrite H. left. reflexivity.
    + intros. right. apply IHl'. apply H0.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice: forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [|m l' IHl'].
  - intros H. simpl in H. apply H.
  - intros H. simpl in Hcount, H. destruct (eqbP n m).
    + discriminate.
    + apply IHl' in Hcount. destruct H. symmetry in H. apply H0 in H. apply H.
    apply Hcount in H. apply H.
Qed.

Inductive nostutter {X:Type}: list X -> Prop :=
  | nostutter_nil: nostutter []
  | nostutter_one (x: X): nostutter [x]
  | nostutter_cons (x: X) (y: X) (l: list X) (H: nostutter (y::l)) (H2: x <> y):
  nostutter (x::(y::l))
.

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  repeat constructor; apply eqb_neq; auto.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof.
  repeat constructor; apply eqb_neq; auto.
Qed.

Example test_nostutter_3: nostutter [5].
  Proof. repeat constructor; auto. Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto.
Qed.

Inductive merge {X: Type}: list X -> list X -> list X -> Prop :=
  | merge_nil: merge [] [] []
  | merge_l (x: X) (a b c: list X) (H: merge a b c): merge (x::a) b (x::c)
  | merge_r (x: X) (a b c: list X) (H: merge a b c): merge a (x::b) (x::c)
.

Theorem merge_filter: forall (X: Set) (test: X -> bool) (l l1 l2: list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  intros. induction H.
  - reflexivity.
  - simpl in H0. destruct H0. simpl. rewrite H0. replace (filter test c) with a.
  reflexivity. symmetry. apply IHmerge. apply H2. apply H1.
  - simpl in H1. destruct H1. simpl. rewrite H1. apply IHmerge. apply H0. apply
  H2.
Qed.

Theorem filter_challenge_2: forall (test: nat -> bool) (sub l: list nat),
  (subseq sub l) -> All (fun n => test n = true) sub -> length sub <= length
  (filter test l).
Proof.
  intros. induction H.
  - simpl. apply le_n.
  - simpl. apply IHsubseq in H0. apply le_trans with (n := length (filter test
  l2)). apply H0. destruct (test x). simpl. apply le_S. apply le_n. apply le_n.
  - simpl. simpl in H0. destruct H0. apply IHsubseq in H1. rewrite H0. simpl.
  apply n_le_m__Sn_le_Sm. apply H1.
Qed.

Inductive pal {X:Type}: list X -> Prop :=
  | pal_nil: pal []
  | pal_one (x:X): pal [x]
  | pal_add (x:X) (l: list X) (H: pal l): pal (x :: l ++ [x])
.

Theorem pal_app_rev: forall {X:Type} (l: list X),
  pal (l ++ (rev l)).
Proof.
  intros. induction l.
  - simpl. apply pal_nil.
  - simpl. rewrite app_assoc. apply pal_add. apply IHl.
Qed.

Theorem rev_involutive: forall (X:Type) (l: list X),
  rev (rev l) = l.
Proof.
  induction l as [| n l IHl].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl. reflexivity.
Qed.

Theorem pal_rev: forall (X:Type) (l: list X), pal l -> l = rev l.
Proof.
  intros. induction H.
  - reflexivity.
  - reflexivity.
  - assert ([x] ++ l ++ [x] = ([x] ++ l) ++ [x]). apply app_assoc.
    rewrite <- (rev_involutive _ ([x] ++ l)) in H0. simpl in H0. simpl. rewrite
    H0. simpl. rewrite <- IHpal. reflexivity.
Qed.

Lemma rev_app_distr : forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros X l1 l2. induction l1 as [| n l1' IHl1'].
- simpl. rewrite -> app_nil_r. reflexivity.
- simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
Qed.

Lemma palindrome_converse': forall X (n: nat) (l:list X),
  length l <= n -> l = rev l -> pal l.
Proof.
  intros X. induction n.
  - intros. inversion H. destruct l. apply pal_nil. discriminate.
  - intros. destruct l. apply pal_nil. simpl in *. destruct (rev l) as [] eqn:E.
    + rewrite H0. apply pal_one.
    + injection H0 as H0. rewrite H1. apply pal_add. apply IHn. apply leb_iff in
    H. simpl in H. apply leb_iff in H. rewrite H1 in H. rewrite app_length in H.
    apply le_trans with (n := length l0 + length [x]). apply le_plus_l. apply H.
    rewrite H1 in E. rewrite rev_app_distr in E. rewrite H0 in E. simpl in E.
    injection E as E. rewrite E. reflexivity.
Qed.

Theorem palindrome_converse: forall {X: Type} (l: list X),
  l = rev l -> pal l.
Proof.
  intros X l H. apply palindrome_converse' with (n := length l). apply le_n.
  apply H.
Qed.

Inductive disjoint {X}: (list X) -> (list X) -> Prop :=
  | disjoint_nil: disjoint [] []
  | disjoint_l (x:X) (l1 l2:list X) (H: disjoint l1 l2) (HI: ~(In x l2)) : disjoint (x::l1) l2
  | disjoint_r (x:X) (l1 l2:list X) (H: disjoint l1 l2) (HI: ~(In x l1)) : disjoint l1 (x::l2)
.

Inductive NoDup {X}: list X -> Prop :=
  | NoDup_nil: NoDup []
  | NoDup_add (x:X) (l:list X) (H:NoDup l) (HI: ~(In x l)) : NoDup (x::l)
.

Theorem app_no_dup_disjoint: forall X (l1 l2: list X),
  NoDup (l1 ++ l2) -> disjoint l1 l2.
Proof.
  intros X. induction l1 as [|x' l1].
  - intros l2 H. induction l2. apply disjoint_nil. apply disjoint_r. apply IHl2.
  inversion H. apply H1. intros contra. simpl in contra. apply contra.
  - intros l2 H. simpl in *. inversion H. apply IHl1 in H1. apply disjoint_l.
  apply H1. unfold not in *. intros. apply HI. apply In_app_iff. right. apply H3.
Qed.

Lemma in_split: forall (X:Type) (x:X) (l: list X),
  In x l -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x. induction l.
  - intros. destruct H.
  - intros. destruct H.
    + exists nil, l. rewrite H. reflexivity.
    + apply IHl in H. destruct H as [l1[l2]]. exists (x0::l1), l2. rewrite H. reflexivity.
Qed.

Inductive repeats {X:Type}: list X -> Prop :=
  | repeats_rep (x:X) (xs: list X) (H: In x xs): repeats (x::xs)
  | repeats_add (x:X) (xs: list X) (H: repeats xs): repeats (x::xs)
.

Lemma remove {X:Type}: forall (x:X) (xs:list X),
  In x xs -> exists xs', (forall x', x<>x' -> In x' xs -> In x' xs') /\ (length
  xs = S(length xs')).
Proof.
  intros. apply in_split in H. destruct H as [l1[l2]]. exists (l1 ++ l2).
  rewrite H. intros. clear H. split.
  - intros. apply In_app_iff in H0. apply In_app_iff. destruct H0. left. apply
  H0. simpl in H0. destruct H0. apply H in H0. destruct H0. right. apply H0.
  - rewrite app_length. simpl. rewrite app_length. replace (S (length l2)) with
  (1 + length l2). replace (S (length l1 + length l2)) with (1 + length l1 +
  length l2).
  rewrite add_assoc. rewrite (add_comm (length l1) 1). reflexivity. reflexivity. reflexivity.
Qed.

Theorem pigeonhole_principle: excluded_middle -> forall (X:Type) (l1 l2: list X),
  (forall x, In x l1 -> In x l2) -> length l2 < length l1 -> repeats l1.
Proof.
  intros ex. induction l1.
  - intros. inversion H0.
  - intros. destruct (ex (In x l1)).
    + apply repeats_rep. apply H1.
    + apply repeats_add. assert (In x l2). { apply H. simpl. left. reflexivity. }
      apply (remove x l2) in H2. destruct H2 as [l2'[]]. apply (IHl1 l2').
      * intros. apply H2. intros contra. rewrite <- contra in H4. apply H1 in
      H4. apply H4. apply H. simpl. right. apply H4.
      * rewrite H3 in H0. simpl in H0. apply Sn_le_Sm__n_le_m in H0. apply H0.
Qed.

(* TODO: Extended Exercise: A Verified Regular-Expression Matcher *)

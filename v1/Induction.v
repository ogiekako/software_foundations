From LF Require Export Basics.

Theorem add_0_r_firsttry: forall n:nat,
  n + 0 = n.

Proof.
  intros n.
  simpl.
Abort.

Theorem add_0_r: forall n: nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem minus_n_n : forall n, minus n n = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mul_0_r : forall n: nat,
  n * 0 = 0.
Proof.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm: forall n m : nat,
  S(n+m) = n + (S m).
Proof.
  induction n as [|n' IHn'].
  - intros m. simpl. reflexivity.
  - intros m. simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem add_comm: forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [|n' IHn'].
  - intros m. simpl. rewrite -> add_0_r. reflexivity.
  - intros m. simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed.

Theorem add_assoc: forall n m p:nat,
  n+(m+p) = (n+m)+p.
Proof.
  induction n as [|n' IHn'].
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite -> IHn'. reflexivity. Qed.

Fixpoint double(n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus: forall n, double n = n + n.
Proof.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite plus_n_Sm. reflexivity. Qed.

Theorem eqb_refl: forall n: nat,
  (n =? n) = true.
Proof.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. apply IHn'. Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - rewrite IHn'. rewrite negb_involutive. simpl. reflexivity. Qed.

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.

Theorem add_shuffle3: forall n m p:nat,
  n+(m+p) = m+(n+p).
Proof.
  intros.
  rewrite add_assoc.
  rewrite add_assoc.
  assert (H:n+m=m+n). apply add_comm.
  rewrite H. reflexivity. Qed.

Theorem mul_comm: forall m n : nat,
  m * n = n * m.
Proof.
  induction m.
  - intros. simpl. rewrite mul_0_r. reflexivity.
  - intros. simpl. rewrite IHm. assert (H: n + n * m = n * S m).
    { induction n.
    - simpl. reflexivity.
    - simpl. rewrite <- IHn. rewrite add_shuffle3. reflexivity. }
    apply H. Qed.

Check leb.

Theorem plus_leb_compat_l: forall n m p: nat,
  n <=? m = true -> (p + n) <=? (p +  m) = true.
Proof.
  intros n. intros m. induction p.
  - simpl. intros. apply H.
  - intros. simpl. rewrite IHp. reflexivity. apply H. Qed.

Theorem leb_refl: forall n: nat,
  (n <=? n) = true.
Proof.
  induction n. simpl. reflexivity. simpl. apply IHn. Qed.

Theorem zero_neqb_S: forall n: nat,
  0 =? (S n) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem andb_false_r: forall b: bool,
  andb b false = false.
Proof.
  intros. destruct b. simpl. reflexivity. simpl. reflexivity.
Qed.

Theorem S_neqb_0: forall n:nat,
  (S n) =? 0 = false.
Proof.
  reflexivity.
Qed.

Theorem mult_1_l: forall n:nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite <- plus_n_O.
  reflexivity. Qed.

  Theorem all3_spec : forall b c : bool,
  orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  destruct b.
  - simpl. destruct c.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Theorem mult_plus_distr_r: forall n m p: nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros. induction n as [| n IHn].
  - reflexivity.
  - simpl. rewrite -> IHn. rewrite <- add_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros.
  induction n as [| n IHn].
  - reflexivity.
  - simpl. rewrite -> IHn. rewrite <- mult_plus_distr_r. reflexivity.
Qed.

Theorem add_shuffle3': forall n m p:nat,
  n+(m+p) = m+(n+p).
Proof.
  intros.
  rewrite add_assoc.
  rewrite add_assoc.
  replace (n + m) with (m + n). reflexivity. apply add_comm. Qed.

Theorem bin_to_nat_pres_incr : forall n:bin,
  bin_to_nat (incr n) = S (bin_to_nat n).
Proof.
  assert (H: forall m: nat, m * 2 = m + m). {
    intros.
    rewrite -> mul_comm. simpl. rewrite <- plus_n_O. reflexivity.
  }
  induction n as [|n IHn|n IHn].
  - reflexivity.
  - simpl.
    rewrite -> H. rewrite -> plus_n_Sm. replace (S (bin_to_nat n)) with (bin_to_nat n + 1).
    + rewrite -> add_assoc. reflexivity.
    + rewrite -> add_comm. rewrite -> plus_1_l. reflexivity.
  - simpl. rewrite -> H. rewrite -> H. rewrite -> IHn. rewrite -> plus_n_Sm.
    rewrite <- plus_1_l. rewrite -> add_assoc.
    assert (H2: forall k:nat, 1 + k + 1 + k = k + k + 2). {
      intros. replace (k + k + 2) with (k + 2 + k).
      + replace (k + 2) with (1 + k + 1).
        * reflexivity.
        * rewrite <- add_assoc. rewrite add_comm. replace (k+1+1) with
        (k+(1+1)). reflexivity. rewrite add_assoc. reflexivity.
      + rewrite <- add_assoc. replace (2+k) with (k+2). rewrite add_assoc.
      reflexivity. apply add_comm.
    }
    rewrite -> H2. reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr(nat_to_bin(n')) end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite bin_to_nat_pres_incr. rewrite IHn'. reflexivity. Qed.

(* TODO: solve Bin to Nat and Back to Bin. *)
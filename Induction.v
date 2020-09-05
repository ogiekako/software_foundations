From LF Require Export Basics.

Theorem plus_n_O: forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  0 * n = 0.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m: nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S(S(double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. simpl. rewrite -> negb_involutive. reflexivity.
Qed.

Set Nested Proofs Allowed.

Theorem mult_O_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

Theorem plus_swap: forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: p + m = m + p). { rewrite -> plus_comm. reflexivity. }
  rewrite <- H.
  assert (H2: m + (n + p) = (n + p) + m). { rewrite -> plus_comm. reflexivity. }
  rewrite -> H2.
  rewrite -> plus_assoc. reflexivity.
Qed.

Theorem mult_n_Sm': forall n m : nat,
  n + n * m = n * S m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. assert (H: n' + (m + n' * m) = m + (n' + n' * m)). {
    rewrite <- plus_swap. reflexivity.
  }
    rewrite -> H.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem mult_comm: forall m n : nat,
  m * n = n * m.
Proof.
  intros. induction n as [| n' IHn'].
  - rewrite <- mult_n_O. rewrite -> mult_0_r. reflexivity.
  - simpl.
    rewrite <- IHn'.
    rewrite -> plus_comm.
    rewrite <- mult_n_Sm'.
    rewrite -> plus_comm.
    reflexivity.
Qed.

Theorem lab_refl : forall n:nat,
  true = (n <=? n).
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  reflexivity.
Qed.

Theorem andb_false_r: forall b:bool,
  andb b false = false.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_l: forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H.
  induction p as [| p IHp].
  - simpl. rewrite <- H. reflexivity.
  - simpl. rewrite <- IHp. reflexivity.
Qed.

Theorem S_nbeq_0: forall n:nat,
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

Theorem mult_plus_distr_r: forall n m p: nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros. induction n as [| n IHn].
  - reflexivity.
  - simpl. rewrite -> IHn. rewrite <- plus_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros.
  induction n as [| n IHn].
  - reflexivity.
  - simpl. rewrite -> IHn. rewrite <- mult_plus_distr_r. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  induction n as [| n IHn].
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity. Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  replace (m + p) with (p + m).
  replace (m + (n + p)) with ((n + p) + m).
  - rewrite <- plus_assoc. reflexivity.
  - rewrite -> plus_comm. reflexivity.
  - rewrite -> plus_comm. reflexivity.
Qed.

(* pres stands for preserve. *)
Theorem bin_to_nat_pres_incr : forall n:bin,
  bin_to_nat (incr n) = S (bin_to_nat n).
Proof.
  assert (H: forall m: nat, m * 2 = m + m). {
    intros.
    rewrite -> mult_comm. simpl. rewrite <- plus_n_O. reflexivity.
  }
  induction n as [|n IHn|n IHn].
  - reflexivity.
  - simpl.
    rewrite -> H. rewrite -> plus_n_Sm. replace (S (bin_to_nat n)) with (bin_to_nat n + 1).
    + rewrite -> plus_assoc. reflexivity.
    + rewrite -> plus_comm. rewrite -> plus_1_l. reflexivity.
  - simpl. rewrite -> H. rewrite -> H. rewrite -> IHn. rewrite -> plus_n_Sm.
    rewrite <- plus_1_l. rewrite -> plus_assoc.
    assert (H2: forall k:nat, 1 + k + 1 + k = k + k + 2). {
      intros. replace (k + k + 2) with (k + 2 + k).
      + replace (k + 2) with (1 + k + 1).
        * reflexivity.
        * rewrite <- plus_assoc. rewrite <- plus_swap. reflexivity.
      + rewrite <- plus_assoc. rewrite -> plus_swap. rewrite -> plus_comm. reflexivity.
    }
    rewrite -> H2. reflexivity.
Qed.

Fixpoint nat_to_bin_sub(n i:nat) : bin :=
  match n with
  | O => match i with
    | O => Z
    | _ => B1 Z
  end
  | S n' => match n <=? i with
    | false => (nat_to_bin_sub n' (S i))
    | true => match (evenb n) with
      | false => B0 (nat_to_bin_sub n' 1)
      | true => B1 (nat_to_bin_sub n' 1)
    end
  end
end.

Definition nat_to_bin (n:nat) : bin := (nat_to_bin_sub n 0).

Example test_nat_to_bin1: bin_to_nat (nat_to_bin 0) = 0.
Proof. reflexivity. Qed.
Example test_nat_to_bin2: bin_to_nat (nat_to_bin 1) = 1.
Proof. reflexivity. Qed.
Example test_nat_to_bin3: bin_to_nat (nat_to_bin 2) = 2.
Proof. reflexivity. Qed.
Example test_nat_to_bin4: bin_to_nat (nat_to_bin 42) = 42.
Proof. reflexivity. Qed.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - Admitted. (* TODO. Solve Exercise: 5 stars, advanced (binary_inverse) *)

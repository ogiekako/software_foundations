From LF Require Export Lists.

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X)
.

(* list is a function from Types to Inductive definitions. i.e. Type -> Type. *)

Check nil: forall X : Type , list X.
Check cons : forall X : Type, X -> list X -> list X.
(* nil and cons are now polymorphic constructors. We must provide a first argument that is the type of the list they are building. *)

Check (nil nat) : list nat.
Check cons nat : nat -> list nat -> list nat.

Check (cons nat 3 (nil nat)) : list nat.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end
.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat))
.
Proof. reflexivity. Qed.
Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool)
.
Proof. reflexivity. Qed
.

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end
.

Arguments nil {X}. (* Tell Coq always to infer the type arguments. *)
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123''' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint app {X:Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end
.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil) end
.
Fixpoint length {X:Type} (l: list X): nat :=
  match l with
  | nil => O
  | cons _ t => S (length t) end
.

Example test_rev1:
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed
.

Example test_rev2 : rev (cons true nil) = cons true nil. Proof. reflexivity. Qed
.

Example test_length1 : length (cons 1 (cons 2 (cons 3 nil))) = 3. Proof. reflexivity. Qed
.

(* Fail quantifier is used to ensure that that command indeed fails when executed. It prints error message on console. *)
Fail Definition mynil := nil. (* Cannot infer the implicit parameter X of nil. *)

Definition mynil : list nat := nil.

(* Force the implicit arguments to be explicit by prefixing @. *)
Check @nil : forall X : Type, list X.
Definition mynil' := @nil nat.

Check nil.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Definition list123'''' := [1;2;3].

Theorem app_nil_r : forall (X:Type), forall l:list X, l ++ [] = l.
Proof. intros X l. induction l as [| h t IHl].
    - reflexivity.
    - simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n: list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l as [|h t IHl].
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem app_length : forall X (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_app_distr : forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [|h t IH].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IH. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X (l:list X),
  rev (rev l) = l.
Proof.
  intros X l. induction l as [|h t IH].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IH. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

(* product type. The annotation type_scope tells Coq this notation applies only when parsing types, not when parsing expressions. *)
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
end.

Definition snd {X Y : Type} (p : X * Y) : Y := match p with | (x, y) => y end
.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | nil, _ => nil
  | _ , nil => nil
  | x::tx, y::ty => (x,y) :: (combine tx ty)
  end
.

Check @combine : forall X Y : Type, list X -> list Y -> list (X * Y).

Compute (combine [1;2] [false; false;true;true]).

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | nil => (nil , nil)
  | (x, y) :: t => match split t with
    | (xt, yt) => (x::xt, y::yt)
    end
  end
.

Example test_split:
  split [(1,false); (2,false)] = ([1;2],[false;false]).
Proof.
  reflexivity.
Qed.

Module OptionPlayground.
Inductive option (X:Type) : Type :=
| Some (x : X)
| None.

Arguments Some {X} _.
Arguments None {X}.
End OptionPlayground.

Fixpoint nth_error {X:Type} (l:list X) (n:nat) : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
    | O => Some a
    | S n' => nth_error l' n'
  end
  end
.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | h::_ => Some h
  end
.
Check @hd_error : forall X : Type, list X -> option X.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1]; [2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).
Check @doit3times.
Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Example test_doit3times : doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example test_doit3times' : doit3times negb true = false.
Proof. reflexivity. Qed
.

(* Return a new list containing just those elements for which the predicate returns true. *)
Fixpoint filter {X:Type} (test: X->bool) (l:list X) : (list X) :=
  match l with
  | nil => nil
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.
Example test_filter2 : filter length_is_1 [ [1;2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].

Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).
Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

  Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
  filter (fun l => (length l) =? 1)
    [ [1;2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat := filter (fun n => even n && (7 <? n)) l .

Example test_filter_even_gt7_1 : filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 : filter_even_gt7 [5;2;6;19;129] = nil.
Proof. reflexivity. Qed.

Definition partition {X:Type} (f: X->bool) (l: list X) : (list X * list X) :=
  (filter f l,
  filter (fun x => negb (f x)) l).

Example test_partition1: partition odd ([1;2;3;4;5]) = ([1;3;5],[2;4]).
Proof. reflexivity. Qed.
Example test_parition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y: Type} (f : X -> Y) (l:list X) : (list Y) :=
  match l with
  | nil => nil
  | h :: t => (f h) :: (map f t)
  end
.

Example test_map1: map (fun x => plus 3 x) [2;0;2] =[5;3;5].
Proof. reflexivity. Qed.

Example test_map2: map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_map3 : map (fun n =>  [even n; odd n]) [2;1;2;5] = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Theorem map_app_distr : forall (X Y: Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros. induction l1 as [| h t IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros. induction l as [|h t IHl].
  - reflexivity.
  - simpl. rewrite -> map_app_distr. rewrite -> IHl. reflexivity.
Qed.

Fixpoint flat_map {X Y : Type} (f:X -> list Y) (l : list X) : (list Y) := match l with
| nil => nil
| h :: t => f h ++ flat_map f t
end
.
Example test_flat_map1: flat_map (fun n => [n;n;n]) [1;5;4] = [1;1;1;5;5;5;4;4;4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y := match xo with
| None => None
| Some x => Some (f x)
end
.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b: Y) : Y := match l with
| nil => b
| h :: t => f h (fold f t b) end
.

Check (fold andb) : list bool -> bool -> bool.

Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed
.
Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed
.

Example fold_example3 : fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed
.

Example fold_example4 : fold (fun x y => length x + y) [[1];[];[2;3];[4]] 0 = 4.
Proof. reflexivity. Qed
.

Definition constfun {X:Type} (x:X) : nat->X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.
Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed
.

Check plus : nat -> nat -> nat.

Definition plus3 := plus 3.
Check plus3 : nat -> nat.
Example test_plus3 : plus3 4 = 7. Proof. reflexivity. Qed
.
Example test_plus3' : doit3times plus3 0 = 9. Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9. Proof. reflexivity. Qed.

Module Exercises.

Definition fold_length {X:Type} (l:list X) : nat :=
fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed
.

Theorem fold_length_correct: forall X (l : list X),
fold_length l = length l.
Proof.
  intros. induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite <- IH. reflexivity.
Qed.

Definition fold_map {X Y : Type} (f: X -> Y) (l:list X) : list Y :=
  fold (fun x yl => f x :: yl) l nil.
Theorem fold_map_correct: forall X Y (f: X -> Y) (l: list X),
  fold_map f l = map f l.
Proof.
  intros. induction l as [|h t IH].
  - reflexivity.
  - simpl. rewrite <- IH. reflexivity.
Qed.


Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z :Type} (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Theorem prod_curry_uncurry: forall (X Y Z:Type) (f: X -> Y -> Z),
  (prod_curry (prod_uncurry f))= f.
Proof.
  intros. reflexivity.
Qed.

Theorem prod_uncurry_curry: forall (X Y Z:Type) (f: X * Y -> Z) (p:X*Y),
  (prod_uncurry (prod_curry f)) p = f p.
Proof.
  intros. destruct p. reflexivity.
Qed.

Example test_map1' : map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed
.

Check @prod_curry : forall (X Y Z : Type), (X * Y -> Z) -> X -> Y -> Z.


Module Church.

Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition one : cnat := fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat := fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition zero : cnat := fun (X : Type) (f : X -> X) (x : X) => x.

Definition three : cnat := @doit3times.

Definition succ (n : cnat) : cnat
  := fun (X : Type) (f : X -> X) (x : X) => f (n X f x)
.

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed
.
Example succ_2 : succ one = two.
Proof. reflexivity. Qed
.
Example succ_3 : succ two = three.
Proof. reflexivity. Qed
.

Definition plus (n m : cnat) : cnat := fun (X:Type) (f : X -> X) (x : X) => n X f (m X f x)
.

Example plus_1 : plus zero one = one. Proof. reflexivity. Qed
.
Example plus_2 : plus two three = plus three two. Proof. reflexivity. Qed
.
Example plus_3 : plus (plus two two) three = plus one (plus three three). Proof. reflexivity. Qed
.

Definition mult (n m : cnat) : cnat := fun (X : Type) (f : X -> X) (x : X) => n X (m X f) x
.

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed
.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed
.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed
.

Compute two. (* func (X : Type) (x : X -> X) (x0 : X) => x (x x0) *)

Definition exp (n m : cnat) : cnat := fun (X: Type) (f : X -> X) (x : X) => (* n^1 f x = 
  n X f x.
  n^2 f x = (mult n n) f x = n X (n X f) x.
        
  ((2 (X -> X) (n X)) f) x = (n X) ((n X) f) x.
*)

  (m (X -> X) (n X)) f x
.
Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed
.
Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed
.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed
.

End Church.

End Exercises.

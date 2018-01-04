Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

  Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.


Fixpoint nonzeros (k:natlist) : natlist :=
  match k with
  | nil => nil
  | 0 :: l => nonzeros(l)
  | h :: l => [h] ++ nonzeros(l)
  end.


Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.


Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Fixpoint oddmembers (k:natlist) : natlist :=
  match k with
  | nil => nil
  | h :: l =>
    match evenb(h) with
    |true => oddmembers (l)
    |false => [h] ++ oddmembers (l)
    end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
length(oddmembers(l)).


Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
  Proof. reflexivity. Qed.




Definition bag := natlist.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.


Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | m :: s' =>
    match beq_nat (v) (m) with
    | true => 1 + count (v) (s')
    | false  => count (v) (s')
    end
  end.


Example test_count1: count 1 [1;2;3;1;4;1] = 3.
 Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
 Proof. reflexivity. Qed.


Definition sum : bag -> bag -> bag := app.


Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
 Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := sum s [v].

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.


Definition member (v:nat) (s:bag) : bool :=
match beq_nat (count (v) (s)) (0) with
|true => false
|false => true
end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
match s with
| nil => nil
| x :: n =>
  match beq_nat (x) (v) with
  | true => n
  | false => x :: remove_one (v) (n)
  end
end.


Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
match s with
| nil => nil
| x :: n =>
  match beq_nat (x) (v) with
  | true => remove_all (v) (n)
  | false => x :: remove_all (v) (n)
  end
end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.


Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | x :: n =>
    match member (x) (s2) with
    |true => subset (n) (remove_one x s2)
    |false => false
    end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Theorem bag_theorem : forall x:nat, count(x)(add (x) ([])) = 1.
Proof.
intros x.
simpl. induction x as [|IHx].
- reflexivity.
- simpl. rewrite -> IHIHx. reflexivity.
Qed.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
induction n as [| n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros n m.
induction m as [| m' IHm'].
- simpl. induction n as [| n' IHn'].
+ reflexivity.
+ simpl. rewrite -> IHn'. reflexivity.
- simpl. rewrite <- IHm'. rewrite -> plus_n_Sm. reflexivity.
Qed.


Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length, plus_comm.
    simpl. rewrite -> IHl'. reflexivity. Qed.

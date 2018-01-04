Add LoadPath "/home/anikait/Desktop/coqExamples/unit1".
Add LoadPath "/home/anikait/Desktop/coqExamples/unit2".
Add LoadPath "/home/anikait/Desktop/coqExamples/unit3".

Print LoadPath. 

Require Export natList.
Require Export Basics.
Require Export inductionbasics.

(*List Excercise 1*)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
intros l.
induction l.
- reflexivity.
- simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros l1 l2.
induction l1.
- simpl. induction l2.
+ reflexivity.
+ rewrite -> app_nil_r. reflexivity.
-simpl. induction l2.
+ simpl. rewrite -> app_nil_r. reflexivity.
+ simpl. rewrite -> IHl1. simpl. rewrite <-app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
intros l.
induction l.
- simpl. reflexivity.
- simpl. rewrite -> rev_app_distr. simpl. rewrite -> IHl. reflexivity.
Qed.

 Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
intros l1 l2 l3 l4.
rewrite -> app_assoc.
rewrite -> app_assoc.
reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
intros l1 l2.
induction l1.
- simpl. reflexivity.
- simpl. destruct n.
+ rewrite <- IHl1. reflexivity.
+ simpl. rewrite <- IHl1. reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
match l1 with
|nil => 
  match l2 with 
  |nil => true
  |a => false
  end
|s:: l1' =>
  match l2 with  
  |nil => false 
  |x :: l2' => 
    match beq_nat (x) (s) with
    |true => beq_natlist (l1') (l2')
    |false => false
    end
  end
end.  

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
 Proof. reflexivity. Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
 Proof. reflexivity. Qed.

Theorem equality: forall n, beq_nat n n = true.
Proof.
intros n.
induction n.
- reflexivity.
- simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
 Proof. 
intros l.
induction l.
- reflexivity.
- simpl. rewrite <- IHl. simpl. rewrite -> equality. reflexivity.
Qed.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

(*list exercise 2*)
Theorem count_member_nonzero : forall(s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
intros s.
simpl. reflexivity. Qed.

 Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
intros s.
induction s.
- simpl. reflexivity.
- simpl. destruct n.
+ simpl. rewrite -> ble_n_Sn. reflexivity.
+ simpl. rewrite -> IHs. reflexivity.
Qed.

Theorem rev_injective: forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
intros l1 l2.
intros H.
rewrite <- rev_involutive.
rewrite <- H.
rewrite -> rev_involutive.
reflexivity.
Qed.


(*Options*)

 Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end.

 Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.


Definition hd_error (l : natlist) : natoption :=
match l with
| nil => None
| s :: n => Some s
end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
intros l.
intros default.
destruct l.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

(*Partial Map*)

 Inductive id : Type :=
  | Id : nat -> id.

 Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
intros x.
destruct x.
simpl. rewrite -> equality. reflexivity. 
Qed.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

 Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
intros d x v.
simpl.
destruct x.
simpl.
induction n.
- reflexivity.
- simpl.  rewrite -> equality. reflexivity. 
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
intros d x y o.
simpl.
intros H.
rewrite -> H. reflexivity.
Qed.

Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.

(*no constructor that defines a distinct baz. Such as O in a nat. Thus, 0 elements can be created from this definition.*)






 




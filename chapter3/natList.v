Add LoadPath "/home/anikait/Desktop/coqExamples/unit1".
Add LoadPath "/home/anikait/Desktop/coqExamples/unit2".
Add LoadPath "/home/anikait/Desktop/coqExamples/unit3".

Print LoadPath. 

Require Export natList.
Require Export Basics.
Require Export inductionbasics.

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

Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
intros s.
simpl. reflexivity.

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
simpl. rewrite <- ble_n_Sn. 




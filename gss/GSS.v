(* part 1 *)
Inductive day : Type :=
  | monday    : day
  | tuesday   : day
  | wednesday : day
  | thursday  : day
  | friday    : day
  | saturday  : day
  | sunday    : day.

Definition next_day (d : day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday
  | sunday    => monday
  end.

Compute (next_day friday).

Fixpoint app_times {a : Type} (f : a -> a) (x : a) (n : nat) : a :=
  match n with
  | O => x
  | S n' => app_times f (f x) n'
  end.

Compute (app_times next_day monday 7).

Theorem seven_is_the_charm : forall d, d = app_times next_day d 7.
Proof. intros. destruct d; simpl; reflexivity. Qed.

Print seven_is_the_charm.


Theorem f_thrice :
  forall (A : Type) (f : A -> A) (x : A), f (f (f x)) = app_times f x 3.
Proof. intros. simpl. reflexivity. Qed.

(* part 2 *)
Module Nats.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(* + is defined exactly the same way *)

Theorem plus_0_n : forall n, n = 0 + n.
Proof. intro n. simpl. reflexivity. Qed.

Print plus_0_n.

Theorem plus_n_0 : forall n, n = n + 0.
Proof. intro n. induction n.
  * simpl. reflexivity.
  * simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

(* part 3 *)

Definition group (G : Type) (op : G -> G -> G) (e : G) :=
  (* associativity *)
  (forall (a b c : G), (op (op a b) c) = (op a (op b c)))
  /\
  (* identity *)
  (forall (a : G), (op e a = a) /\ (op a e = a))
  /\
  (* inverse *)
  (forall (a : G), exists (a_inv : G), (op a a_inv = e) /\ (op a_inv a = e)).

Inductive zero_group : Set :=
| E.

Definition zero_op (_ _ : zero_group) : zero_group :=
  E.

Theorem zero_group_is_group : group zero_group zero_op E.
Proof. split.
  * intros. reflexivity.
  * split.
    - intros. split; destruct a; reflexivity.
    - intros. exists E. split; reflexivity.
Qed.

Theorem left_cancellation :
  forall G op e (gp : group G op e) (a b c : G),
    (op a b = op a c) -> (b = c).
Proof. intros.
  destruct gp as [assoc [ident inv]].
  destruct (ident b) as [eq1 eq2].
  destruct (ident c) as [eq3 eq4].
  rewrite <- eq1.
  rewrite <- eq3.
  destruct (inv a) as [a_inv [eq5 eq6]].
  rewrite <- eq6.
  rewrite -> (assoc a_inv a b).
  rewrite -> (assoc a_inv a c).
  rewrite -> H.
  reflexivity. Qed.

Theorem right_cancellation :
  forall G op e (gp : group G op e) (a b c : G),
    (op b a = op c a) -> (b = c).
Proof. intros.
  destruct gp as [assoc [ident inv]].
  destruct (ident b) as [eq1 eq2].
  destruct (ident c) as [eq3 eq4].
  rewrite <- eq2.
  rewrite <- eq4.
  destruct (inv a) as [a_inv [eq5 eq6]].
  rewrite <- eq5.
  rewrite <- (assoc b a a_inv).
  rewrite <- (assoc c a a_inv).
  rewrite <- H.
  reflexivity. Qed.

Theorem idempotent_e :
  forall G op e (gp : group G op e) (x : G),
    (op x x = x) -> (x = e).
Proof. intros. destruct gp as [assoc [ident inv]].
  destruct (inv x) as [x_inv [inv_eq1 inv_eq2]].
  destruct (ident x) as [id_eq1 id_eq2].
  rewrite <- id_eq2.
  rewrite <- inv_eq1.
  rewrite <- (assoc x x x_inv).
  rewrite -> H.
  reflexivity.
Qed.

Print idempotent_e.

Definition group_homomorphism
  (G H : Type) (op_G : G -> G -> G) (op_H : H -> H -> H) (phi : G -> H) :=
  forall (u v : G), phi (op_G u v) = op_H (phi u) (phi v).

Theorem homomorphism_preserves_identity :
  forall G H op_G op_H e_G e_H
    (gp_G : group G op_G e_G) (gp_H : group H op_H e_H)
    (phi : G -> H) (gh : group_homomorphism G H op_G op_H phi),
    (phi e_G) = e_H.
Proof. intros.
  apply (right_cancellation _ _ _ gp_H (phi e_G)).
  destruct gp_G as [assoc_G [ident_G inv_G]].
  destruct gp_H as [assoc_H [ident_H inv_H]].
  destruct (ident_H (phi e_G)) as [eq1 eq2].
  rewrite -> eq1.
  rewrite <- (gh e_G e_G).
  destruct (ident_G e_G) as [eq3 _].
  rewrite -> eq3.
  reflexivity. Qed.

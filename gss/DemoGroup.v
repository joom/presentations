Definition group (G : Set) (op : G -> G -> G) (e : G) :=
  (* associativity *)
  (forall (a b c : G), (op (op a b) c) = (op a (op b c)))
  /\
  (* identity *)
  (forall (a : G), (op e a = a) /\ (op a e = a))
  /\
  (* inverse *)
  (forall (a : G), exists (a_inv : G), (op a a_inv = e) /\ (op a_inv a = e)).

(* an example group *)

Inductive singleton_set : Set :=
| E.

Definition singleton_op (_ _ : singleton_set) : singleton_set :=
  E.

Theorem singleton_set_is_trivial_group : group singleton_set singleton_op E.
Proof. Admitted.

(* General theorems about groups *)

Theorem left_cancellation :
  forall G op e (gp : group G op e) (a b c : G),
    (op a b = op a c) -> (b = c).
Proof. Admitted.

Theorem right_cancellation :
  forall G op e (gp : group G op e) (a b c : G),
    (op b a = op c a) -> (b = c).
Proof. Admitted.

Theorem idempotent_e :
  forall G op e (gp : group G op e) (x : G),
    (op x x = x) -> (x = e).
Proof. Admitted.

Print idempotent_e.

Definition group_homomorphism
  (G H : Set) (op_G : G -> G -> G) (op_H : H -> H -> H) (phi : G -> H) :=
  forall (u v : G), phi (op_G u v) = op_H (phi u) (phi v).

Theorem homomorphism_preserves_identity :
  forall G H op_G op_H e_G e_H
    (gp_G : group G op_G e_G) (gp_H : group H op_H e_H)
    (phi : G -> H) (gh : group_homomorphism G H op_G op_H phi),
    (phi e_G) = e_H.
Proof. Admitted.

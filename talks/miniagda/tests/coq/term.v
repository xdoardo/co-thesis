(* Assume we can do this. *)
Unset Guard Checking.
Fixpoint bad (x : nat) := 1 + (bad x).

Axiom bad_ax : forall x, bad x = 1 + (bad x).

Require Import Lia.

Theorem n_neq_sn : forall (x:nat), (x = S x) -> False.
Proof. intros.  induction x.
  + inversion H.
  + inversion H.  apply IHx in H1. assumption.
Qed.

Theorem zero_eq_one: 0 = 1.
  assert (bad 0 = 1 + (bad 0)).
  + apply bad_ax.
  + destruct bad.
    * simpl in H.  assumption.
    * simpl in H. apply n_neq_sn in H. exfalso. assumption.
Qed.

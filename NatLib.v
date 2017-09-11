Require Import Coq.Arith.Div2.
Require Import Coq.omega.Omega.

Fixpoint mod2 (n : nat) : bool :=
  match n with
    | 0 => false
    | 1 => true
    | S (S n') => mod2 n'
  end.

Ltac rethink :=
  match goal with
    | [ H : ?f ?n = _ |- ?f ?m = _ ] => replace m with n; simpl; auto
  end.

Theorem mod2_S_double : forall n, mod2 (S (2 * n)) = true.
  induction n; simpl; intuition; rethink.
Qed.

Theorem mod2_double : forall n, mod2 (2 * n) = false.
  induction n; simpl; intuition; rewrite <- plus_n_Sm; rethink.
Qed.

Theorem div2_double : forall n, div2 (2 * n) = n.
  induction n; simpl; intuition; rewrite <- plus_n_Sm; f_equal; rethink.
Qed.

Theorem div2_S_double : forall n, div2 (S (2 * n)) = n.
  induction n; simpl; intuition; f_equal; rethink.
Qed.

Fixpoint pow2 (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => 2 * pow2 n'
  end.

Theorem untimes2 : forall n, n + (n + 0) = 2 * n.
  auto.
Qed.

Section strong.
  Variable P : nat -> Prop.

  Hypothesis PH : forall n, (forall m, m < n -> P m) -> P n.

  Lemma strong' : forall n m, m <= n -> P m.
    induction n; simpl; intuition; apply PH; intuition.
    elimtype False; omega.
  Qed.

  Theorem strong : forall n, P n.
    intros; eapply strong'; eauto.
  Qed.
End strong.

Theorem div2_odd : forall n,
  mod2 n = true
  -> n = S (2 * div2 n).
  induction n as [n] using strong; simpl; intuition.

  destruct n as [|n]; simpl in *; intuition.
    discriminate.
  destruct n as [|n]; simpl in *; intuition.
  do 2 f_equal.
  replace (div2 n + S (div2 n + 0)) with (S (div2 n + (div2 n + 0))); auto.
Qed.

Theorem div2_even : forall n,
  mod2 n = false
  -> n = 2 * div2 n.
  induction n as [n] using strong; simpl; intuition.

  destruct n as [|n]; simpl in *; intuition.
  destruct n as [|n]; simpl in *; intuition.
    discriminate.
  f_equal.
  replace (div2 n + S (div2 n + 0)) with (S (div2 n + (div2 n + 0))); auto.
Qed.

Theorem drop_mod2 : forall n k,
  2 * k <= n
  -> mod2 (n - 2 * k) = mod2 n.
  induction n as [n] using strong; intros.

  do 2 (destruct n; simpl in *; repeat rewrite untimes2 in *; intuition).

  destruct k; simpl in *; intuition.

  destruct k; simpl; intuition.
  rewrite <- plus_n_Sm.
  repeat rewrite untimes2 in *.
  simpl; auto.
  apply H; omega.
Qed.

Theorem div2_minus_2 : forall n k,
  2 * k <= n
  -> div2 (n - 2 * k) = div2 n - k.
  induction n as [n] using strong; intros.

  do 2 (destruct n; simpl in *; intuition; repeat rewrite untimes2 in *).
  destruct k; simpl in *; intuition.

  destruct k; simpl in *; intuition.
  rewrite <- plus_n_Sm.
  apply H; omega.
Qed.

Theorem div2_bound : forall k n,
  2 * k <= n
  -> k <= div2 n.
  intros ? n H; case_eq (mod2 n); intro Heq.

  rewrite (div2_odd _ Heq) in H.
  omega.

  rewrite (div2_even _ Heq) in H.
  omega.
Qed.


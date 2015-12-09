Inductive Nat : Set :=
  | Z : Nat
  | S : Nat -> Nat.

Definition one_not_zero_tactic : S Z = Z -> False.
Proof.
  intros.
  inversion H.
Qed.

Print one_not_zero_tactic.

Definition one_not_zero_manual (impossibru: S Z = Z): False :=
  match impossibru in _ = zero return
    (* We can return different things based on what form zero appears in. *)
    match zero with
    (* Of course if zero is Z, we need to return False. And when coq is
       checking this return annotation against the declared type of
       `impossibru`, zero matches with Z, so this needs to return False. *)
    | Z => False
    (* From the point of view of the type checker, then, this branch here
       doesn't match against zero, so it will never be entered. So, we can
       set this return type to anything we want; let's pick `True`. *)
    | S n => True
    end
  with
  (* But here's where the switcheroo happens. When we actually bring
     `eq_refl` into scope, we are binding the `zero` variable above to
     `S Z`. So we only are obligated to provide a value given by the type
     we specified in the `S n` branch, which is super easy! *)
  | eq_refl => I
  end.

Inductive Lt : Nat -> Nat -> Prop :=
  (* n < n + 1 for all n. *)
  | lt_n : forall n, Lt n (S n)
  (* If n1 < n2 and n2 < n3 then n1 < n3. *)
  | lt_trans : forall n1 n2 n3,  Lt n1 n2 -> Lt n2 n3 -> Lt n1 n3.

Arguments lt_n {n}.
Arguments lt_trans {n1 n2 n3} _ _.

(* Proof that one is greater than zero. *)
Definition zero_lt_one : Lt Z (S Z) := lt_n.

(* Proof that one is less than two. *)
Definition one_lt_two : Lt (S Z) (S (S Z)) := lt_n.

Lemma nothing_lt_self: forall n, Lt n n -> False.
Proof.
Admitted.

Lemma one_less_lt: forall n m, Lt (S n) m -> Lt n m.
Proof.
  intros n.
  induction n.
    intros.
    apply (lt_trans zero_lt_one H).
    intros.
    destruct m.

  refine (
    fix proof n m lt :=
      match n


Theorem nothing_lt_zero_tactic: forall n, Lt n Z -> False.
Proof.
  induction n. apply nothing_lt_self.
  intros.

intros. apply inversion H.

Theorem one_not_lt_zero_tactic : Lt (S Z) Z -> False.
Proof.
  intros.
  inversion H.


(* Proof that zero is less than any non-zero number. *)
Definition zero_lt_nonzero : forall n, Lt Z (S n).
Proof.
  refine (
    fix hypo num :=
      match num return Lt Z (S num) with
      | Z   => lt_n
      | S n =>
        (* Use the inductive hypothesis to prove 0 < n + 1. *)
        let z_lt_sn : Lt Z (S n) := hypo n in
        (* Make a proof that n + 1 < n + 2. *)
        let sn_lt_ssn : Lt (S n) (S (S n)) := lt_n in
        (* Use transitivity with the proofs that 0 < n + 1 and n + 1 < n + 2,
           To show that 0 < n + 2. *)
        lt_trans z_lt_sn sn_lt_ssn
      end
  ).
Defined.

(* Proof that one is NOT less than zero. *)
Definition one_not_lt_zero: Lt (S Z) Z -> False.
  refine (
    fun impossibru =>
      match impossibru in Lt zero _ return
        match zero with
        | Z => False
        | S k => False
        end
      with
      | lt_n _ => _
      | lt_trans _ _ _ _ _ => _
      end
  ).

Print zero_lt_nonzero.

Definition zero_lt_two : Lt Z (S (S Z)) := zero_lt_nonzero (S Z).

(* Given that one is greater than zero, gt_trans demonstrates that
   two is greater than one. *)

Definition two_gt_one : Gt (S (S Z)) (S Z) :=
  gt_trans (S Z) Z one_gt_zero.

(* *)
Theorem three_gt_one : Gt (S (S (S Z))) (S Z).
Proof.
  constructor.

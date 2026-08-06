(** Cantor.v - Cantor's diagonal argument in the Rocq Prover

    This file formalizes Cantor's theorem: for any type X, there is no
    surjection X -> (X -> bool). As a corollary, the set of all infinite
    binary sequences (nat -> bool) is uncountable.

    Proof structure:
    1. [diagonal_not_in_range]: The diagonal sequence differs from every
       row of any enumeration - purely constructive, no axioms needed.
    2. [no_surjection_general]: General Cantor's theorem - for any type X,
       no surjection X -> (X -> bool) exists. Constructive.
    3. [no_surjection_nat_seq01]: Specialization to nat - no surjection
       nat -> seq01. Constructive, derived from (2).
    4. [inj_to_nat_implies_surj_from_nat]: An injection seq01 -> nat
       implies a surjection nat -> seq01 - uses classical logic
       (excluded_middle_informative + constructive_indefinite_description
       from ClassicalEpsilon).
    5. [seq01_uncountable]: Main theorem - combines (3) and (4).

    Axioms used: ClassicalEpsilon (constructive_indefinite_description,
    classic via Classical_Prop), consistent with Rocq's type theory.

    Tested on: Rocq Prover 9.1.1 (OCaml 5.4.1)
 *)

From Stdlib Require Import Arith Lia ClassicalEpsilon.

(* ================================================================== *)
(** * Definitions *)

(** A 0-1 sequence is a function [nat -> bool]. *)
Definition seq01 := nat -> bool.

(** A type [X] is countable if there exists an injection [X -> nat]. *)
Definition countable (X : Type) : Prop :=
  exists (f : X -> nat), forall x y : X, f x = f y -> x = y.

(** A function [f : nat -> seq01] is surjective if every sequence
    appears in the enumeration. *)
Definition surjective (f : nat -> seq01) : Prop :=
  forall s : seq01, exists n : nat, f n = s.

(** Boolean negation. *)
Definition flip (b : bool) : bool :=
  match b with true => false | false => true end.

(** The diagonal sequence: for any enumeration [f], the [n]-th element
    of [diagonal f] is the negation of the [n]-th element of [f n].
    This is the core of Cantor's construction. *)
Definition diagonal (f : nat -> seq01) : seq01 :=
  fun n => flip (f n n).

(** A constant sequence (used as a default when a natural number
    is not in the range of an injection). *)
Definition const_seq : seq01 := fun _ => true.

(* ================================================================== *)
(** * The Diagonal Argument (Constructive) *)

(** The diagonal sequence differs from every row of any enumeration.
    This is the heart of Cantor's argument and requires no axioms.

    Proof: If [diagonal f = f n], then evaluating at index [n] gives
    [flip (f n n) = f n n], which is impossible since [flip b <> b]
    for any boolean [b]. *)
Lemma diagonal_not_in_range :
  forall (f : nat -> seq01) (n : nat),
    diagonal f <> f n.
Proof.
  intros f n H.
  assert (H1 : diagonal f n = f n n).
  { rewrite H. reflexivity. }
  unfold diagonal in H1.
  destruct (f n n); discriminate.
Qed.

(* ================================================================== *)
(** * General Cantor's Theorem (Constructive) *)

(** For any type [X], there is no surjection [X -> (X -> bool)].
    This is Cantor's theorem in its full generality: the "powerset"
    of [X] (represented as characteristic functions [X -> bool]) is
    strictly larger than [X] itself.

    Proof: Given a surjection [f : X -> (X -> bool)], the diagonal
    sequence [d x = flip (f x x)] must appear in the range of [f],
    so [f x0 = d] for some [x0]. But then [f x0 x0 = d x0 = flip (f x0 x0)],
    which is impossible. *)
Theorem no_surjection_general :
  forall (X : Type),
    ~ exists f : X -> (X -> bool),
      forall s : X -> bool, exists x : X, f x = s.
Proof.
  intros X Hexf.
  destruct Hexf as [f Hsurj].
  destruct (Hsurj (fun x => flip (f x x))) as [x Hx].
  assert (Hfx : f x x = flip (f x x)).
  { apply (f_equal (fun s => s x)) in Hx. simpl in Hx. exact Hx. }
  destruct (f x x); discriminate.
Qed.

(* ================================================================== *)
(** * No Surjection from Nat to Seq01 (Constructive) *)

(** There is no surjection from [nat] to [seq01].
    This is a corollary of [no_surjection_general] with [X = nat]. *)
Theorem no_surjection_nat_seq01 :
  ~ exists f : nat -> seq01, surjective f.
Proof.
  intro H.
  apply (no_surjection_general nat).
  destruct H as [f Hsurj].
  exists f. exact Hsurj.
Qed.

(* ================================================================== *)
(** * Injection Implies Surjection (Classical) *)

(** If there exists an injection [f : seq01 -> nat], then there exists
    a surjection [g : nat -> seq01]. This requires classical logic.

    Construction: For each [n], decide (classically) whether [n] is in
    the range of [f]. If yes, use [constructive_indefinite_description]
    to extract the unique preimage (uniqueness follows from injectivity).
    If no, return a constant sequence.

    The resulting [g] satisfies [g (f s) = s] for all [s : seq01],
    hence [g] is surjective. *)
Lemma inj_to_nat_implies_surj_from_nat :
  forall (f : seq01 -> nat),
    (forall x y, f x = f y -> x = y) ->
    exists g : nat -> seq01, surjective g.
Proof.
  intros f Hinj.
  (* Classical decidability: for each n, is n in range(f)? *)
  assert (Hdec : forall n : nat,
    {exists s : seq01, f s = n} + {~ exists s : seq01, f s = n}).
  { intro n. apply excluded_middle_informative. }
  (* Construct g: extract preimage if it exists, else default *)
  exists (fun n : nat =>
    match Hdec n with
    | left Hex =>
        match constructive_indefinite_description (fun s => f s = n) Hex
        with exist _ s _ => s end
    | right _ => const_seq
    end).
  (* Prove g is surjective *)
  intro s.
  exists (f s).
  destruct (Hdec (f s)) as [Hex|Hnex].
  - destruct (constructive_indefinite_description (fun s0 => f s0 = f s) Hex)
      as [s0 Hs0].
    assert (s0 = s).
    { apply Hinj. exact Hs0. }
    subst s0. reflexivity.
  - exfalso. apply Hnex. exists s. reflexivity.
Qed.

(* ================================================================== *)
(** * Main Theorem: Seq01 is Uncountable *)

(** The set of 0-1 sequences is uncountable.

    Proof: By contradiction. If [seq01] were countable, there would
    be an injection [f : seq01 -> nat]. By
    [inj_to_nat_implies_surj_from_nat], this gives a surjection
    [g : nat -> seq01], contradicting [no_surjection_nat_seq01]. *)
Theorem seq01_uncountable :
  ~ countable seq01.
Proof.
  unfold countable.
  intro H.
  destruct H as [f Hinj].
  destruct (inj_to_nat_implies_surj_from_nat f Hinj) as [g Hsurj].
  exact (no_surjection_nat_seq01 (ex_intro _ g Hsurj)).
Qed.

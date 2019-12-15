From mathcomp Require Import ssreflect ssrfun.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Export Coq.Unicode.Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Universe Polymorphism.

Notation dfunE := functional_extensionality_dep.
Notation funE  := functional_extensionality.
Notation PropE := propositional_extensionality.
Notation PropI := proof_irrelevance.

Notation "∃! x , P" := (exists! x, P) (at level 200).

Set Primitive Projections.
Record prod@{i} (T S : Type@{i}) := pair {
  fst : T; snd : S
}.
Unset Primitive Projections.
Notation "T * S" := (prod T S) : type_scope.
Notation "p .1" := (fst p) (at level 2, left associativity) : pair_scope.
Notation "p .2" := (snd p) (at level 2, left associativity) : pair_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Arguments fst {_ _} _.
Arguments snd {_ _} _.
(* This declaration helps inferring a pair p when we know what p.1 and p.2
   should be. This typically arises when p : Type * Type. *)
Definition prod_pair@{i} (T S : Type@{i}) (x : T) (y : S) := (x, y).
Canonical prod_pair.

Definition pairf@{i} (T S R : Type@{i}) (f : R → T) (g : R → S) x :=
  (f x, g x).

Set Primitive Projections.
Record sig@{i} (T : Type@{i}) (P : T → Prop) := Sig {
  val  : T;
  valP : P val;
}.
Unset Primitive Projections.

Arguments Sig {T} P val valP.

Notation "{ x | P }" := (sig (fun x => P)) : type_scope.
Notation "{ x : T | P }" := (sig (fun x : T => P)) : type_scope.

Lemma val_inj@{i} (T : Type@{i}) (P : T → Prop) : injective (@val T P).
Proof.
case=> [x xP] [y yP] /= exy; case: y / exy yP => xP'.
by rewrite (PropI _ xP xP').
Qed.

Axiom uchoice : ∀ T (P : T → Prop), (∃! x, P x) → {x | P x}.

Section Quotient.

Universe i.

Context (T : Type@{i}) (R : relation T) `{E : Equivalence _ R}.

Definition quot : Type@{i} := {P : T → Prop | ∃x, P = R x}.

Definition Quot (x : T) : quot := Sig _ (R x) (ex_intro _ x erefl).

Lemma QuotE x y : R x y -> Quot x = Quot y.
Proof.
move=> e; apply: val_inj; apply: funE=> z; apply: PropE.
by rewrite /= e.
Qed.

Section Elim.

Context S (f : T → S) (fP : ∀ x y, R x y → f x = f y).

Lemma quot_rec_subproof (q : quot) : ∃! a, ∃ x, val q x ∧ a = f x.
Proof.
case: q=> _ /= [x ->]; exists (f x); split=> [|a].
  exists x; split; auto; reflexivity.
by case=> x' [x'P ->]; apply: fP.
Qed.

Definition quot_rec (q : quot) :=
  val (uchoice (quot_rec_subproof q)).

Lemma quot_recE x : quot_rec (Quot x) = f x.
Proof.
rewrite /quot_rec; case: uchoice=> a [/= x' [x'P ->]].
by symmetry; apply: fP.
Qed.

Lemma quotP g : (∀ x, g (Quot x) = f x) -> g = quot_rec.
Proof.
rewrite /quot_rec=> gP; apply: funE => q.
case: uchoice=> _ [x [/= xP ->]]; rewrite -gP; congr g.
apply: val_inj; apply: funE=> x'.
case: q xP=> /= _ [/= x'' ->] e.
apply: PropE; by rewrite e.
Qed.

End Elim.

End Quotient.
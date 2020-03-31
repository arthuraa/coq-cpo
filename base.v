From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Export Coq.Unicode.Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Universe Polymorphism.
Set Primitive Projections.

Obligation Tactic := idtac.

Notation dfunE := functional_extensionality_dep.
Notation  funE := functional_extensionality.
Notation PropE := propositional_extensionality.
Notation PropI := proof_irrelevance.

Declare Scope cast_scope.
Delimit Scope cast_scope with CAST.
Local Open Scope cast_scope.

Definition cast@{u} (T S : Type@{u}) (e : T = S) : T -> S :=
  match e with erefl => id end.

Arguments cast {_ _} e _.

Notation "e1 * e2" := (etrans e1 e2)
  (at level 40, left associativity) : cast_scope.
Notation "e ^-1" := (esym e) : cast_scope.

(* We redefine some constants of the standard library here to avoid problems
   with universe inconsistency and opacity. *)

Definition congr1 T S (f : T -> S) x y (e : x = y) : f x = f y :=
  match e with erefl => erefl end.

Notation "f @@ e" := (congr1 f e) (at level 25, right associativity) : cast_scope.

Definition congr1V T S (f : T -> S) x y (e : x = y) : (f @@ e)^-1 = f @@ e^-1 :=
  match e with erefl => erefl end.

Definition congr1CE (T S : Type) (a : S) x y (e : x = y) :
  (λ _ : T, a) @@ e = erefl :=
  match e with erefl => erefl end.

Definition congr1D T S (f : T → S) x y z (exy : x = y) (eyz : y = z) :
  f @@ (exy * eyz) = f @@ exy * f @@ eyz :=
  match eyz with erefl => erefl end.

Definition etransV T (x y z : T) (p : x = y) (q : y = z) : (p * q)^-1 = q^-1 * p^-1 :=
  match p in _ = y return forall q : y = z, (p * q)^-1 = q^-1 * p^-1 with
  | erefl => fun q => match q with erefl => erefl end
  end q.

Definition etrans1p T (x y : T) (p : x = y) : erefl * p = p :=
  match p with erefl => erefl end.

Definition etransVp T (x y : T) (p : x = y) : p^-1 * p = erefl :=
  match p with erefl => erefl end.

Definition etranspV T (x y : T) (p : x = y) : p * p^-1 = erefl :=
  match p with erefl => erefl end.

Definition congr2 T1 T2 S (f : T1 -> T2 -> S) x1 y1 x2 y2 (e1 : x1 = y1) (e2 : x2 = y2) : f x1 x2 = f y1 y2 :=
  congr1 (f x1) e2 * congr1 (fun a => f a y2) e1.

Definition castD T S R (p : T = S) (q : S = R) :
  forall a, cast (p * q) a = cast q (cast p a) :=
  match q with erefl => fun a => erefl end.

Notation "'∃' ! x .. y , p" :=
  (ex (unique (fun x => .. (ex (unique (fun y => p))) ..)))
  (at level 200, x binder, right associativity,
   format "'[' '∃'  !  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Record prod@{i} (T S : Type@{i}) := pair {
  fst : T; snd : S
}.
Notation "T * S" := (prod T S) : type_scope.
Notation "p .1" := (fst p) (at level 2, left associativity) : pair_scope.
Notation "p .2" := (snd p) (at level 2, left associativity) : pair_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Declare Scope coq_prod_scope.
Delimit Scope coq_prod_scope with coq_prod.
Notation "T * S" := (Datatypes.prod T S) : coq_prod_scope.
Notation "p .1" := (Datatypes.fst p) (at level 2, left associativity) : coq_prod_scope.
Notation "p .2" := (Datatypes.snd p) (at level 2, left associativity) : coq_prod_scope.
Notation "( x , y , .. , z )" := (Datatypes.pair .. (Datatypes.pair x y) .. z) : coq_prod_scope.

Arguments fst {_ _} _.
Arguments snd {_ _} _.
(* This declaration helps inferring a pair p when we know what p.1 and p.2
   should be. This typically arises when p : Type * Type. *)
Definition prod_pair@{i} (T S : Type@{i}) (x : T) (y : S) := (x, y).
Canonical prod_pair.

Definition pairf@{i} (T S R : Type@{i}) (f : R → T) (g : R → S) x :=
  (f x, g x).

Record sub@{i} (T : Type@{i}) (P : T → Prop) := Sub {
  val  : T;
  valP : P val;
}.

Arguments Sub {T P} val valP.

Notation "{ x | P }" := (sub (fun x => P)) : type_scope.
Notation "{ x : T | P }" := (sub (fun x : T => P)) : type_scope.

Lemma val_inj@{i} (T : Type@{i}) (P : T → Prop) : injective (@val T P).
Proof.
case=> [x xP] [y yP] /= exy; case: y / exy yP => xP'.
by rewrite (PropI _ xP xP').
Qed.

Notation "{ 'lift' x 'to' S }" :=
  ((λ (P : _ → Prop) (f : S → {y | P y}), P x) _ id)
  (at level 0) : type_scope.

Axiom uchoice : ∀ T (P : T → Prop), (∃! x, P x) → {x | P x}.

Lemma uchoiceE T (P : T → Prop) (e : ∃!x, P x) x : P x → val (uchoice e) = x.
Proof.
case: uchoice=> y yP /= xP.
by case: e=> z [_ zP]; rewrite -(zP _ yP) -(zP _ xP).
Qed.

Section Quotient.

Universe i.

Context (T : Type@{i}).

Record equiv : Type@{i} := Equiv {
  equiv_rel :> T → T → Prop;
  _         :  ∀ x, equiv_rel x x;
  _         :  ∀ x y, equiv_rel x y → equiv_rel y x;
  _         :  ∀ x y z, equiv_rel x y → equiv_rel y z → equiv_rel x z;
}.

Context (R : equiv).

Global Instance equivP : Equivalence R.
Proof. by case: R. Qed.

Unset Elimination Schemes.
Record quot : Type@{i} := Quot_ {of_quot : {P : T → Prop | ∃x, P = R x}}.
Set Elimination Schemes.

Definition Quot (x : T) : quot := Quot_ (Sub (R x) (ex_intro _ x erefl)).

Lemma QuotE x y : R x y -> Quot x = Quot y.
Proof.
move=> e; congr Quot_; apply: val_inj; apply: funE=> z; apply: PropE.
by rewrite /= e.
Qed.

Lemma Quot_inj x y : Quot x = Quot y -> R x y.
Proof.
move=> e; rewrite -[R x y]/(val (of_quot (Quot x)) y) e //=; reflexivity.
Qed.

Section Elim.

Context (S : quot → Type) (f : ∀ x, S (Quot x)).
Context (fP : ∀ x y (exy : R x y), cast (S @@ QuotE exy) (f x) = f y).

Lemma quot_rect_subproof (q : quot) :
  ∃! a, ∃ x (exq : Quot x = q), a = cast (S @@ exq) (f x).
Proof.
have {q} [x ->]: ∃x, q = Quot x.
  by case: q=> [[P [x xP]]]; exists x; congr Quot_; apply: val_inj.
exists (f x); split=> [|a]; first by exists x, erefl.
case=> y [eyx -> {a}].
by rewrite (PropI _ eyx (QuotE (Quot_inj eyx))) fP.
Qed.

Definition quot_rect q := val (uchoice (quot_rect_subproof q)).

Lemma quot_rectE x : quot_rect (Quot x) = f x.
Proof.
rewrite /quot_rect; case: uchoice=> _ [y [eyx /= ->]].
by rewrite (PropI _ eyx (QuotE (Quot_inj eyx))) fP.
Qed.

End Elim.

Definition quot_ind (P : quot → Prop) := @quot_rect P.

Section Rec.

Context S (f : T → S) (fP : ∀ x y, R x y → f x = f y).

Definition quot_rec :=
  @quot_rect (λ _, S) f
    (λ x y exy, (λ p, cast p (f x)) @@ congr1CE S (QuotE exy) * fP exy).

Lemma quot_recE x : quot_rec (Quot x) = f x.
Proof. by rewrite /quot_rec quot_rectE. Qed.

End Rec.

End Quotient.

Section Sigma.

Universe u.

Context (T : Type@{u}) (S : T → Type@{u}).

Record sig : Type := Sig { sig1 : T; sig2 : S sig1 }.

Lemma sig_inj x (y1 y2 : S x) : Sig y1 = Sig y2 → y1 = y2.
Proof.
move=> e.
have ->: y1 = cast (S @@ (sig1 @@ e^-1)) y2.
  by rewrite -[y2]/(Sig y2).(sig2); case: _ / e.
by rewrite (PropI _ (sig1 @@ e^-1) erefl).
Qed.

End Sigma.

Arguments Sig {T S} _ _.

Notation "{ x & P }"     := (sig (fun x => P)) : type_scope.
Notation "{ x : T & P }" := (sig (fun x : T => P)) : type_scope.
Notation "{ ' pat : T & P }" := (sig (fun pat : T => P)) : type_scope.

Section Singletons.

Variable T : Type.

Variant subsing :=
  Subsing of {X : T -> Prop | forall x y, X x -> X y -> x = y}.

Definition pred_of_subsing (X : subsing) :=
  let: Subsing X := X in val X.

Coercion pred_of_subsing : subsing >-> Funclass.

Lemma subsingP (X : subsing) x y : X x -> X y -> x = y.
Proof. case: X=> [X]; exact: (valP X). Qed.

Lemma eq_subsing (X Y : subsing) :
  (forall x, X x <-> Y x) <-> X = Y.
Proof.
split=> [|-> //]; case: X Y=> [X] [Y] /= e.
by congr Subsing; apply/val_inj/funE=> x; apply/PropE.
Qed.

Program Definition subsing_of (x : T) :=
  Subsing (Sub (eq x) _).

Next Obligation. by move=> /= ??? ->. Qed.

Lemma subsing_of_inj : injective subsing_of.
Proof. by move=> x y [->]. Qed.

Lemma in_subsing (X : subsing) (x : T) : X x -> X = subsing_of x.
Proof.
move=> Xx; apply/eq_subsing=> y; split=> [|<- //].
exact: (subsingP Xx).
Qed.

Program Definition subsing0 : subsing :=
  Subsing (Sub (fun _ : T => False) (fun _ _ (H : False) => match H with end)).

End Singletons.

Arguments Subsing {_} _.
Arguments subsing0 {_}.
Arguments subsing_of {_}.

Section SingletonMap.

Variables T S : Type.

Program Definition liftss (f : T -> subsing S) (x : subsing T) :=
  Subsing (Sub (fun y => exists2 x0, x x0 & f x0 y) _).

Next Obligation.
move=> f x y1 y2 [x1 x1P1 x1P2] [x2 /(subsingP x1P1) <- x2P2].
exact: (subsingP x1P2 x2P2).
Qed.

Definition mapss (f : T -> S) := liftss (subsing_of \o f).

End SingletonMap.

Lemma liftss1 T : @liftss T T subsing_of = id.
Proof.
apply/funE=> X.
apply/eq_subsing=> x; split; first by case=> y Xy <-.
by move=> ?; exists x.
Qed.

Lemma liftss_comp T S R (f : S -> subsing R) (g : T -> subsing S) :
  liftss f \o liftss g = liftss (liftss f \o g).
Proof.
apply/funE=> X; apply/eq_subsing=> z; split.
- by case=> y [x Xx gx] fy; exists x=> //; exists y.
- by case=> x Xx [y gx fy]; exists y=> //; exists x.
Qed.

Lemma liftss_comp1 T S (f : T -> subsing S) : liftss f \o subsing_of = f.
Proof.
apply/funE=> /= x.
apply/eq_subsing=> y; split; first by case => _ <-.
by move=> ?; exists x.
Qed.

Lemma liftssB T S (f : T -> subsing S) : liftss f subsing0 = subsing0.
Proof. by apply/eq_subsing=> x; split=> [[? []]|[]]. Qed.

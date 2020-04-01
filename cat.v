From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype.
From void Require Import void.
From cpo Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Cumulativity Weak Constraints.
Set Universe Minimization ToSet.
Obligation Tactic := idtac.

Module Cat.

Section WithUniverse.

Universe u.

Section ClassDef.

Variable T    : Type@{u}.
Variable hom  : T → T → Type@{u}.
Variable comp : ∀ X Y Z, hom Y Z → hom X Y → hom X Z.
Variable id   : ∀ X, hom X X.
Arguments id {_}.

Record axioms : Prop := Axioms {
  _ : ∀ X Y (f : hom X Y), comp id f = f;
  _ : ∀ X Y (f : hom X Y), comp f id = f;
  _ : ∀ X Y Z W (h : hom Z W) (g : hom Y Z) (f : hom X Y),
          comp h (comp g f) = comp (comp h g) f;
}.

Set Primitive Projections.

(** We add a symmetric version of the associativity axiom so that
    taking opposites is an involution definitionally. *)

Record axioms_ : Prop := Axioms_ {
  comp1f : ∀ X Y (f : hom X Y), comp id f = f;
  compf1 : ∀ X Y (f : hom X Y), comp f id = f;
  compA  : ∀ X Y Z W (h : hom Z W) (g : hom Y Z) (f : hom X Y),
             comp h (comp g f) = comp (comp h g) f;
  compAV : ∀ X Y Z W (h : hom Z W) (g : hom Y Z) (f : hom X Y),
             comp (comp h g) f = comp h (comp g f)
}.

Lemma pack_axioms : axioms -> axioms_.
Proof. by case=> H1 H2 H3; split. Qed.

End ClassDef.

Record mixin_of (T : Type@{u}) (hom : T -> T -> Type@{u}) := Mixin_ {
  comp  : ∀ X Y Z, hom Y Z -> hom X Y -> hom X Z;
  id    : ∀ X, hom X X;
  compP : axioms_ comp id
}.

Definition Mixin (T : Type@{u}) (hom : T -> T -> Type@{u}) comp id compP :=
  @Mixin_ T hom comp id (pack_axioms compP).

Notation class_of := mixin_of (only parsing).

Record type : Type := Pack {
  obj : Type@{u};
  hom : obj -> obj -> Type@{u};
  class : mixin_of hom
}.
Local Coercion obj : type >-> Sortclass.
Variables (T : Type@{u}) (cT : type).
Definition clone h c of phant_id class c := @Pack T h c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Unset Primitive Projections.

End WithUniverse.

Module Exports.
Coercion obj : type >-> Sortclass.
Coercion hom : type >-> Funclass.
Notation catType := type.
Notation CatMixin := Mixin.
Notation CatType T h m := (@Pack T h m).
End Exports.

End Cat.

Export Cat.Exports.

Section CatTheory.

Universe u.

Variable C : catType@{u}.

Definition hom := @Cat.hom@{u} C.
Definition comp := @Cat.comp@{u} _ _ (@Cat.class C).
Definition cat_id := @Cat.id@{u} _ _ (@Cat.class C).
Arguments cat_id {_}.

Local Notation "g ∘ f" := (comp g f) (at level 40, left associativity).
Local Notation "1" := cat_id.

Lemma comp1f X Y (f : C X Y) : 1 ∘ f = f.
Proof. by rewrite /comp /cat_id; case: (@Cat.class C)=> ?? []. Qed.

Lemma compf1 X Y (f : C X Y) : f ∘ 1 = f.
Proof. by rewrite /comp /cat_id; case: (@Cat.class C)=> ?? []. Qed.

Lemma compA X Y Z W (h : C Z W) (g : C Y Z) (f : C X Y) :
  h ∘ (g ∘ f) = h ∘ g ∘ f.
Proof. by rewrite /comp; case: (@Cat.class C)=> ?? []. Qed.

Definition compp X Y Z (p : C Y Z * C X Y) : C X Z := p.1 ∘ p.2.

Definition has_inverse X Y (f : C X Y) : Prop :=
  ∃g, f ∘ g = 1 ∧ g ∘ f = 1.

Lemma inverse_def X Y (f : C X Y) :
  has_inverse f → ∃! g, f ∘ g = 1 ∧ g ∘ f = 1.
Proof.
case=> g [fg gf]; exists g; split; first by split.
by move=> h [fh hf]; rewrite -[LHS]comp1f -hf -compA fg compf1.
Qed.

Definition inverse X Y (f : C X Y) (fP : has_inverse f) : C Y X :=
  val (uchoice (inverse_def fP)).

Lemma inverseK X Y (f : C X Y) (fP : has_inverse f) : inverse fP ∘ f = 1.
Proof. by rewrite /inverse; case: uchoice=> /= g []. Qed.

Lemma inverseKV X Y (f : C X Y) (fP : has_inverse f) : f ∘ inverse fP = 1.
Proof. by rewrite /inverse; case: uchoice=> /= g []. Qed.

Record iso X Y := Iso {
  iso1  : C X Y;
  iso2  : C Y X;
  iso1K : iso2 ∘ iso1 = 1;
  iso2K : iso1 ∘ iso2 = 1
}.

Definition iso_of_eq X Y (e : X = Y) : C X Y :=
  match e with erefl => cat_id end.

Lemma iso_of_eqK X Y (e : X = Y) : iso_of_eq e ∘ iso_of_eq (esym e) = 1.
Proof. by case: Y / e; rewrite comp1f. Qed.

Lemma iso_of_eqKV X Y (e : X = Y) : iso_of_eq (esym e) ∘ iso_of_eq e = 1.
Proof. by case: Y / e; rewrite comp1f. Qed.

Lemma iso_of_eqD X Y Z (e1 : Y = Z) (e2 : X = Y) :
  iso_of_eq (etrans e2 e1) = iso_of_eq e1 ∘ iso_of_eq e2.
Proof. by case: Z / e1 e2 => e2; rewrite /= comp1f. Qed.

Lemma sig_isoL X Y Z (e : Y = Z) (f : C X Y) :
  Sig (X, Z) (iso_of_eq e ∘ f) = Sig (X, Y) f :> { '(X, Y) : _ & C X Y}.
Proof. by case: Z / e; rewrite comp1f. Qed.

Lemma sig_isoR X Y Z (f : C Y Z) (e : X = Y) :
  Sig (X, Z) (f ∘ iso_of_eq e) = Sig (Y, Z) f :> { '(X, Y) : _ & C X Y}.
Proof. by move: f; case: Y / e=> f; rewrite compf1. Qed.

Definition sig_iso@{} := (sig_isoL, sig_isoR)%coq_prod.

(* FIXME: This does not introduce an extra universe level, but I cannot add a @{} annotation *)
Lemma eq_hom X Y (f g : C X Y) :
  Sig (X, Y) f = Sig (X, Y) g :> ({'(X, Y) :  C * C & C X Y}) → f = g.
Proof. exact: sig_inj. Qed.

End CatTheory.

Notation "g ∘ f" := (comp g f) (at level 40) : cat_scope.
Notation "1" := (@cat_id _ _) : cat_scope.
Arguments cat_id {_}.
Arguments iso_of_eq {_ _ _} _.

Open Scope cat_scope.

Section Opposite.

Universe u.

Variable C : catType@{u}.

Definition op (T : Type@{u}) : Type@{u} := T.
Definition op_hom (T : Type@{u}) (hom : T -> T -> Type@{u}) X Y : Type@{u} :=
  hom Y X.
Definition op_comp@{} X Y Z (f : op_hom C Y Z) (g : op_hom C X Y) : op_hom C X Z :=
  g ∘ f.
Definition op_id@{} X : op_hom C X X := cat_id X.

Definition op_catMixin :=
  @Cat.Mixin_ (op C) (op_hom C) op_comp op_id
             (Cat.Axioms_
                (fun X Y =>
                     @Cat.compf1 _ _ _ _ (Cat.compP (Cat.class C)) Y X)
                (fun X Y =>
                   @Cat.comp1f _ _ _ _ (Cat.compP (Cat.class C)) Y X)
                (fun X Y Z W h g f =>
                   @Cat.compAV _ _ _ _ (Cat.compP (Cat.class C))
                               W Z Y X f g h)
                (fun X Y Z W h g f =>
                   @Cat.compA  _ _ _ _ (Cat.compP (Cat.class C))
                               W Z Y X f g h)).

Canonical op_catType :=
  CatType (op C) (op_hom C) op_catMixin.

(** Identities to help type checking *)
Definition Op (T : Type@{u}) (x : T) : op T := x.
Definition of_op (T : Type@{u}) (hom : T -> T -> Type@{u}) X Y :
  op_hom hom X Y -> hom Y X :=
  id.
Definition to_op (T : Type@{u}) (hom : T -> T -> Type@{u}) X Y :
  hom X Y -> op_hom hom Y X := id.
Lemma op_compE X Y Z (f : op_hom C Y Z) (g : op_hom C X Y) :
  f ∘ g = of_op g ∘ of_op f.
Proof. by []. Qed.

Lemma op_idE (X : C) : @cat_id op_catType X = cat_id X.
Proof. by []. Qed.

End Opposite.

Notation "C '^op'" := (op_catType C)
  (at level 2, left associativity, format "C ^op") : cat_scope.

Section Sets.

Universe u v.
Constraint u < v.

Definition sfun_catMixin :=
  @Cat.Mixin_@{v}
     Type@{u} (λ T S, T → S) (fun _ _ _ f g x => f (g x)) (fun _ x => x)
     (@Cat.Axioms_
        Type@{u} _ (fun _ _ _ f g x => f (g x)) (fun _ x => x)
        (fun _ _ _ => erefl) (fun _ _ _ => erefl)
        (fun _ _ _ _ _ _ _ => erefl) (fun _ _ _ _ _ _ _ => erefl)).

Canonical Sets@{} := CatType Type@{u} _ sfun_catMixin.

Lemma SetsE X Y Z (f : Sets Y Z) (g : Sets X Y) (x : X) : (f ∘ g) x = f (g x).
Proof. by []. Qed.

Lemma Sets1 (X : Sets) (x : X) : cat_id X x = x.
Proof. by []. Qed.

Lemma Sets_has_inverse X Y (f : Sets X Y) :
  (∀ y, ∃! x, f x = y) → has_inverse f.
Proof.
move=> fP; exists (λ y, val (uchoice (fP y))); split; apply/funE.
  by move=> y; rewrite SetsE Sets1; case: uchoice.
by move=> x; rewrite SetsE Sets1 (uchoiceE (fP (f x)) erefl).
Qed.

End Sets.

Section Functor.

Universe u.

Context (C D : catType@{u}).

Record functor@{} : Type@{u} := Functor {
  fobj  :> C → D;
  fmap  :  ∀ X Y, C X Y → D (fobj X) (fobj Y);
  fmap1 :  ∀ X, fmap 1 = 1 :> D (fobj X) (fobj X);
  fmapD :  ∀ X Y Z (f : C Y Z) (g : C X Y),
             fmap (f ∘ g) = fmap f ∘ fmap g;
}.

Definition functor_of of phant (C -> D) := functor.
Identity Coercion functor_of_functor : functor_of >-> functor.
Notation "{ 'functor' T }" := (functor_of (Phant T))
  (at level 0, format "{ 'functor'  T }") : type_scope.

Open Scope cast_scope.

Lemma eq_functor@{} (F G : functor) (eFG : ∀ X, F X = G X) :
  (∀ X Y (f : C X Y),
    iso_of_eq (eFG Y) ∘ fmap F f = fmap G f ∘ iso_of_eq (eFG X)) →
  F = G.
Proof.
case: F G eFG=> [F0 F1 Fmap1 FmapD] [G0 G1 Gmap1 GmapD] /= e0.
have e0': F0 = G0 by exact: funE.
case: G0 / e0' e0 G1 Gmap1 GmapD=> e0 F1' Fmap1' FmapD' /= e1.
have {}e1: F1 = F1'.
  apply/dfunE=> X; apply/dfunE=> Y; apply/funE=> f; move: (e1 X Y f).
  by rewrite (PropI _ (e0 Y) erefl) (PropI _ (e0 X) erefl) comp1f compf1.
case: F1' / e1 Fmap1' FmapD' => Fmap1' FmapD'.
by rewrite (PropI _ FmapD FmapD') (PropI _ Fmap1 Fmap1').
Qed.

Implicit Types F G H : functor.

Lemma fmap_iso_of_eq F X Y (e : X = Y) :
  fmap F (iso_of_eq e) = iso_of_eq (F @@ e).
Proof. by case: Y / e=> /=; rewrite fmap1. Qed.

Record nat_trans@{} F G : Type@{u} := NatTrans {
  of_nat_trans :
    {η : ∀ X, D (F X) (G X) |
     ∀ X Y (f : C X Y), fmap G f ∘ η X = η Y ∘ fmap F f}
}.

Coercion of_nat_trans : nat_trans >-> sub.

Definition fun_of_nat_trans (F G : functor) (η : nat_trans F G) :=
  let: NatTrans η := η in val η.

Coercion fun_of_nat_trans : nat_trans >-> Funclass.

Lemma nat_transP F G (η : nat_trans F G) X Y (f : C X Y) :
  fmap G f ∘ η X = η Y ∘ fmap F f.
Proof. case: η=> η; exact: (valP η X Y f). Qed.

Lemma eq_nat_trans F G (η ε : nat_trans F G) : (forall X, η X = ε X) ↔ η = ε.
Proof.
split; last by move=> ->.
case: η ε=> [η] [ε] /= eηε; congr NatTrans.
by apply: val_inj; apply: dfunE.
Qed.

Program Definition nat_trans_comp@{} F G H
  (η : nat_trans G H) (ε : nat_trans F G) : nat_trans F H :=
  NatTrans (Sub (fun X => η X ∘ ε X) _).

Next Obligation.
move=> F G H [η] [ε] X Y f.
by rewrite compA (valP η) -compA (valP ε) compA.
Qed.

Program Definition nat_trans_id@{} F : nat_trans F F :=
  NatTrans (Sub (fun X => 1) _).

Next Obligation. by move=> F X Y f /=; rewrite comp1f compf1. Qed.

Lemma nat_trans_compP@{} : Cat.axioms@{u} nat_trans_comp nat_trans_id.
Proof.
split.
- by move=> F G [η]; apply/eq_nat_trans=> X /=; rewrite comp1f.
- by move=> F G [η]; apply/eq_nat_trans=> X /=; rewrite compf1.
- by move=> F G H K [η] [ε] [θ]; apply/eq_nat_trans=> X /=; rewrite compA.
Qed.

Definition functor_catMixin@{} := CatMixin nat_trans_compP@{}.
Canonical Fun@{} :=
  CatType functor nat_trans functor_catMixin@{}.

Lemma nat_trans_idE@{} (F : functor) X : cat_id F X = 1.
Proof. by []. Qed.

Lemma nat_trans_compE@{} F G H (η : nat_trans G H) (ε : nat_trans F G) X :
  (η ∘ ε) X = η X ∘ ε X.
Proof. by []. Qed.

Lemma has_inverse_nat_trans@{} F G (η : nat_trans F G) (X : C) :
  has_inverse η → has_inverse (η X).
Proof.
move=> ηP; exists (inverse ηP X).
by rewrite -2!nat_trans_compE inverseK inverseKV.
Qed.

Lemma nat_trans_has_inverse@{} F G (η : nat_trans F G) :
  (∀ X, has_inverse (η X)) → has_inverse η.
Proof.
move=> ηP; pose ε X := inverse (ηP X).
have εP: ∀ X Y f, fmap F f ∘ ε X = ε Y ∘ fmap G f.
  move=> X Y f; rewrite -[fmap F f]comp1f -(inverseK (ηP Y)).
  by rewrite -[_ ∘ fmap F f]compA -nat_transP -!compA inverseKV compf1.
by exists (NatTrans (Sub ε εP)); split; apply/eq_nat_trans=> X;
rewrite nat_trans_compE /= ?inverseK ?inverseKV.
Qed.

End Functor.

Notation "{ 'functor' T }" := (functor_of (Phant T))
  (at level 0, format "{ 'functor'  T }") : type_scope.

Arguments fmap {_ _} _ {_ _}.
Arguments Functor {_ _} _ _ _ _.

Definition op_functor@{u} (C D : catType@{u}) (F : functor C D) :
  functor (op_catType C) (op_catType D) :=
  Functor (fun (X : op C) => Op (F X))
          (fun (X Y : C) (f : C Y X) => fmap F f)
          (fun _ => fmap1 F _)
          (fun _ _ _ _ _ => fmapD F _ _).

Section ConstFunctor.

Universes u.

Context (C D : catType@{u}).

Open Scope cast_scope.

Definition const_functor@{} (X : D) : functor C D :=
  Functor (λ _, X) (λ _ _ _, 1) (λ _, erefl) (λ _ _ _ _ _, (comp1f 1)^-1).

Program Definition const_functor_fmap@{} (X Y : D) (f : D X Y) :
  nat_trans (const_functor X) (const_functor Y) :=
  NatTrans (Sub (λ X : C, f) (λ (A B : C) (g : C A B), comp1f f * (compf1 f)^-1)).

Program Definition const_functor_functor : functor D (Fun C D) :=
  Functor const_functor (@const_functor_fmap) _ _.

Next Obligation.
by move=> X; apply/eq_nat_trans=> A /=.
Qed.

Next Obligation.
by move=> X Y Z f g; apply/eq_nat_trans=> A /=.
Qed.

End ConstFunctor.

Section CatCat.

Universe u.

Definition functor_id@{} (C : catType@{u}) : functor C C :=
  @Functor C C id (fun _ _ => id) (fun _ => erefl) (fun _ _ _ _ _ => erefl).

Program Definition functor_comp@{}
  (C D E : catType@{u}) (F : functor D E) (G : functor C D) : functor C E :=
  Functor (fun X => F (G X)) (fun _ _ f => fmap F (fmap G f)) _ _.

Next Obligation. by move=> C D E F G X /=; rewrite !fmap1. Qed.
Next Obligation. by move=> C D E F G X Y Z f g /=; rewrite !fmapD. Qed.

Lemma functor_compP@{v} : @Cat.axioms@{v} _ _ functor_comp functor_id.
Proof.
by split; move=> *; apply/eq_functor=> * /=; rewrite comp1f compf1.
Qed.

Definition cat_catMixin@{v} := CatMixin functor_compP@{v}.
Canonical Cat@{v} :=
  Eval hnf in CatType catType functor cat_catMixin@{v}.

End CatCat.

Section ObjFunctor.

Universe u v.
Constraint u < v.

Definition obj_functor@{} : functor Cat@{u v} Sets@{u v} :=
  Functor (λ C, Cat.obj C) (λ C D F, fobj F) (λ C, erefl) (λ C D E F G, erefl).

End ObjFunctor.

Section Discrete.

Universes u.

Variable T : Type@{u}.

Set Primitive Projections.
Record disc : Type@{u} := Disc {
  of_disc : T;
}.
Unset Primitive Projections.

Definition disc_hom (x y : disc) := x = y.
Definition disc_id (x : disc) : disc_hom x x := erefl.
Definition disc_comp (x y z : disc)
                     (f : disc_hom y z) (g : disc_hom x y) : disc_hom x z :=
  etrans g f.

Lemma disc_compP : Cat.axioms@{u} disc_comp disc_id.
Proof.
split=> //.
- by move=> X Y f; case: Y / f.
- by move=> A B C D h g f; case: D / h.
Qed.

Definition disc_catMixin := CatMixin@{u} disc_compP.
Canonical disc_catType : catType@{u} :=
  Eval hnf in CatType disc disc_hom disc_catMixin.

Open Scope cast_scope.

Program Definition disc_lift (C : catType@{u}) (f : T → C) :
  functor@{u} disc_catType C :=
  Functor (λ x, f x.(of_disc)) (λ x y exy, iso_of_eq (_ @@ exy)) (λ x, erefl) _.

Next Obligation.
by move=> C f x y z eyx exy; rewrite /= congr1D iso_of_eqD.
Qed.

End Discrete.

Section Indiscrete.

Universe i.

Variable T : Type@{i}.

Definition indisc_obj : Type@{i} := T.
Definition indisc_hom (_ _ : T) : Set := unit.
Definition indisc_id (_ : T) := tt.
Definition indisc_comp (_ _ _ : T) (x y : unit) := tt.

Lemma indisc_compP : Cat.axioms@{i} indisc_comp indisc_id.
Proof. by rewrite /indisc_comp /indisc_id; split=> // ?? []. Qed.

Definition indisc_catMixin := CatMixin@{i} indisc_compP.
Canonical indisc_catType : catType@{i} :=
  Eval hnf in CatType indisc_obj indisc_hom indisc_catMixin.

End Indiscrete.

Canonical unit_catType : catType@{Set} :=
  CatType unit (@indisc_hom@{Set} unit) (indisc_catMixin@{Set} unit).

Section Yoneda.

Universe u v.
Constraint u < v.

Context (C : catType@{u}).

Definition yoneda_fobj@{} (X : C) : C^op → Type@{u} := λ Y : C^op, @hom C Y X.
Definition yoneda_fmap@{} (X : C) (Y Z : C^op) : C^op Y Z → Sets@{u v} (yoneda_fobj X Y) (yoneda_fobj X Z) :=
  λ f g, g ∘ f.

Lemma yoneda_fmap1@{} (X : C) (Y : C^op) : @yoneda_fmap X Y Y 1 = 1.
Proof. by rewrite /yoneda_fmap; apply/funE=> f; rewrite compf1. Qed.

Lemma yoneda_fmapD@{} (X : C) (Y Z W : C^op) (f : C^op Z W) (g : C^op Y Z) :
  @yoneda_fmap X _ _ (f ∘ g) = @yoneda_fmap X _ _ f ∘ @yoneda_fmap X _ _ g.
Proof.
by rewrite /yoneda_fmap; apply/funE=> h /=; rewrite compA.
Qed.

Definition yoneda@{} X :=
  Functor (@yoneda_fobj X) (@yoneda_fmap X) (@yoneda_fmap1 X) (@yoneda_fmapD X).

Definition yoneda_in@{} X (F : functor C^op Sets) (η : nat_trans (yoneda X) F) : F X :=
  η X 1.

Local Notation out X F x :=
  ((λ (Y : C^op) (f : yoneda X Y), fmap F f x) :
   ∀ Y, Sets (yoneda X Y) (F Y)).

Lemma yoneda_out_subproof@{} (X : C) (F : functor C^op Sets) (x : F X)
  (Y Z : C^op) (f : C^op Y Z) :
  fmap F f ∘ out X F x Y = out X F x Z ∘ fmap (yoneda X) f.
Proof.
apply/funE => g /=.
by rewrite -[LHS]/((fmap F f ∘ fmap F g) x) -fmapD.
Qed.

Definition yoneda_out@{} (X : C) (F : functor C^op Sets@{u v}) (x : F X) : nat_trans (yoneda X) F :=
  NatTrans (Sub (out X F x) (yoneda_out_subproof x)).

Lemma yoneda_inK@{} X (F : functor C^op Sets) (η : nat_trans (yoneda X) F) : yoneda_out (yoneda_in η) = η.
Proof.
apply/eq_nat_trans=> Y; apply/funE=> f; case: η=> η.
rewrite /yoneda_out /yoneda_in /=.
by rewrite -[LHS]SetsE /= (valP η) SetsE /= -[f in RHS]comp1f.
Qed.

Lemma yoneda_outK@{} X (F : functor C^op Sets) (x : F X) : yoneda_in (yoneda_out x) = x.
Proof. by rewrite /yoneda_out /yoneda_in /= fmap1. Qed.

End Yoneda.

Section Representable.

Universes u v.
Constraint u < v.

Context (C : catType@{u}) (F : functor@{v} C^op Sets@{u v}).

Definition represent@{} (X : C) : Type@{u} :=
  {x : F X | has_inverse (yoneda_out@{u v} x)}.

Definition mediating@{} X (ρ : represent X) (Y : C) (y : F Y) : C Y X :=
  inverse (valP ρ) Y y.

Definition proj@{} X (ρ : represent X) (Y : C) (f : C Y X) : F Y :=
  yoneda_out@{u v} (val ρ) Y f.

Lemma projK@{} X (ρ : represent X) (Y : C) (f : C Y X) :
  mediating ρ (proj ρ f) = f.
Proof.
rewrite -[RHS]/(cat_id (yoneda X) Y f).
by rewrite -[1 in RHS](inverseK (valP ρ)).
Qed.

Lemma mediatingK X (ρ : represent X) (Y : C) (y : F Y) :
  proj ρ (mediating ρ y) = y.
Proof.
rewrite -[RHS]/(cat_id F Y y).
by rewrite -[1 in RHS](inverseKV (valP ρ)).
Qed.

Lemma proj1 X (ρ : represent X) : proj ρ 1 = val ρ.
Proof. by rewrite /proj /yoneda_out /= fmap1. Qed.

End Representable.

Section Limits.

Universes u v.
Constraint u < v.

Context (I C : catType@{u}) (X : functor I C).

(** We use functor_comp directly instead of comp to avoid introducing an extra
universe level *)

Definition cone@{} : functor C^op Sets@{u v} :=
  functor_comp (yoneda@{u v} X)
               (op_functor@{u} (const_functor_functor@{u} I C)).

Program Definition Cone@{} Y (p : ∀ i, C Y (X i))
  (pP : ∀ i j ij, fmap X ij ∘ p i = p j) : cone Y := NatTrans (Sub p _).

Next Obligation. by move=> Y p pP /= i j ij; rewrite pP compf1. Qed.

Lemma coneP@{} Y (c : cone Y) i j ij : fmap X ij ∘ c i = c j.
Proof. by rewrite /= (nat_transP c) compf1. Qed.

Definition is_limit@{} (L : C) : Type@{u} := represent cone L.

Definition lim_proj@{} L (l : is_limit L) (i : I) : C L (X i) :=
  proj l 1 i.

Lemma lim_proj_fmap@{} L (l : is_limit L) (i j : I) (ij : I i j) :
  fmap X ij ∘ lim_proj l i = lim_proj l j.
Proof. by rewrite /lim_proj proj1 (nat_transP (val l)) /= compf1. Qed.

Lemma lim_projP@{} L (l : is_limit L) Y (d : cone Y) i :
  lim_proj l i ∘ mediating l d = d i.
Proof.
by rewrite /lim_proj proj1 -[d in RHS](mediatingK l).
Qed.

Lemma eq_into_limit@{} (L K : C) (k : is_limit K) :
  ∀ f g : C L K,
  (∀ i, lim_proj k i ∘ f = lim_proj k i ∘ g) →
  f = g.
Proof.
move=> f g e; rewrite -(projK k f) -(projK k g); congr mediating.
apply/eq_nat_trans=> i; move/(_ i): e.
by rewrite /lim_proj /proj /= compf1.
Qed.

Lemma Limit_subproof@{} L (c : cone L) :
  (∀ (Y : C) (d : cone Y), ∃! f : C Y L, ∀ i, c i ∘ f = d i) →
  has_inverse (yoneda_out c).
Proof.
move=> LP; apply/nat_trans_has_inverse=> Y; apply/Sets_has_inverse=> d.
case/(_ Y d): LP=> f [fP f_unique].
exists f; split; first by apply/eq_nat_trans.
by move=> g gP; apply: f_unique=> i; rewrite -gP.
Qed.

Definition Limit@{} L c cP : is_limit L :=
  Sub c (@Limit_subproof L c cP).

End Limits.

Arguments eq_into_limit {I C X L K}.
Arguments Cone {I C X Y} p pP.
Arguments Limit {I C X L} c cP.

Section TransportCone.

Universes u v.
Constraint u < v.

Context (I C D : catType@{u}) (X : functor I C) (F : functor C D).

Program Definition cone_app@{} Y (c : cone@{u v} X Y) :
  cone@{u v} (functor_comp F X) (F Y) :=
  @Cone I D (functor_comp F X) (F Y) (λ i, fmap F (c i)) _.

Next Obligation.
by move=> Y c i j ij /=; rewrite -fmapD (coneP c).
Qed.

End TransportCone.

Section HasLimits.

Universes u v.
Constraint u < v.

Variables (I C : catType@{u}).

Definition has_limits@{} :=
  ∀ X : {functor I -> C}, {L : C & is_limit@{u v} X L}.

Hypothesis lim : has_limits.

Definition lim_functor_fobj@{} :=
  λ X : {functor I -> C}, sig1 (lim X).

Program Definition lim_functor_fmap@{} (X Y : {functor I -> C}) (η : nat_trans X Y) :=
  mediating@{u v} (sig2 (lim Y))
           (Cone@{u v} (λ i : I, η i ∘ lim_proj (sig2 (lim X)) i) _).

Next Obligation.
move=> /= X Y η i j ij.
by rewrite compA nat_transP -compA lim_proj_fmap.
Qed.

Program Definition lim_functor : {functor {functor I -> C} -> C} :=
  Functor lim_functor_fobj lim_functor_fmap _ _.

Next Obligation.
move=> /= X.
apply/(eq_into_limit (sig2 (lim X)))=> i.
by rewrite lim_projP /= compf1 comp1f.
Qed.

(* FIXME: The ssreflect patterns [RHS] seem to be introducing universes *)
Next Obligation.
rewrite /lim_functor_fmap.
move=> /= X Y Z η ε.
apply/(eq_into_limit (sig2 (lim Z)))=> i /=.
rewrite compA !lim_projP /=.
rewrite -!(compA (η i)); congr (_ ∘ _).
by rewrite lim_projP /=.
Qed.

End HasLimits.

Section Products.

Universes u v.
Constraint u < v.

Context (I : Type@{u}) (C : catType@{u}) (X : I → C).

Definition is_prod@{} (L : C) : Type@{u} :=
  represent (cone@{u v} (disc_lift X)) L.

Definition ProdCone Y (d : ∀ i, C Y (X i)) : cone@{u v} (disc_lift@{u} X) Y :=
  @Cone@{u v} _ _ (disc_lift@{u} X) _ (λ i' : disc I, d i'.(of_disc))
    (λ i j ij, match ij with erefl => comp1f (d i.(of_disc)) end).

Lemma Prod_subproof@{} L (c : ∀ i, C L (X i)) :
  (∀ (Y : C) (d : ∀ i, C Y (X i)), ∃! f : C Y L, ∀ i, c i ∘ f = d i) →
  has_inverse (yoneda_out (ProdCone c)).
Proof.
move=> cP; apply: Limit_subproof => Y d.
case: (cP Y (λ i, d (Disc i)))=> f [fP f_unique].
exists f; split => [[i]|g gP]; first exact: fP.
apply: f_unique=> i; exact: (gP (Disc i)).
Qed.

End Products.

Section LimitSets.

Universes u v.
Constraint u < v.

Context (I : catType@{u}) (X : functor@{v} I Sets@{u v}).

Set Primitive Projections.
Record lim_sets@{} : Type@{u} := LimSets {
  of_lim_sets :
    {L : ∀ i, X i | ∀ i j ij, fmap@{v} X ij (L i) = L j}
}.
Unset Primitive Projections.
Coercion of_lim_sets : lim_sets >-> sub.

Lemma eq_lim_sets@{} (x y : lim_sets) : (∀ i, val x i = val y i) → x = y.
Proof.
by move=> exy; congr LimSets; apply/val_inj/dfunE.
Qed.

Universe w.
Constraint v < w.

Program Definition lim_sets_cone@{} : cone@{v w} X lim_sets :=
  @Cone@{v w} _ _ X _ (λ (i : I) (x : lim_sets), val x i) _.

Next Obligation.
by move=> /= i j ij; apply/funE=> x; rewrite /= !SetsE (valP x).
Qed.

Lemma lim_sets_coneP@{} :
  (∀ (Y : Sets) (d : cone@{v w} X Y),
   exists! f : Sets Y lim_sets, ∀ i, lim_sets_cone i ∘ f = d i).
Proof.
move=> Y d.
have dP: ∀ y i j ij, fmap@{v} X ij (d i y) = d j y.
  by move=> y i j ij; rewrite -[LHS]SetsE coneP.
exists (λ y, LimSets (Sub (λ i, d i y) (dP y))); split=> [i|].
  by apply/funE=> /= y.
move=> f ηE; apply/funE=> y /=.
rewrite (_ : Sub _ _ = of_lim_sets (f y)); first by case: (f y).
by apply/val_inj/dfunE=> i /=; rewrite -ηE.
Qed.

Definition lim_setsP@{} : is_limit X lim_sets :=
  Limit lim_sets_cone lim_sets_coneP.

End LimitSets.

Section LimitCat.

Universes u v w.
Constraint u < v.
Constraint v < w.

Context (I : catType@{u}) (C : functor@{v} I Cat@{u v}).

Open Scope cast_scope.

Let lim_cat_obj : Type@{u} := lim_sets (obj_functor ∘ C : Cat@{v w} _ _).

Set Primitive Projections.
Record lim_cat_hom@{} (X Y : lim_cat_obj) : Type@{u} := LimCatHom {
  of_lim_cat_hom :
    {f : ∀ i : I, C i (X.(val) i) (Y.(val) i) |
     ∀ i j ij,
       fmap@{v} (fmap@{v} C ij) (f i) =
       iso_of_eq (Y.(valP) i j ij)^-1 ∘ f j ∘ iso_of_eq (X.(valP) i j ij)
    }
}.
Unset Primitive Projections.
Local Coercion of_lim_cat_hom : lim_cat_hom >-> sub.

Lemma eq_lim_cat_hom X Y (f g : lim_cat_hom X Y) :
  (∀ i, val f i = val g i) → f = g.
Proof.
by move=> efg; congr LimCatHom; apply/val_inj/dfunE.
Qed.

Program Definition lim_cat_id@{} (X : lim_cat_obj) : lim_cat_hom X X :=
  LimCatHom (Sub (λ i, 1) _).

Next Obligation.
by move=> /= X i j ij; rewrite fmap1 compf1 iso_of_eqKV.
Qed.

Lemma lim_cat_compWF@{} X Y Z (F : lim_cat_hom Y Z) (G : lim_cat_hom X Y) :
  {lift (λ i, F.(val) i ∘ G.(val) i) to lim_cat_hom X Z}.
Proof.
move=> i j ij.
rewrite fmapD F.(valP) G.(valP) !compA.
by rewrite -[_ ∘ iso_of_eq (valP Y i j ij) ∘ _]compA iso_of_eqK compf1.
Qed.

Definition lim_cat_comp@{} X Y Z (F : lim_cat_hom Y Z) (G : lim_cat_hom X Y) :=
  LimCatHom (Sub (λ i, F.(val) i ∘ G.(val) i) (@lim_cat_compWF X Y Z F G)).

Lemma lim_cat_compP@{} : Cat.axioms@{u} lim_cat_comp lim_cat_id.
Proof.
split.
- move=> X Y [f]; congr LimCatHom; apply/val_inj/dfunE=> i.
  by rewrite /= comp1f.
- move=> X Y [f]; congr LimCatHom; apply/val_inj/dfunE=> i.
  by rewrite /= compf1.
- move=> X Y Z W [h] [g] [f]; congr LimCatHom.
  by apply/val_inj/dfunE=> i; rewrite /= compA.
Qed.

Definition lim_cat_catMixin := CatMixin@{u} lim_cat_compP.
Canonical lim_cat := CatType lim_cat_obj lim_cat_hom lim_cat_catMixin.

Definition lim_cat_cone_proj@{} (i : I) : Cat@{v w} lim_cat (C i) :=
  Functor (λ X : lim_cat_obj, val X i) (λ X Y f, val f i)
          (λ X, erefl) (λ X Y Z f g, erefl).

Lemma lim_cat_coneC@{} i j ij :
  fmap C ij ∘ lim_cat_cone_proj i = lim_cat_cone_proj j.
Proof.
apply/eq_functor.
- move=> X /=; exact: (valP X).
- move=> e1 X Y f.
  rewrite -[fmap (_ ∘ _) f]/(fmap (fmap C ij) (val f i)) (valP f).
  rewrite -[fmap _ f]/(val f j).
  rewrite (PropI _ (valP X i j ij) (e1 X)).
  rewrite (PropI _ (valP Y i j ij) (e1 Y)).
  by rewrite !compA iso_of_eqK comp1f.
Qed.

Definition lim_cat_cone@{} : cone@{v w} C lim_cat :=
  @Cone@{v w} _ _ C lim_cat (@lim_cat_cone_proj) lim_cat_coneC.

Lemma lim_cat_coneP@{} (D : Cat) (d : cone@{v w} C D) :
  ∃! F : Cat D lim_cat, ∀ i, lim_cat_cone i ∘ F = d i.
Proof.
pose limP := lim_setsP (functor_comp obj_functor C).
pose F0 : D → lim_cat_obj := mediating limP (cone_app _ d).
have F0P X i : val (F0 X) i = d i X.
  by rewrite -[LHS]/((lim_proj limP i ∘ F0) X) lim_projP.
pose F1_def X Y (f : D X Y) i : C i (val (F0 X) i) (val (F0 Y) i) :=
  iso_of_eq (F0P Y i)^-1 ∘ fmap (d i) f ∘ iso_of_eq (F0P X i).
have F1_defP X Y f : {lift F1_def X Y f to lim_cat_hom (F0 X) (F0 Y)}.
  move=> i j ij; apply: eq_hom; rewrite /F1_def !fmapD !fmap_iso_of_eq.
  by rewrite !sig_iso -(coneP d ij).
pose F1 X Y f := LimCatHom (Sub (F1_def X Y f) (F1_defP X Y f)).
have F11 X : F1 X X 1 = 1.
  congr LimCatHom; apply/val_inj/dfunE=> i.
  by rewrite /= /F1_def fmap1 compf1 iso_of_eqKV.
have F1D X Y Z (f : D Y Z) (g : D X Y) : F1 _ _ (f ∘ g) = F1 _ _ f ∘ F1 _ _ g.
  congr LimCatHom; apply/val_inj/dfunE=> i /=.
  rewrite /= /F1_def !compA -[_ ∘ iso_of_eq _ ∘ iso_of_eq _]compA.
  by rewrite iso_of_eqK compf1 fmapD !compA.
exists (Functor F0 F1 F11 F1D); split.
  move=> i; apply/eq_functor=> [X|]; first exact: F0P.
  move=> F0P' X Y f /=; rewrite /F1_def.
  rewrite (PropI _ (F0P Y i) (F0P' Y)) !compA iso_of_eqK comp1f.
  congr comp; congr iso_of_eq; exact: PropI.
move=> G GP; apply/eq_functor=> [X|] /=.
  by apply/eq_lim_sets=> i; rewrite F0P -GP.
move=> eF0G X Y f; apply/eq_lim_cat_hom=> i /=.
have e Z : val (iso_of_eq (eF0G Z)) i = iso_of_eq ((λ H : lim_cat_obj, val H i) @@ eF0G Z).
  by case: _ / (eF0G Z).
by rewrite !e; apply/eq_hom; rewrite /F1_def !sig_iso -GP.
Qed.

Definition lim_catP@{} : is_limit C lim_cat :=
  Limit lim_cat_cone lim_cat_coneP.

End LimitCat.

Module CartCat.

Section ClassDef.

Universe u v.
Constraint u < v.

Record class_of (C : Type@{u}) (hom : C -> C -> Type@{u}) : Type@{u} := Class {
  base : Cat.mixin_of@{u} hom;
  term : {T : C & is_limit@{u v} (@disc_lift _ (Cat.Pack base) (of_void C)) T};
  prod : ∀ F : functor (disc_catType bool) (Cat.Pack base), {P : C & is_limit@{u v} F P};
}.

Record type := Pack {
  obj : Type@{u};
  hom : obj -> obj -> Type@{u};
  _   : class_of hom
}.
Local Coercion obj : type >-> Sortclass.
Local Coercion base : class_of >-> Cat.mixin_of.
Variables (C0 : Type@{u}) (C1 : C0 -> C0 -> Type@{u}) (cC : type).
Definition class := let: Pack _ _ c as cC' := cC return class_of (@hom cC') in c.
Definition clone c of phant_id class c := @Pack C0 C1 c.

Definition catType := @Cat.Pack _ _ class.

End ClassDef.

Module Exports.
Coercion obj : type >-> Sortclass.
Coercion hom : type >-> Funclass.
Coercion base : class_of >-> Cat.mixin_of.
Coercion catType : type >-> Cat.type.
Canonical catType.
Notation cartCatType := type.
End Exports.

End CartCat.

Export CartCat.Exports.

Section Adjunctions.

Universe u.

Context (C D : catType@{u}).

Record adjoint (F : functor C D) (G : functor D C) : Type@{u} := Adjoint {
  adjLR  : ∀ X Y, D (F X) Y → C X (G Y);
  adjRL  : ∀ X Y, C X (G Y) → D (F X) Y;
  adjLRK : ∀ X Y (f : D (F X) Y), adjRL (adjLR f) = f;
  adjRLK : ∀ X Y (f : C X (G Y)), adjLR (adjRL f) = f;
  adjLRN : ∀ (X1 X2 : C) (Y1 Y2 : D),
           ∀ (f : D Y1 Y2) (g : D (F X2) Y1) (h : C X1 X2),
             adjLR (f ∘ g ∘ fmap F h) = fmap G f ∘ adjLR g ∘ h;
  adjRLN : ∀ (X1 X2 : C) (Y1 Y2 : D),
           ∀ (f : D Y1 Y2) (g : C X2 (G Y1)) (h : C X1 X2),
             adjRL (fmap G f ∘ g ∘ h) = f ∘ adjRL g ∘ fmap F h;
}.

Lemma eq_adjointLR F G (a1 a2 : adjoint F G) :
  (∀ X Y (f : D (F X) Y), adjLR a1 f = adjLR a2 f) →
  a1 = a2.
Proof.
case: a1 a2=> [LR1 RL1 p11 p12 p13 p14] [LR2 RL2 p21 p22 p23 p24] /= eLR.
have {}eLR: LR1 = LR2.
  by apply/dfunE=> X; apply/dfunE=> Y; apply/funE=> f.
case: LR2 / eLR p21 p22 p23 p24=> p21 p22 p23 p24.
suff eRL: RL1 = RL2.
  case: RL2 / eRL p21 p22 p23 p24=> p21 p22 p23 p24.
  congr Adjoint; exact: PropI.
apply/dfunE=> X; apply/dfunE=> Y; apply/funE=> f.
by rewrite -{2}[f]p12 p21.
Qed.

End Adjunctions.

Section NatCat.

(* This could be generalized to any preorder, but we do an adhoc definition
   for nat to avoid messing with PoType for now. *)

Lemma nat_compP :
  @Cat.axioms@{Set} nat leq (fun n m p mp nm => leq_trans nm mp) leqnn.
Proof.
split.
- move=> n m nm; exact: eq_irrelevance.
- move=> n m nm; exact: eq_irrelevance.
- move=> n m p q pq mp nm; exact: eq_irrelevance.
Qed.

Definition nat_catMixin := CatMixin nat_compP.
Canonical nat_catType := Eval hnf in CatType@{Set} nat leq nat_catMixin.

(* Build a functor from nat by giving each morphism.  We make the
   functor contravariant so that it is more convenient for us when
   building the inverse limit of CPOs.  *)

Universes i j.
Constraint i <= j.

Section DownDef.

Variable C : catType@{i}.
Variable X : nat -> C.
Variable f : forall n, C (X n.+1) (X n).

Fixpoint down_def n m : C (X (m + n)) (X n) :=
  match m with
  | 0    => 1
  | m.+1 => down_def n m ∘ f (m + n)
  end.

Lemma down_defSn n m :
  f n ∘ down_def n.+1 m = down_def n m.+1 ∘ iso_of_eq (congr1 X (addnS _ _)).
Proof.
elim: m=> [|m IH] /=; first by rewrite eq_axiomK /= comp1f.
rewrite compA IH /= -[LHS]compA -[RHS]compA; congr comp.
move: (addnS m n) (addnS m.+1 n); rewrite -![_.+1 + _]/((_ + _).+1).
(* FIXME: Why is this rewrite needed? *)
rewrite -![m.+2 + _]/((_ + _).+2).
move: (m + n.+1) (m + n).+1=> a b q.
by case: b / q=> q /=; rewrite !eq_axiomK /= comp1f compf1.
Qed.

Fact down_key : unit. Proof. exact: tt. Qed.

Definition down n m (nm : n <= m) : C (X m) (X n) :=
  locked_with
    down_key
    (down_def _ _ ∘ (iso_of_eq (congr1 X (esym (subnK nm))))).

Lemma downS n m (nm : n <= m) (nm1 : n <= m.+1) : down nm1 = down nm ∘ f m.
Proof.
unfold down; rewrite !unlock.
move: (subnK nm) (subnK nm1); rewrite (subSn nm) /=.
move: {nm nm1} (m - n)=> o; rewrite -[o.+1 + n]/(o + n).+1 => e.
by case: m / e => ?; rewrite eq_axiomK /= !compf1.
Qed.

Lemma down0 n (nn : n <= n) : down nn = 1.
Proof.
unfold down; rewrite unlock; move: (subnK nn); rewrite subnn=> e.
by rewrite eq_axiomK /= comp1f.
Qed.

Lemma down1 n (nSn : n <= n.+1) : down nSn = f n.
Proof. by rewrite (downS (leqnn n) nSn) down0 comp1f. Qed.

Lemma downD n m o (nm : n <= m) (mo : m <= o) :
  down (leq_trans nm mo) = down nm ∘ down mo.
Proof.
move: (mo) (leq_trans _ _); rewrite -(subnK mo) {mo}.
elim: (o - m)=> {o} [|o IH] /=.
  move=> mo no; unfold down; rewrite !unlock; move: (subnK mo).
  rewrite -![0 + m]/(m) subnn => {mo} mo; rewrite eq_axiomK /= compf1.
  by rewrite (eq_irrelevance no nm) compf1.
rewrite -![o.+1 + _]/(o + _).+1 => mo no.
rewrite (downS (leq_trans nm (leq_addl o m)) no).
rewrite (IH (leq_addl o m) (leq_trans nm (leq_addl o m))).
by rewrite (downS (leq_addl o m) mo) compA.
Qed.

Program Definition down_functor : {functor op nat -> C} :=
  Functor X (fun m n nm => down nm) _ _.

Next Obligation. move=> n /=; exact: down0. Qed.
Next Obligation. by move=> n m p /= g h; rewrite -downD. Qed.

Lemma down_coneP Y (g : forall n, C Y (X n)) :
  (forall n, f n ∘ g n.+1 = g n) ->
  forall n m (nm : n <= m), down nm ∘ g m = g n.
Proof.
move=> /= gP n m nm; unfold down; rewrite !unlock.
move: (m - n) (subnK nm)=> p e; case: m / e {nm}; rewrite compf1.
elim: p=> [|p IH] /=; first by rewrite comp1f.
by rewrite -IH -[g (p + n)]gP compA.
Qed.

Definition nat_cone Y (g : forall n, C Y (X n)) :
  (forall n, f n ∘ g n.+1 = g n) -> cone down_functor Y :=
  fun gP => @Cone _ _ down_functor Y g (fun m n nm => down_coneP gP nm).

End DownDef.

Lemma down_comp
  (C D : catType@{i}) (X : nat -> C) (f : forall n, C (X n.+1) (X n))
  (G : {functor C -> D}) n m (nm : n <= m) :
  fmap G (down f nm) = down (fun n => fmap G (f n)) nm.
Proof.
move: (nm); rewrite -(subnK nm); elim: (m - n)=> {m nm} [|m IH].
  by move=> ?; rewrite !down0 fmap1.
change (m.+1 + n) with (m + n).+1 => nm.
by rewrite !(downS _ (leq_addl m n)) fmapD IH.
Qed.

Lemma down_comp_cone
  (C D : catType@{i}) (X : nat -> C) (f : forall n, C (X n.+1) (X n))
  Y (g : forall n, C Y (X n)) (gP : forall n, g n = f n ∘ g n.+1)
  (F : {functor C -> D}) :
  forall n, fmap F (g n) = fmap F (f n) ∘ fmap F (g n.+1).
Proof. by move=> n; rewrite -fmapD gP. Qed.

Arguments down_comp_cone {_ _ _} _ {_} _ _ _ _.

End NatCat.

From mathcomp Require Import ssreflect ssrfun.
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

Variant nat_trans@{} F G : Type@{u} := NatTrans of
  {η : ∀ X, D (F X) (G X) |
   ∀ X Y (f : C X Y), fmap G f ∘ η X = η Y ∘ fmap F f}.

Definition fun_of_nat_trans (F G : functor) (η : nat_trans F G) :=
  let: NatTrans η := η in val η.

Coercion fun_of_nat_trans : nat_trans >-> Funclass.

Lemma eq_nat_trans F G (η ε : nat_trans F G) : (forall X, η X = ε X) ↔ η = ε.
Proof.
split; last by move=> ->.
case: η ε=> [η] [ε] /= eηε; congr NatTrans.
by apply: val_inj; apply: dfunE.
Qed.

Program Definition nat_trans_comp@{} F G H
  (η : nat_trans G H) (ε : nat_trans F G) : nat_trans F H :=
  NatTrans (Sig _ (fun X => η X ∘ ε X) _).

Next Obligation.
move=> F G H [η] [ε] X Y f.
by rewrite compA (valP η) -compA (valP ε) compA.
Qed.

Program Definition nat_trans_id@{} F : nat_trans F F :=
  NatTrans (Sig _ (fun X => 1) _).

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

End Functor.

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
  NatTrans (Sig _ (λ X : C, f) (λ (A B : C) (g : C A B), comp1f f * (compf1 f)^-1)).

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
Canonical cat_catType@{v} :=
  Eval hnf in CatType catType functor cat_catMixin@{v}.

End CatCat.

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

Definition yoneda_out_def@{} (X : C) (F : functor C^op Sets) (x : F X) :
  ∀ Y, Sets (yoneda X Y) (F Y) :=
  λ (Y : C^op) (f : yoneda X Y), fmap F f x.
Arguments yoneda_out_def {X F} x Y f.

Lemma yoneda_out_defP@{} (X : C) (F : functor C^op Sets) (x : F X)
  (Y Z : C^op) (f : C^op Y Z) :
  fmap F f ∘ yoneda_out_def x Y = yoneda_out_def x Z ∘ fmap (yoneda X) f.
Proof.
apply/funE => g /=.
by rewrite -[LHS]/((fmap F f ∘ fmap F g) x) -fmapD.
Qed.

Definition yoneda_out@{} (X : C) (F : functor C^op Sets@{u v}) (x : F X) : nat_trans (yoneda X) F :=
  NatTrans (Sig _ (yoneda_out_def x) (yoneda_out_defP x)).

Lemma yoneda_inK@{} X (F : functor C^op Sets) (η : nat_trans (yoneda X) F) : yoneda_out (yoneda_in η) = η.
Proof.
apply/eq_nat_trans=> Y; apply/funE=> f; case: η=> η.
rewrite /yoneda_out /yoneda_out_def /yoneda_in /=.
by rewrite -[LHS]SetsE /= (valP η) SetsE /= -[f in RHS]comp1f.
Qed.

Lemma yoneda_outK@{} X (F : functor C^op Sets) (x : F X) : yoneda_in (yoneda_out x) = x.
Proof.
by rewrite /yoneda_out /yoneda_out_def /yoneda_in /= fmap1.
Qed.

End Yoneda.

Section Representable.

Universes u v.
Constraint u < v.

Context (C : catType@{u}) (X : C) (F : functor C^op Sets).

Definition represent@{} : Type@{u} :=
  {x : F X | has_inverse (yoneda_out@{u v} x)}.

Definition mediating@{} (ρ : represent) (Y : C) (y : F Y) : C Y X :=
  inverse (valP ρ) Y y.

End Representable.

Section Limits.

Universes u v.
Constraint u < v.

Context (I C : catType@{u}) (X : functor I C).

(** We use functor_comp directly instead of comp to avoid introducing an extra
universe level *)

Definition cone@{} : functor C^op Sets@{u v} :=
  functor_comp (yoneda@{u v} X) (op_functor@{u} (const_functor_functor@{u} I C)).

Definition is_limit@{} (L : C) : Type@{u} := represent L cone.

Definition proj@{} L (l : is_limit L) (i : I) : C L (X i) :=
  val l i.

Lemma proj_fmap L (l : is_limit L) (i j : I) (f : I i j) :
  fmap X f ∘ proj l i = proj l j.
Proof.
by rewrite /proj; case: (val l)=> η /=; rewrite (valP η) /= compf1.
Qed.

End Limits.

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
  NatTrans (Sub _ (fun X => η X ∘ ε X) _).

Next Obligation.
move=> F G H [η] [ε] X Y f.
by rewrite compA (valP η) -compA (valP ε) compA.
Qed.

Program Definition nat_trans_id@{} F : nat_trans F F :=
  NatTrans (Sub _ (fun X => 1) _).

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
by exists (NatTrans (Sub _ ε εP)); split; apply/eq_nat_trans=> X;
rewrite nat_trans_compE /= ?inverseK ?inverseKV.
Qed.

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
  NatTrans (Sub _ (λ X : C, f) (λ (A B : C) (g : C A B), comp1f f * (compf1 f)^-1)).

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
  NatTrans (Sub _ (out X F x) (yoneda_out_subproof x)).

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

Context (C : catType@{u}) (F : functor C^op Sets).

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
  (pP : ∀ i j ij, fmap X ij ∘ p i = p j) : cone Y := NatTrans (Sub _ p _).

Next Obligation. by move=> Y p pP /= i j ij; rewrite pP compf1. Qed.

Lemma coneP@{} Y (c : cone Y) i j ij : fmap X ij ∘ c i = c j.
Proof. by rewrite /= (nat_transP c) compf1. Qed.

Definition is_limit@{} (L : C) : Type@{u} := represent cone L.

Definition lim_proj@{} L (l : is_limit L) (i : I) : C L (X i) :=
  proj l 1 i.

Lemma lim_proj_fmap@{} L (l : is_limit L) (i j : I) (ij : I i j) :
  fmap X ij ∘ lim_proj l i = lim_proj l j.
Proof. by rewrite /lim_proj proj1 (nat_transP (val l)) /= compf1. Qed.

Lemma is_limitP@{} L (c : cone L) :
  (∀ (Y : C) (d : cone Y), exists! f : C Y L, ∀ i, c i ∘ f = d i) →
  is_limit L.
Proof.
move=> LP; exists c.
apply/nat_trans_has_inverse=> Y; apply/Sets_has_inverse=> d.
case/(_ Y d): LP=> f [fP f_unique].
exists f; split; first by apply/eq_nat_trans.
by move=> g gP; apply: f_unique=> i; rewrite -gP.
Qed.

End Limits.

Arguments is_limitP {I C X L} c cP.

Section LimitSets.

Universes u v.
Constraint u < v.

Context (I : catType@{u}) (X : functor@{v} I Sets@{u v}).

Record lim_sets@{} : Type@{u} := LimSets {
  of_lim_sets :
    {L : ∀ i, X i | ∀ i j ij, fmap@{v} X ij (L i) = L j}
}.
Coercion of_lim_sets : lim_sets >-> sub.

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
exists (λ y, LimSets (Sub _ (λ i, d i y) (dP y))); split=> [i|].
  by apply/funE=> /= y.
move=> f ηE; apply/funE=> y /=.
rewrite (_ : Sub _ _ _ = of_lim_sets (f y)); first by case: (f y).
by apply/val_inj/dfunE=> i /=; rewrite -ηE.
Qed.

Definition lim_setsP@{} : is_limit X lim_sets :=
  is_limitP lim_sets_cone lim_sets_coneP.

End LimitSets.

Section LimitCat.

Universes u v w.
Constraint u < v.
Constraint v < w.

Context (I : catType@{u}) (C : functor@{v} I Cat@{u v}).

Open Scope cast_scope.

Let lim_cat_obj : Type@{u} := lim_sets (obj_functor ∘ C : Cat@{v w} _ _).

Record lim_cat_hom@{} (X Y : lim_cat_obj) : Type@{u} := LimCatHom {
  of_lim_cat_hom :
    {f : ∀ i : I, C i (X.(val) i) (Y.(val) i) |
     ∀ i j ij,
       fmap@{v} (fmap@{v} C ij) (f i) =
       iso_of_eq (Y.(valP) i j ij)^-1 ∘ f j ∘ iso_of_eq (X.(valP) i j ij)
    }
}.
Local Coercion of_lim_cat_hom : lim_cat_hom >-> sub.

Program Definition lim_cat_hom_id@{} (X : lim_cat_obj) : lim_cat_hom X X :=
  LimCatHom (Sub _ (λ i, 1) _).

Next Obligation.
by move=> /= X i j ij; rewrite fmap1 compf1 iso_of_eqKV.
Qed.

Program Definition lim_cat_hom_comp@{}
  (X Y Z : lim_cat_obj)
  (F : lim_cat_hom Y Z) (G : lim_cat_hom X Y) : lim_cat_hom X Z :=
  LimCatHom (Sub _
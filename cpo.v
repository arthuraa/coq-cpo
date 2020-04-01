From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From cpo Require Import base cat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Strings.String.

Open Scope string_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* TODO:

- Fix canonical structure inference for mono, cont and friends.

- Better naming conventions for mono, cont, etc instances.

- Use mixins to define subtyping

- Use smart constructors for other subtypes.

- Remove mapp

- Make composition simplify when applied.

- Name categories after objects instead of hom sets

- Get rid of invlim_proj

*)

Obligation Tactic := idtac.
Definition phant_id_err {T1 T2 : Type} t1 t2 (s : string) : Prop :=
  phantom T1 t1 -> phantom T2 t2.
Definition unify {T : Type} {t : T} (x : phantom T t) := x.
Notation "[ 'find' v | t1 ~ t2 ] rest" :=
  (fun v (_ : phant_id t1 t2) => rest)
  (at level 0, v ident, rest at level 10, right associativity) : form_scope.
Notation "[ 'find' v : T | t1 ~ t2 ] rest" :=
  (fun (v : T) (_ : phant_id t1 t2) => rest)
  (at level 0, v ident, rest at level 10, right associativity) : form_scope.
Notation "[ 'find' v | t1 ~ t2 | msg ] rest" :=
  (fun v (_ : phant_id_err t1 t2 msg) => rest)
  (at level 0, v ident, rest at level 10, right associativity) : form_scope.
Notation "[ 'find' v : T | t1 ~ t2 | msg ] rest" :=
  (fun (v : T) (_ : phant_id_err t1 t2 msg) => rest)
  (at level 0, v ident, rest at level 10, right associativity) : form_scope.
Notation "’Error: t msg" := (phant_id_err _ t msg)
  (at level 0) : form_scope.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

Definition dfun T (S : T -> Type) := forall x, S x.
Definition sfun@{i} (T S : Type@{i}) : Type@{i} := T -> S.

Definition flip@{i} (T S : Type@{i}) (R : T -> S -> Type@{i})
  (f : forall x y, R x y) y x := f x y.

Identity Coercion fun_of_dfun : dfun >-> Funclass.
Identity Coercion fun_of_sfun : sfun >-> Funclass.

(* This declaration helps inferring a pair p when we know what p.1 and p.2
   should be. This typically arises when p : Type * Type. *)
Definition prod_pair@{i} (T S : Type@{i}) (x : T) (y : S) := (x, y).
Canonical prod_pair.

Definition pairf@{i} (T S R : Type@{i}) (f : R -> T) (g : R -> S) x :=
  (f x, g x).

Section DFunOfProd.

Variables (K : Type) (K_sort : K -> Type).
Variables T S : K.

Local Coercion K_sort : K >-> Sortclass.

Definition dfun_of_prod (p : T * S) : dfun (fun b => if b then T else S) :=
  fun b => match b with
           | true => p.1
           | false => p.2
           end.

Definition prod_of_dfun (p : dfun (fun b => if b then T else S)) : T * S :=
  (p true, p false).

Lemma dfun_of_prodK : cancel dfun_of_prod prod_of_dfun.
Proof. by case. Qed.

End DFunOfProd.

Unset Universe Polymorphism.
Universe u0.
Universe u1.
Universe u2.
Constraint u0 < u1.
Constraint u1 < u2.
Notation Type0 := Type@{u0} (only parsing).
Notation Type1 := Type@{u1} (only parsing).
Notation Type2 := Type@{u2} (only parsing).

Module Po.

Definition axioms (T : Type0) (appr : relation T) :=
  [/\ reflexive T appr, transitive T appr & antisymmetric T appr].

Record mixin_of (T : Type0) := Mixin {
  appr : relation T;
  _    : axioms appr
}.

Notation class_of := mixin_of.

Section ClassDef.

Record type : Type1 := Pack {sort : Type0; base : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type0) (cT : type).

Definition class := let: Pack _ c := cT return class_of cT in c.

Definition clone := fun c & cT -> T & phant_id (@Pack T c) cT => Pack c.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Notation poType := type.
Notation PoMixin := Mixin.
Notation PoType T m := (@Pack T m).
Notation "[ 'poType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'poType'  'of'  T ]") : form_scope.

End Exports.

End Po.

Export Po.Exports.

Reserved Notation "x ⊑ y" (at level 50, no associativity).
Reserved Notation "x ⋢ y" (at level 50, no associativity).
Reserved Notation "x ⊑ y ⊑ z" (at level 50, y at next level, no associativity).

Delimit Scope cpo_scope with cpo.
Open Scope cpo_scope.

Section PoTheory.

Variables T : poType.

Definition appr : relation T :=
  Po.appr (Po.base T).

Lemma appr_refl : Reflexive appr.
Proof. by rewrite /appr; case: (T)=> ? [? []]. Qed.

Lemma appr_trans : Transitive appr.
Proof. by rewrite /appr; case: (T)=> ? [? []]. Qed.

Lemma appr_anti : antisymmetric T appr.
Proof. by rewrite /appr; case: (T)=> ? [? []]. Qed.

End PoTheory.

Existing Instance appr_refl.
Existing Instance appr_trans.

Notation "x ⊑ y" := (appr x y) : cpo_scope.
Notation "x ⋢ y" := (~ appr x y) : cpo_scope.
Notation "x ⊑ y ⊑ z" := (x ⊑ y /\ y ⊑ z) : cpo_scope.

Definition monotone (T S : poType) (f : T -> S) :=
  forall x y, x ⊑ y -> f x ⊑ f y.

Lemma monotone_comp (T S R : poType) (f : S -> R) (g : T -> S) :
  monotone f -> monotone g -> monotone (f \o g).
Proof. by move=> mono_f mono_g x y /mono_g/mono_f. Qed.

Variant mono (T S : poType) :=
  Mono of {f : T -> S | ∀ x y, x ⊑ y → f x ⊑ f y}.
Definition mono_of (T S : poType) of phant (T -> S) := mono T S.
Notation "{ 'mono' T }" := (mono_of (Phant T))
  (at level 0, format "{ 'mono'  T }") : type_scope.
Identity Coercion mono_of_mono_of : mono_of >-> mono.

Definition fun_of_mono (T S : poType) (f : mono T S) :=
  let: Mono f := f in val f.
Coercion fun_of_mono : mono >-> Funclass.

Lemma monoP (T S : poType) (f : {mono T -> S}) : monotone f.
Proof. case: f=> [] [? fP]; exact: fP. Defined.

Lemma eq_mono (T S : poType) (f g : {mono T -> S}) : f =1 g <-> f = g.
Proof.
split; last by move=> ->.
by case: f g=> [f] [g] /= /funE/val_inj ->.
Qed.

Definition mono_comp (T S R : poType) (f : {mono S -> R}) (g : {mono T -> S}) : {mono T -> R} :=
  Eval hnf in Mono (Sub (f \o g) (monotone_comp (monoP f) (monoP g))).

Lemma mono_compA (A B C D : poType) (f : {mono C -> D}) (g : {mono B -> C}) (h : {mono A -> B}) :
  mono_comp f (mono_comp g h) = mono_comp (mono_comp f g) h.
Proof. exact/eq_mono. Qed.

Lemma monotone_id (T : poType) : monotone (@id T).
Proof. by []. Qed.

Definition mono_id (T : poType) : {mono T -> T} :=
  Eval hnf in Mono (Sub idfun (@monotone_id T)).

Arguments mono_id {_}.

Lemma mono_comp1f (T S : poType) (f : {mono T -> S}) : mono_comp mono_id f = f.
Proof. exact/eq_mono. Qed.

Lemma mono_compf1 (T S : poType) (f : {mono T -> S}) : mono_comp f mono_id = f.
Proof. exact/eq_mono. Qed.

Definition mono_catMixin := CatMixin (@Cat.Axioms _ _ _ _ mono_comp1f mono_compf1 mono_compA).
Canonical mono_catType :=
  Eval hnf in CatType poType mono mono_catMixin.

Definition isotone (T S : poType) (f : T -> S) :=
  forall x y, f x ⊑ f y = x ⊑ y.

Lemma iso_mono (T S : poType) (f : T -> S) :
  isotone f -> monotone f.
Proof. by move=> iso_f x y; rewrite iso_f. Qed.

Program Definition forget_mono : {functor poType -> Sets@{u0 u1}} :=
  Functor@{u1} (λ X, X) (λ X Y f, f) (λ X, erefl) (λ X Y Z f g, erefl).

Section LimPoType.

Variable (I : catType@{u0}) (X : functor_of@{u1} (Phant (I -> poType))).

Definition appr_lim_poset :
  relation (lim_sets@{u0 u1} (functor_comp@{u1} forget_mono X)) :=
  λ x y, ∀ i, val x i ⊑ val y i.

Lemma appr_lim_posetP : Po.axioms appr_lim_poset.
Proof.
split.
- move=> x i; exact: appr_refl.
- move=> x y z xy yz i; exact: appr_trans (yz i).
- move=> x y xy yz.
  by apply/eq_lim_sets=> i; apply/appr_anti; auto.
Qed.

Definition lim_poset_poMixin := PoMixin appr_lim_posetP.
Canonical lim_poset_poType :=
  Eval hnf in PoType _ lim_poset_poMixin.

Program Definition lim_poset_cone@{} : cone@{u1 u2} X lim_poset_poType :=
  Cone@{u1 u2} (λ i, Mono (Sub (λ x : lim_poset_poType, val x i) _)) _.

Next Obligation.
move=> /= i x y; exact.
Qed.

Next Obligation.
move=> /= i j ij.
apply/eq_mono=> x /=.
by rewrite -(valP x _ _ ij).
Qed.

Lemma lim_poset_coneP@{} :
  (∀ (Y : poType) (d : cone@{u1 u2} X Y),
   exists! f : mono Y lim_poset_poType, ∀ i, lim_poset_cone i ∘ f = d i).
Proof.
move=> Y d.
pose Ud := cone_app@{u1 u2} forget_mono d.
pose f : Y → lim_sets (functor_comp forget_mono X) :=
  mediating (lim_setsP (functor_comp forget_mono X)) Ud.
have fP : monotone f.
  move=> y1 y2 y12 i; rewrite 2!lim_setsE /=.
  exact: (monoP (d i)).
exists (Mono (Sub f fP)).
split=> [i|].
  by apply/eq_mono=> /= y /=; rewrite lim_setsE.
move=> g gP; apply/eq_mono=> y /=.
apply/eq_lim_sets=> i.
by rewrite lim_setsE /= -gP.
Qed.

Definition lim_posetP : is_limit X lim_poset_poType :=
  Limit _ lim_poset_coneP.

End LimPoType.

Section InjPo.

Variables (T : Type0) (S : poType).
Variables (f : T -> S).
Hypothesis f_inj : injective f.

Definition inj_appr (x y : T) := f x ⊑ f y.

Lemma inj_apprP : Po.axioms inj_appr.
Proof.
rewrite /inj_appr; split.
- move=> x; reflexivity.
- move=> x y z; exact: transitivity.
- move=> x y xy yx; apply: f_inj.
  exact: appr_anti xy yx.
Qed.

Definition InjPoMixin := PoMixin inj_apprP.

End InjPo.

Definition CanPoMixin (T : Type0) (S : poType) (f : T -> S) g (fK : cancel f g) :=
  InjPoMixin (can_inj fK).

Module Ppo.

Section ClassDef.

Record mixin_of (T : poType) := Mixin {
  bot : T;
  _   : forall x, bot ⊑ x;
}.

Record class_of T := Class {
  base  : Po.class_of T;
  mixin : mixin_of (Po.Pack base)
}.

Record type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Local Coercion base : class_of >-> Po.class_of.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  [find p  | Po.sort p ~ T | "not a poType" ]
  [find pm | Po.class p ~ pm ]
  fun m => @Pack T (@Class T pm m).

Definition poType := @Po.Pack cT xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Po.class_of.
Coercion sort : type >-> Sortclass.
Coercion poType : type >-> Po.type.
Canonical poType.
Notation ppoType := type.
Notation PpoMixin := Mixin.
Notation PpoType T m := (@pack T _ unify _ unify m).
Notation "[ 'ppoType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'ppoType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ppoType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ppoType'  'of'  T ]") : form_scope.
End Exports.

End Ppo.

Export Ppo.Exports.

Section PpoTheory.

Variable T : ppoType.

Definition bot : T :=
  Ppo.bot (Ppo.mixin (Ppo.class T)).
Lemma botP x : bot ⊑ x.
Proof. by rewrite /bot; case: (Ppo.mixin (Ppo.class T)) x. Qed.

End PpoTheory.

Arguments bot {_}.
Notation "⊥" := bot : cpo_scope.

End DFunPo.

Canonical sfun_poType (T : Type) (S : poType) :=
  Eval hnf in PoType (sfun T S) (dfun_poMixin _).

Definition mono_poMixin (T S : poType) :=
  [poMixin of {mono T -> S} by <:].
Canonical mono_poType (T S : poType) :=
  Eval hnf in PoType (mono T S) (mono_poMixin T S).
Canonical mono_subPoType (T S : poType) :=
  Eval hnf in [subPoType of mono T S].
Canonical mono_of_poType (T S : poType) :=
  Eval hnf in PoType {mono T -> S} (mono_poMixin T S).
Canonical mono_of_subPoType (T S : poType) :=
  Eval hnf in [subPoType of {mono T -> S}].

Section DFunPpo.

Variables (I : Type) (T_ : I -> ppoType).

Definition fun_bot : dfun T_ := fun x => ⊥.

Lemma fun_botP f : fun_bot ⊑ f.
Proof. by move=> /= x; exact: botP. Qed.

Definition dfun_ppoMixin := PpoMixin fun_botP.
Canonical dfun_ppoType := Eval hnf in PpoType (dfun T_) dfun_ppoMixin.

End DFunPpo.

Arguments fun_bot {_ _}.

Canonical sfun_ppoType (T : Type) (S : ppoType) :=
  Eval hnf in PpoType (sfun T S) (dfun_ppoMixin _).

Section MonoPpo.

Variables (T : poType) (S : ppoType).

Lemma monotone_fun_bot : monotone (@fun_bot T (fun _ => S)).
Proof. move=> ???; reflexivity. Qed.

Definition mono_bot : {mono T -> S} :=
  Eval hnf in Sub fun_bot monotone_fun_bot.
Canonical mono_bot.

Lemma mono_botP f : mono_bot ⊑ f.
Proof. rewrite appr_val /=; exact: botP. Qed.

Definition mono_ppoMixin := PpoMixin mono_botP.
Canonical mono_ppoType := Eval hnf in PpoType (mono T S) mono_ppoMixin.
Canonical mono_of_ppoType := Eval hnf in PpoType {mono T -> S} mono_ppoMixin.

End MonoPpo.

Lemma monotone_mono_comp (T S R : poType) (f1 f2 : {mono S -> R}) (g1 g2 : {mono T -> S}) :
  f1 ⊑ f2 -> g1 ⊑ g2 -> f1 ∘ g1 ⊑ f2 ∘ g2.
Proof.
move=> f12 g12 x /=; move/(_ x)/(valP f2): g12=> /=; apply: transitivity.
exact: f12.
Qed.

Section ProdPo.

Variables T S : poType.

Definition prod_appr (x y : T * S) :=
  x.1 ⊑ y.1 /\ x.2 ⊑ y.2.

Lemma prod_apprP : Po.axioms prod_appr.
Proof.
rewrite /prod_appr; split.
- case=> x y /=; split; reflexivity.
- by case=> [x1 y1] [x2 y2] [x3 y3] /= [xy1 xy2] [yz1 yz2]; split;
  [apply: transitivity xy1 yz1|apply: transitivity xy2 yz2].
- case=> [x1 y1] [x2 y2] /= [xy1 xy2] [yx1 yx2].
  by rewrite (appr_anti xy1 yx1) (appr_anti xy2 yx2).
Qed.

Definition prod_poMixin := PoMixin prod_apprP.
Canonical prod_poType := Eval hnf in PoType (T * S) prod_poMixin.

Lemma monotone_fst : monotone (@fst T S).
Proof. by case=> [??] [??] []. Qed.

Definition mono_fst : {mono T * S -> T} :=
  Eval hnf in Sub fst monotone_fst.
Canonical mono_fst.

Lemma monotone_snd : monotone (@snd T S).
Proof. by case=> [??] [??] []. Qed.

Definition mono_snd : {mono T * S -> S} :=
  Eval hnf in Sub snd monotone_snd.
Canonical mono_snd.

Lemma monotone_pairf (R : poType) (f : {mono R -> T}) (g : {mono R -> S}) :
  monotone (pairf f g).
Proof. move=> x y xy; split=> /=; exact: monoP. Qed.

Definition mono_pairf (R : poType) f g : {mono R -> T * S} :=
  Sub (pairf _ _) (monotone_pairf f g).
Canonical mono_pairf.

End ProdPo.

Lemma mono_prodP : ProdCat.axioms_of mono_pairf mono_fst mono_snd.
Proof.
split.
- by move=> /= T S R f g; apply/eq_mono=> x.
- by move=> /= T S R f g; apply/eq_mono=> x.
move=> /= T S R f g [/eq_mono H1 /eq_mono H2]; apply/eq_mono=> x.
by move: (H1 x) (H2 x)=> /=; case: (f x) (g x)=> [??] [??] /= -> ->.
Qed.

Definition mono_prodCatMixin := ProdCatMixin mono_prodP.
Canonical mono_prodCatType :=
  Eval hnf in ProdCatType poType mono mono_prodCatMixin.

Arguments mono_fst {_ _}.
Arguments mono_snd {_ _}.
Arguments mono_pairf {_ _ _}.

Canonical mono_cartCatType :=
  Eval hnf in CartCatType poType mono.

Program Definition mono_curry (T S R : poType) (f : {mono T * S -> R}) :
    {mono T -> {mono S -> R}} :=
  Mono (fun x => Mono (fun y => f (x, y)) _) _.

Next Obligation.
by move=> T S R f x y1 y2 y12; apply: monoP; split=> //; reflexivity.
Qed.

Next Obligation.
by move=> T S R f x1 x2 x12 y /=; apply: monoP; split=> //; reflexivity.
Qed.

Program Definition mono_eval (T S : poType) :
    {mono {mono T -> S} * T -> S} :=
  Mono (fun p => p.1 p.2) _.

Next Obligation.
move=> T S [/= f x] [/= g y] [/= fg xy].
apply: transitivity (monoP g xy); exact: fg.
Qed.

Lemma mono_ccCatAxioms : CCCat.axioms_of mono_curry mono_eval.
Proof.
split; first by move=> T S R f; apply/eq_mono; case.
by move=> /= T S R f; apply/eq_mono=> x; apply/eq_mono=> y.
Qed.

Definition mono_ccCatMixin := CCCatMixin mono_ccCatAxioms.
Canonical mono_ccCatType :=
  Eval hnf in CCCatType poType mono mono_ccCatMixin.

Lemma nat_apprP : Po.axioms leq.
Proof.
split.
- exact: leqnn.
- by move=> ???; apply: leq_trans.
- by move=> n m nm mn; apply: anti_leq; rewrite nm.
Qed.

Definition nat_poMixin := PoMixin nat_apprP.
Canonical nat_poType := Eval hnf in PoType nat nat_poMixin.

Module PoChoice.

Section ClassDef.

Record class_of (T : Type0) := Class {
  base_po : Po.class_of T;
  base_choice : Choice.class_of T
}.

Record type : Type1 := Pack {sort : Type0; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Local Coercion base_po : class_of >-> Po.class_of.
Local Coercion base_choice : class_of >-> Choice.class_of.
Variables (T : Type0) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack T :=
  [find p  | Po.sort p ~ T | "not a poType" ]
  [find c  | Choice.sort c ~ T | "not a choiceType" ]
  [find pm | Po.class p ~ pm ]
  [find cm | Choice.class c ~ cm ]
  @Pack T (Class pm cm).

Definition choiceType := @Choice.Pack cT xclass.
Definition poType := @Po.Pack cT xclass.

End ClassDef.

Module Exports.
Coercion base_po : class_of >-> Po.class_of.
Coercion base_choice : class_of >-> Choice.class_of.
Coercion sort : type >-> Sortclass.
Coercion poType : type >-> Po.type.
Canonical poType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation poChoiceType := type.
Notation PoChoiceType T := (@pack T _ unify _ unify _ unify _ unify).
Notation "[ 'poChoiceType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'poChoiceType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'poChoiceType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'poChoiceType'  'of'  T ]") : form_scope.
End Exports.

End PoChoice.

Export PoChoice.Exports.

Canonical dfun_poChoiceType T (S : T -> poChoiceType) :=
  PoChoiceType (dfun S).
Canonical sfun_poChoiceType T (S : poChoiceType) :=
  PoChoiceType (sfun T S).
Canonical prod_poChoiceType (T S : poChoiceType) :=
  PoChoiceType (T * S).
Canonical unit_poChoiceType := Eval hnf in PoChoiceType unit.

Section MonotoneChoice.

Variables (T : poType) (S : poChoiceType).

Definition mono_choiceMixin :=
  [choiceMixin of {mono T -> S} by <:].
Canonical mono_choiceType :=
  Eval hnf in ChoiceType (mono T S) mono_choiceMixin.
Canonical mono_poChoiceType :=
  Eval hnf in PoChoiceType (mono T S).
Canonical mono_of_choiceType :=
  Eval hnf in ChoiceType {mono T -> S} mono_choiceMixin.
Canonical mono_of_poChoiceType :=
  Eval hnf in PoChoiceType {mono T -> S}.

End MonotoneChoice.

Section SubsingPo.

Variable (T : poType).
Implicit Types (X Y Z : subsing T) (x y z : T).

Definition subsing_appr X Y : Prop :=
  forall x, X x -> exists2 y, Y y & x ⊑ y.

Lemma subsing_apprP : Po.axioms subsing_appr.
Proof.
split.
- move=> X x Xx; exists x=> //; reflexivity.
- move=> X Y Z XY YZ x /XY [] y /YZ [] z Zz yz xy.
  by exists z; last apply: transitivity xy yz.
- move=> X Y XY YX; apply: val_inj.
  apply: functional_extensionality=> x.
  apply: propositional_extensionality; split=> /=.
  + move=> Xx; case/XY: (Xx)=> [y Yy xy].
    case/YX: (Yy)=> x' Xx' yx'.
    rewrite (valP X _ _ Xx' Xx) in yx'.
    by rewrite (appr_anti xy yx').
  + move=> Yx; case/YX: (Yx)=> [y Xy xy].
    case/XY: (Xy)=> x' Yx' yx'.
    rewrite (valP Y _ _ Yx' Yx) in yx'.
    by rewrite (appr_anti xy yx').
Qed.

Definition subsing_poMixin := PoMixin subsing_apprP.
Canonical subsing_poType := Eval hnf in PoType (subsing T) subsing_poMixin.
Canonical subsing_poChoiceType := Eval hnf in PoChoiceType (subsing T).

Lemma subsing_of_appr x y : subsing_of x ⊑ subsing_of y <-> x ⊑ y.
Proof.
split; first by move=> /(_ x erefl) [y' ->].
by move=> xy x' <-; exists y.
Qed.

Lemma monotone_subsing_of : monotone subsing_of.
Proof. by move=> x y; rewrite subsing_of_appr. Qed.

Definition mono_subsing_of : {mono T -> subsing T} :=
  Sub subsing_of monotone_subsing_of.
Canonical mono_subsing_of.

Lemma subsing_botP X : subsing_bot ⊑ X.
Proof. by move=> x []. Qed.

Definition subsing_ppoMixin := PpoMixin subsing_botP.
Canonical subsing_ppoType :=
  Eval hnf in PpoType (subsing T) subsing_ppoMixin.

Definition sing_poMixin := [poMixin of sing T by <:].
Canonical sing_poType := Eval hnf in PoType (sing T) sing_poMixin.
Canonical sing_subPoType := Eval hnf in [subPoType of sing T].
Canonical sing_poChoiceType := Eval hnf in PoChoiceType (sing T).

End SubsingPo.

Arguments mono_subsing_of {_}.

Lemma monotone_liftss (T S : poType) (f : {mono T -> subsing S}) :
  monotone (liftss f).
Proof.
move=> X X' XX' y [x Xx fx].
case/(_ _ Xx): XX'=> [x' X'x' /(monoP f)/(_ _ fx) [y' fx' yy']].
by exists y'=> //; exists x'.
Qed.

Definition mono_liftss (T S : poType) (f : {mono T -> subsing S}) :
  {mono subsing T -> subsing S} :=
  Sub (liftss f) (@monotone_liftss _ _ f).
Canonical mono_liftss.
Arguments mono_liftss {_ _}.

Lemma monotone2_liftss (T S : poType) : monotone (@mono_liftss T S).
Proof.
move=> /= f g fg X y /= [x Xx fx].
case/(_ _ _ fx): fg=> [/= y' gx yy'].
by exists y'=> //; exists x.
Qed.

Definition mono2_liftss (T S : poType) :
  {mono {mono T -> subsing S} -> {mono subsing T -> subsing S}} :=
  Sub mono_liftss (@monotone2_liftss _ _).
Canonical mono2_liftss.

Definition mono_mapss (T S : poType) (f : {mono T -> S}) : {mono _ -> _} :=
  Eval hnf in Sub (mapss f) (@monotone_liftss _ _ (mono_subsing_of ∘ f)).
Canonical mono_mapss.
Arguments mono_mapss {_ _}.

Lemma monotone2_mapss (T S : poType) : monotone (@mono_mapss T S).
Proof.
move=> f g fg; rewrite appr_val /= /mapss.
by apply: monotone2_liftss; apply: monotone_mono_comp; first reflexivity.
Qed.

Definition mono2_mapss (T S : poType) :
  {mono {mono T -> S} -> {mono subsing T -> subsing S}} :=
  @Mono _ _ (@mono_mapss T S) (@monotone2_mapss T S).

Section Supremum.

Variable T : poType.

Definition ub (x : nat -> T) (ub_x : T) :=
  forall n, x n ⊑ ub_x.

Definition supremum (x : nat -> T) (sup_x : T) :=
  ub x sup_x /\ forall ub_x, ub x ub_x -> sup_x ⊑ ub_x.

Lemma supremum_unique (x : nat -> T) sup_x1 sup_x2 :
  supremum x sup_x1 -> supremum x sup_x2 -> sup_x1 = sup_x2.
Proof.
move=> [ub_x1 least_x1] [ub_x2 least_x2].
apply: appr_anti.
- exact: least_x1 ub_x2.
- exact: least_x2 ub_x1.
Qed.

Definition shift (x : nat -> T) n m := x (n + m).

Lemma supremum_shift (x : nat -> T) n sup_x :
  monotone x ->
  supremum x sup_x ->
  supremum (shift x n) sup_x.
Proof.
move=> x_mono [ub_x least_x]; split; first by move=> m; apply: ub_x.
move=> y ub_y; apply: least_x=> p.
apply: transitivity (x (n + p)) _ _ (ub_y _).
by apply: x_mono; apply: leq_addl.
Qed.

Definition osup (x : nat -> T) : subsing T := Sub (supremum x) (@supremum_unique x).

Lemma supremumC (x : nat -> nat -> T) (x1 x2 : nat -> T) :
  (forall n, supremum (x n) (x1 n)) ->
  (forall m, supremum (x^~ m) (x2 m)) ->
  supremum x1 = supremum x2.
Proof.
have H: forall x x1 x2, (forall n, supremum (x n) (x1 n)) ->
                        (forall m, supremum (x^~ m) (x2 m)) ->
                        forall sup_x,
                        supremum x1 sup_x -> supremum x2 sup_x.
  move=> {x x1 x2} x x1 x2 x1P x2P sup_x [ub_x] least_x; split.
  - move=> m; case: (x2P m)=> [ub_x2 least_x2].
    apply: least_x2=> n.
    apply: transitivity (ub_x n).
    by case: (x1P n)=> [ub_x1 _]; apply: ub_x1.
  - move=> y ub_y; apply: least_x=> n.
    case: (x1P n)=> [_ least_x1]; apply: least_x1.
    move=> m; apply: transitivity (ub_y m).
    by case: (x2P m)=> [ub_x2 _]; apply: ub_x2.
move=> x1P x2P.
apply/functional_extensionality=> sup_x.
apply/propositional_extensionality; split.
- exact: H x1P x2P sup_x.
- exact: (H (fun m n => x n m)) sup_x.
Qed.

End Supremum.

Module Cpo.

Record mixin_of (T : poType) := Mixin {
  sup : {mono nat -> T} -> T;
  _   : forall x : {mono nat -> T}, supremum x (sup x)
}.

Section ClassDef.

Record class_of (T : Type0) :=
  Class {base: PoChoice.class_of T; mixin : mixin_of (Po.Pack base)}.
Local Coercion base : class_of >-> PoChoice.class_of.

Record type : Type1 := Pack {sort : Type0; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type0) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  [find b | PoChoice.sort b ~ T | "not a poChoiceType" ]
  [find c | PoChoice.class b ~ c ]
  fun m => @Pack T (@Class _ c m).

Definition poChoiceType := @PoChoice.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition poType := @Po.Pack cT xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> PoChoice.class_of.
Coercion sort : type >-> Sortclass.
Coercion poChoiceType : type >-> PoChoice.type.
Canonical poChoiceType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion poType : type >-> Po.type.
Canonical poType.
Notation cpoType := type.
Notation cpoMixin := mixin_of.
Notation CpoMixin := Mixin.
Notation CpoType T m := (@pack T _ unify _ unify m).
Notation "[ 'cpoType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'cpoType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'cpoType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'cpoType'  'of'  T ]") : form_scope.
End Exports.

End Cpo.

Export Cpo.Exports.

Notation chain T := {mono nat -> T} (only parsing).

Definition sup (T : cpoType) (x : {mono nat -> T}) : T :=
  Cpo.sup (Cpo.mixin (Cpo.class T)) x.

Section CpoTheory.

Variable T : cpoType.

Lemma supP (x : chain T) : supremum x (sup x).
Proof. by case: T x=> [? [? []]]. Qed.

Lemma sup_unique (x : chain T) sup_x : supremum x sup_x -> sup x = sup_x.
Proof. exact: supremum_unique (supP x). Qed.

Lemma sup_const (x : T) : sup (mono_const _ x) = x.
Proof.
apply: sup_unique; split; first by move=> ?; reflexivity.
by move=> y /(_ 0).
Qed.

Lemma monotone_shift (f : chain T) n : monotone (shift f n).
Proof.
move=> m1 m2 m12; rewrite /shift; apply: monoP.
by rewrite /appr /= leq_add2l.
Qed.

Definition mono_shift (f : chain T) n : chain T :=
  Sub (shift f n) (monotone_shift f n).
Canonical mono_shift.

Lemma sup_shift (f : chain T) n : sup (mono_shift f n) = sup f.
Proof.
apply/sup_unique.
by apply: supremum_shift (@monoP _ _ _) (supP _).
Qed.

End CpoTheory.

Definition unit_sup (f : chain unit) := tt.

Lemma unit_supP (f : chain unit) : supremum f (unit_sup f).
Proof. by split. Qed.

Definition unit_cpoMixin := CpoMixin unit_supP.
Canonical unit_cpoType :=
  Eval hnf in CpoType unit unit_cpoMixin.

Section SubCpo.

Variables (T : cpoType) (P : T -> Prop).

Definition subCpo_axiom_of (S : subPoType P) :=
  forall (x : chain S), P (sup (mono_val' ∘ x)).

Record subCpoType := SubCpoType {
  subCpo_sort  :> subPoType P;
  subCpo_axiom :  subCpo_axiom_of subCpo_sort
}.

Definition clone_subCpoType (U : Type) :=
  [find sT1 : subType P   | sub_sort    sT1 ~ U   | "not a subType"    ]
  [find sT2 : subPoType P | subPo_sort  sT2 ~ sT1 | "not a subPoType"  ]
  [find sT  : subCpoType  | subCpo_sort sT  ~ sT2 | "not a subCpoType" ]
  sT.

Variable sT : subCpoType.

Definition subCpo_sup (x : chain sT) : sT :=
  Sub (sup (mono_val' ∘ x)) (@subCpo_axiom sT x).

Lemma subCpo_supP (x : chain sT) : supremum x (subCpo_sup x).
Proof.
have [ub_x least_x] := supP (mono_comp mono_val' x); split.
  by move=> n; rewrite appr_val /subCpo_sup SubK; apply: ub_x.
move=> y ub_y; rewrite appr_val /subCpo_sup SubK.
by apply: least_x=> n /=; rewrite -appr_val; apply: ub_y.
Qed.

Definition SubCpoMixin := CpoMixin subCpo_supP.
Canonical subCpoType_poChoiceType := Eval hnf in PoChoiceType sT.
Canonical subCpoType_cpoType := Eval hnf in CpoType sT SubCpoMixin.

End SubCpo.

Notation "[ 'subCpoType' 'of' T ]" :=
  (@clone_subCpoType _ _ T _ unify _ unify _ unify)
  (at level 0, format "[ 'subCpoType'  'of'  T ]") : form_scope.
Notation "[ 'cpoMixin' 'of' T 'by' <: ]" :=
  (@SubCpoMixin _ _ [subCpoType of T])
  (at level 0, format "[ 'cpoMixin'  'of'  T  'by'  <: ]") : form_scope.

Module Pcpo.

Section ClassDef.

Record class_of (T : Type0) :=
  Class {base: Cpo.class_of T; mixin : Ppo.mixin_of (Po.Pack base)}.
Local Coercion base : class_of >-> Cpo.class_of.

Record type : Type1 := Pack {sort : Type0; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type0) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  [find b  | Cpo.sort  b ~ T  | "not a cpoType" ]
  [find c  | Cpo.class b ~ c ]
  [find b' | Ppo.sort  b' ~ T | "not a ppoType" ]
  [find m  | Ppo.mixin (Ppo.class b') ~ m ]
  @Pack T (@Class T c m).

Definition cpoType := @Cpo.Pack cT xclass.
Definition poChoiceType := @PoChoice.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition ppoType := @Ppo.Pack cT (@Ppo.Class _ xclass (mixin xclass)).
Definition poType := @Po.Pack cT xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Cpo.class_of.
Coercion sort : type >-> Sortclass.
Coercion cpoType : type >-> Cpo.type.
Canonical cpoType.
Coercion poChoiceType : type >-> PoChoice.type.
Canonical poChoiceType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion ppoType : type >-> Ppo.type.
Canonical ppoType.
Coercion poType : type >-> Po.type.
Canonical poType.
Notation pcpoType := type.
Notation PcpoType T := (@pack T _ unify _ unify _ unify _ unify).
Notation "[ 'pcpoType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'pcpoType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'pcpoType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'pcpoType'  'of'  T ]") : form_scope.
End Exports.

End Pcpo.

Export Pcpo.Exports.

Canonical unit_pcpoType := Eval hnf in PcpoType unit.

Lemma monotone_dflip (T : poType) S (R : S -> poType)
      (f : {mono T -> dfun R}) x : monotone (flip f x).
Proof.
by move=> y z yz; rewrite /flip; apply: (valP f _ _ yz).
Qed.

Definition mono_dflip (T : poType) S (R : S -> poType)
  (f : {mono T -> dfun R}) x :
  {mono T -> R x} :=
  Sub (flip f x) (@monotone_dflip T S R f x).

Definition mono_sflip (T : poType) S (R : poType)
  (f : {mono T -> sfun S R}) x : {mono T -> R} :=
  Sub (flip f x) (@monotone_dflip T S (fun _ => R) f x).

Lemma monotone_flip (T S R : poType) (f : {mono T -> {mono S -> R}}) :
  monotone (mono_sflip (mono_val' ∘ f)).
Proof.
move=> x1 x2 x12 y /=; rewrite /flip /=; exact: (valP (f y) _ _).
Qed.

Definition mono_flip (T S R : poType) (f : {mono T -> {mono S -> R}}) :
  {mono S -> {mono T -> R}} :=
  Eval hnf in Sub (mono_sflip (mono_val' ∘ f)) (monotone_flip f).
Canonical mono_flip.

Section DFunCpo.

Variables (T : Type) (S : T -> cpoType).

Definition dfun_sup f : dfun S :=
  fun x => sup (mono_dflip f x).

Lemma dfun_supP (f : chain (dfun S)) : supremum f (dfun_sup f).
Proof.
split.
- move=> n x; rewrite /dfun_sup.
  have [ub_fx _] := supP (mono_dflip f x).
  exact: ub_fx.
- move=> g ub_g x; rewrite /dfun_sup.
  have [_ least_fx] := supP (mono_dflip f x).
  apply: least_fx=> n; exact: ub_g.
Qed.

Definition dfun_cpoMixin := CpoMixin dfun_supP.
Canonical dfun_cpoType := Eval hnf in CpoType (dfun S) dfun_cpoMixin.

End DFunCpo.

Canonical sfun_cpoType (T : Type) (S : cpoType) :=
  Eval hnf in CpoType (sfun T S) (dfun_cpoMixin _).

Section MonoCpo.

Variables (T : poType) (S : cpoType).

Lemma mono_sup_clos : subCpo_axiom_of (mono_subPoType T S).
Proof.
move=> /= f x y xy.
rewrite /sup /= /dfun_sup.
have [_ least_fx] := supP (mono_dflip (mono_comp mono_val' f) x).
apply: least_fx => n /=.
apply: transitivity (valP (f n) _ _ xy) _.
have [ub_fy _] := supP (mono_dflip (mono_comp mono_val' f) y).
exact: ub_fy.
Qed.

Canonical mono_subCpoType := Eval hnf in SubCpoType mono_sup_clos.
Definition mono_cpoMixin := [cpoMixin of mono T S by <:].
Canonical mono_cpoType := Eval hnf in CpoType (mono T S) mono_cpoMixin.
Canonical mono_of_cpoType := Eval hnf in CpoType {mono T -> S} mono_cpoMixin.

End MonoCpo.

Lemma supC (T : cpoType) (f : {mono nat -> {mono nat -> T}}) :
  sup (sup f) = sup (sup (mono_flip f)).
Proof.
apply: supremum_unique (supP (sup f)) _.
rewrite -(@supremumC T (val \o f) (sup (mono_flip f)) _); first exact: supP.
- move=> n; exact: (supP (mono_dflip (mono_comp mono_val' (mono_flip f)) n)).
- move=> m; exact: (supP (mono_dflip (mono_comp mono_val' f) m)).
Qed.

Lemma supD (T : cpoType) (f : {mono nat -> {mono nat -> T}}) :
  sup (sup f) = sup (uncurry f ∘ ⟨1, 1⟩).
Proof.
have [ub_f1 least_f1] := supP (sup f).
have [ub_f2 least_f2] := supP f.
apply/esym/sup_unique; split.
- move=> n /=; apply: transitivity (ub_f1 n); exact: ub_f2.
- move=> x xP; apply: least_f1=> n.
  suffices /least_f2 : ub f (mono_const _ x) by apply.
  move=> {n} n m /=; apply: transitivity (xP (maxn n m))=> /=.
  move: (monoP f (leq_maxl n m) m) => H.
  apply: transitivity H _; apply: monoP; exact: leq_maxr.
Qed.

Lemma monotone_sup (T : cpoType) : monotone (@sup T).
Proof.
move=> f g fg.
case: (supP f)=> _; apply=> n.
apply: transitivity (fg n) _.
case: (supP g)=> H _; exact: H.
Qed.

Definition mono_sup (T : cpoType) : {mono chain T -> T} :=
  Mono (@sup T) (@monotone_sup T).

Section Continuous.

Variables T S : cpoType.

Definition continuous (f : {mono T -> S}) :=
  forall (x : chain T), sup (f ∘ x) = f (sup x).

Record cont := Cont {
  cont_val :> {mono T -> S};
  _        :  continuous cont_val
}.

Definition cont_of of phant (T -> S) := cont.

Identity Coercion cont_of_cont_of : cont_of >-> cont.

Local Notation "{ 'cont' R }" := (cont_of (Phant R))
  (at level 0, format "{ 'cont'  R }").

Canonical cont_subType := [subType for cont_val].
Definition cont_poMixin := [poMixin of {cont T -> S} by <:].
Canonical cont_poType := Eval hnf in PoType cont cont_poMixin.
Canonical cont_subPoType := [subPoType of {cont T -> S}].
Definition cont_choiceMixin := [choiceMixin of {cont T -> S} by <:].
Canonical cont_choiceType := Eval hnf in ChoiceType cont cont_choiceMixin.
Canonical cont_poChoiceType := Eval hnf in PoChoiceType cont.

Canonical cont_of_subType := Eval hnf in [subType of {cont T -> S}].
Canonical cont_of_poType := Eval hnf in PoType {cont T -> S} cont_poMixin.
Canonical cont_of_subPoType := [subPoType of {cont T -> S}].
Canonical cont_of_choiceType := Eval hnf in ChoiceType {cont T -> S} cont_choiceMixin.
Canonical cont_of_poChoiceType := Eval hnf in PoChoiceType {cont T -> S}.

Lemma contP (f : {cont T -> S}) : continuous f.
Proof. exact: valP. Qed.

Lemma eq_cont (f g : {cont T -> S}) : f =1 g <-> f = g.
Proof.
split; last move=> -> //; move=> e; do 2![apply: val_inj].
exact: functional_extensionality e.
Qed.

Lemma cont_sup_clos : subCpo_axiom_of cont_subPoType.
Proof.
move=> /= f x.
rewrite {3}/sup /= {3}/sup /= /dfun_sup /=.
have -> : mono_dflip (mono_val' ∘ (mono_val' ∘ f)) (sup x) =
          sup (mono_flip (mono_comp mono_val' f) ∘ x).
  apply: val_inj; apply: functional_extensionality=> n /=.
  rewrite /flip /= -(valP (f n)); congr sup.
  by apply: val_inj; apply: functional_extensionality.
rewrite supC; congr sup; apply: val_inj.
apply: functional_extensionality=> m /=.
rewrite /sup /= /dfun_sup; congr sup; apply: val_inj.
by apply: functional_extensionality.
Qed.

Canonical cont_subCpoType := SubCpoType cont_sup_clos.
Definition cont_cpoMixin := [cpoMixin of cont by <:].
Canonical cont_cpoType := Eval hnf in CpoType cont cont_cpoMixin.
Canonical cont_of_cpoType := Eval hnf in CpoType {cont T -> S} cont_cpoMixin.

End Continuous.

Local Notation "{ 'cont' R }" := (cont_of (Phant R))
  (at level 0, format "{ 'cont'  R }") : type_scope.

Arguments Cont {_ _}.

Section ContinuousPcpo.

Variables (T : cpoType) (S : pcpoType).

Lemma continuous_mono_bot : continuous (@mono_bot T S).
Proof.
move=> x.
have -> : mono_bot T S ∘ x = mono_const _ ⊥ by apply: val_inj.
by rewrite sup_const.
Qed.

Definition cont_bot : {cont T -> S} :=
  Eval hnf in Sub (mono_bot _ _) continuous_mono_bot.

Lemma cont_botP f : cont_bot ⊑ f.
Proof. move=> x; exact: botP. Qed.

Definition cont_ppoMixin := PpoMixin cont_botP.
Canonical cont_ppoType := Eval hnf in PpoType {cont T -> S} cont_ppoMixin.
Canonical cont_pcpoType := Eval hnf in PcpoType {cont T -> S}.

End ContinuousPcpo.

Lemma continuous_dflip (T : cpoType) S (R : S -> cpoType)
      (f : {cont T -> dfun R}) x : continuous (mono_dflip f x).
Proof.
move=> y; rewrite /= /flip -(valP f) {2}/sup /= /dfun_sup.
congr sup; exact: val_inj.
Qed.

Definition cont_dflip (T : cpoType) S (R : S -> cpoType)
  (f : {cont T -> dfun R}) x :
  {cont T -> R x} :=
  Sub (mono_dflip f x) (@continuous_dflip T S R f x).
Canonical cont_dflip.

Definition cont_sflip (T : cpoType) S (R : cpoType)
  (f : {cont T -> sfun S R}) x : {cont T -> R} :=
  Sub (mono_sflip f x) (@continuous_dflip T S (fun _ => R) f x).
Canonical cont_sflip.

Lemma continuous_val' (T : cpoType) (P : T -> Prop) (sT : subCpoType P) :
  continuous (@mono_val' T P sT).
Proof.
by move=> /= x; rewrite {2}/sup /= /subCpo_sup SubK.
Qed.

Definition cont_val' (T : cpoType) (P : T -> Prop) (sT : subCpoType P) :
  {cont sT -> T} :=
  Sub mono_val' (@continuous_val' _ _ sT).
Canonical cont_val'.
Arguments cont_val' {_ _ _}.

Section ContinuousComp.

Variables (T S R : cpoType).

Lemma continuous_comp (f : {mono S -> R}) (g : {mono T -> S}) :
  continuous f -> continuous g -> continuous (f ∘ g).
Proof.
by move=> f_cont g_cont x /=; rewrite -g_cont -f_cont compA.
Qed.

Definition cont_comp (f : {cont S -> R}) (g : {cont T -> S}) : {cont T -> R} :=
  Sub (val f ∘ val g) (continuous_comp (valP f) (valP g)).
Canonical cont_comp.

Lemma continuous_id : continuous (@mono_id T).
Proof. by move=> x; rewrite comp1f. Qed.

Definition cont_id : {cont T -> T} := Sub 1 continuous_id.
Canonical cont_id.

End ContinuousComp.

Arguments cont_id {_}.

Lemma cont_compA (A B C D : cpoType) (f : {cont C -> D}) (g : {cont B -> C}) (h : {cont A -> B}) :
  cont_comp f (cont_comp g h) = cont_comp (cont_comp f g) h.
Proof. exact/val_inj/mono_compA. Qed.

Lemma cont_compf1 (A B : cpoType) (f : {cont A -> B}) : cont_comp f cont_id = f.
Proof. by apply: val_inj; rewrite /= compf1. Qed.

Lemma cont_comp1f (A B : cpoType) (f : {cont A -> B}) : cont_comp cont_id f = f.
Proof. by apply: val_inj; rewrite /= comp1f. Qed.

Definition cont_catMixin := CatMixin (And3 cont_comp1f cont_compf1 cont_compA).
Canonical cont_catType := Eval hnf in CatType cpoType cont cont_catMixin.

Lemma cont_compE (T S R : cpoType)
  (f : {cont S -> R}) (g : {cont T -> S}) (x : T)
  : (f ∘ g) x = f (g x).
Proof. by []. Qed.

Definition cont_bang (T : cpoType) : {cont T -> unit} :=
  Cont (mono_bang T) (fun _ => erefl).

Program Definition cont_termCatMixin :=
  @TermCatMixin _ _ _ cont_bang _.

Next Obligation.
by move=> T f; apply/eq_cont=> x; case: (f x).
Qed.

Canonical cont_termCatType :=
  Eval hnf in TermCatType cpoType cont cont_termCatMixin.

Lemma monotone_cont_comp (T S R : cpoType) (f1 f2 : {cont S -> R}) (g1 g2 : {cont T -> S}) :
  f1 ⊑ f2 -> g1 ⊑ g2 -> f1 ∘ g1 ⊑ f2 ∘ g2.
Proof. exact: monotone_mono_comp. Qed.

Lemma monotone_cont_compp (T S R : cpoType) :
  @monotone (prod_poType (cont_poType S R) (cont_poType T S)) _ (@compp _ T S R).
Proof.
move=> [x1 y1] [x2 y2] [/= x11 y12]; exact: monotone_cont_comp.
Qed.

Definition mono_cont_compp (T S R : cpoType) :
  {mono {cont S -> R} * {cont T -> S} -> {cont T -> R}} :=
  Mono _ (@monotone_cont_compp T S R).
Arguments mono_cont_compp {_ _ _}.

Lemma continuous_cast T (S : T -> cpoType) x y (e : x = y) : continuous (mono_cast S e).
Proof. case: y / e=> /=; rewrite mono_cast1; exact: continuous_id. Qed.

Definition cont_cast T (S : T -> cpoType) x y (e : x = y) : {cont _ -> _} :=
  Sub (mono_cast S e) (continuous_cast e).

Lemma continuous_valV (T S : cpoType) (P : S -> Prop) (sS : subCpoType P) (f : {mono T -> sS}) :
  continuous (mono_val' ∘ f) -> continuous f.
Proof.
move=> f_cont x; apply: val_inj.
rewrite {1}/sup /= /subCpo_sup SubK; move: (f_cont x)=> /= <-.
by rewrite compA.
Qed.

Lemma continuous_const (T S : cpoType) (x : S) : continuous (@mono_const T S x).
Proof. by move=> y; rewrite mono_comp_constL sup_const. Qed.

Definition cont_const (T S : cpoType) (x : S) : {cont T -> S} :=
  Eval hnf in Sub (@mono_const T S x) (continuous_const x).
Canonical cont_const.

Definition pcpo_cont (T S : pcpoType) := cont T S.
Canonical pcpo_cont_ppoType T S :=
  Eval hnf in PpoType (pcpo_cont T S) (cont_ppoMixin T S).
Canonical pcpo_cont_pcpoType T S :=
  Eval hnf in PcpoType (pcpo_cont T S).

Definition pcpo_contP : @Cat.axioms pcpoType pcpo_cont
                                    (fun T S R f g => f ∘ g)
                                    (fun T => 1).
Proof.
by split; move=> *; rewrite ?comp1f ?compf1 ?compA.
Qed.

Definition pcpo_cont_catMixin := CatMixin pcpo_contP.
Canonical pcpo_cont_catType :=
  Eval hnf in CatType pcpoType pcpo_cont pcpo_cont_catMixin.

Lemma continuous_sup (T : cpoType) : continuous (mono_sup T).
Proof.
by move=> f /=; rewrite supC; do 2![congr sup; apply/eq_mono=> ?].
Qed.

Definition cont_sup (T : cpoType) := Cont (mono_sup T) (@continuous_sup T).

Section ProdCpo.

Variables T S : cpoType.

Definition prod_sup (x : chain (T * S)) :=
  (sup ('π1 ∘ x), sup ('π2 ∘ x)).

Lemma prod_supP (x : chain (T * S)) : supremum x (prod_sup x).
Proof.
rewrite /prod_sup.
case: (supP ('π1 ∘ x)) => [ub_x1 least_x1].
case: (supP ('π2 ∘ x)) => [ub_x2 least_x2].
split.
  by move=> n; split=> /=; [apply: ub_x1|apply: ub_x2].
case=> y1 y2 ub_y; split; [apply: least_x1|apply: least_x2];
by move=> n; case: (ub_y n).
Qed.

Definition prod_cpoMixin := CpoMixin prod_supP.
Canonical prod_cpoType := Eval hnf in CpoType (T * S) prod_cpoMixin.

Lemma continuous_fst : continuous (@mono_fst T S).
Proof. by []. Qed.

Definition cont_fst : {cont T * S -> T} :=
  Sub mono_fst continuous_fst.
Canonical cont_fst.

Lemma continuous_snd : continuous (@mono_snd T S).
Proof. by []. Qed.

Definition cont_snd : {cont T * S -> S} :=
  Sub mono_snd continuous_snd.
Canonical cont_snd.

Lemma continuous_pairf (R : cpoType) (f : {cont R -> T}) (g : {cont R -> S}) :
  continuous (mono_pairf f g).
Proof.
move=> x; rewrite {1}/sup /=; congr pair; rewrite -contP; congr sup;
exact: val_inj.
Qed.

Definition cont_pairf (R : cpoType) (f : {cont R -> T}) (g : {cont R -> S}) :
  {cont R -> T * S} :=
  Sub (@mono_pairf _ _ _ f g) (continuous_pairf f g).
Canonical cont_pairf.

Lemma sup_pairf (f : chain T) (g : chain S) :
  sup (mono_pairf f g) = (sup f, sup g).
Proof.
by rewrite {1}/sup /= /prod_sup; congr (sup _, sup _); apply/eq_mono.
Qed.

Lemma continuous2P (R : cpoType) (f : {mono T * S -> R}) :
  continuous f <->
  (forall (x : chain T) y,
      f (sup x, y) = sup (f ∘ mono_pairf x (mono_const _ y))) /\
  (forall x (y : chain S),
      f (x, sup y) = sup (f ∘ mono_pairf (mono_const _ x) y)).
Proof.
split; first move=> cont_f; first split.
- move=> x y; rewrite cont_f {2}/sup /= /prod_sup -{1}[y]sup_const.
  congr (f (sup _, sup _)); by apply/eq_mono.
- move=> x y; rewrite cont_f {2}/sup /= /prod_sup -{1}[x]sup_const.
  congr (f (sup _, sup _)); by apply/eq_mono.
case=> cont_f1 cont_f2 /= x; rewrite {2}/sup /= /prod_sup.
apply: sup_unique; split.
  move=> n /=; apply: monoP.
  case: (supP (mono_fst ∘ x))=> [/(_ n) /= ub_x1 _].
  case: (supP (mono_snd ∘ x))=> [/(_ n) /= ub_x2 _].
  by split.
move=> y ub_y; rewrite cont_f1.
case: (supP (f ∘ mono_pairf (mono_fst ∘ x) (mono_const _ (sup (mono_snd ∘ x))))).
move=> _; apply=> n; rewrite /=; unfold pairf; rewrite /constfun /= cont_f2.
case: (supP (f ∘ mono_pairf (mono_const _ (x n).1) (mono_snd ∘ x))).
move=> _; apply=> m; rewrite /=; unfold pairf; rewrite /constfun /=.
by apply: transitivity (ub_y (maxn n m)); apply: monoP; split=> /=;
apply monoP; apply: monoP; [exact: leq_maxl|exact: leq_maxr].
Qed.

End ProdCpo.

Lemma cont_prodCatAxioms : ProdCat.axioms_of cont_pairf cont_fst cont_snd.
Proof.
split; try by move=> T S R f g; apply/eq_cont.
move=> T S R f g [/eq_cont H1 /eq_cont H2]; apply/eq_cont=> x.
by move: (H1 x) (H2 x)=> /=; case: (f x) (g x)=> [??] [??] /=  -> ->.
Qed.

Definition cont_prodCatMixin := ProdCatMixin cont_prodCatAxioms.
Canonical cont_prodCatType :=
  Eval hnf in ProdCatType cpoType cont cont_prodCatMixin.
Canonical cont_cartCatType :=
  Eval hnf in CartCatType cpoType cont.

Arguments cont_fst {_ _}.
Arguments cont_snd {_ _}.
Arguments cont_pairf {_ _ _}.

Program Definition cont_curry (T S R : cpoType) (f : {cont T * S -> R}) :
    {cont T -> {cont S -> R}} :=
  Cont (Mono (fun x => Cont (mono_curry f x) _) _) _.

Next Obligation.
move=> T S R f x y /=.
case/continuous2P: (contP f)=> _ ->; congr sup.
by apply/eq_mono.
Qed.

Next Obligation.
by move=> T S R f x1 x2 x12; move=> y /=; apply: monoP; split=> //;
reflexivity.
Qed.

Next Obligation.
move=> T S R f x; apply/eq_cont=> y /=.
case/continuous2P: (contP f)=> -> _; congr sup.
by apply/eq_mono.
Qed.

Program Definition cont_eval (T S : cpoType) :
    {cont {cont T -> S} * T -> S} :=
  Cont (Mono (fun p => p.1 p.2) _) _.

Next Obligation.
move=> T S [/= f x] [/= g y] [/= fg xy].
apply: transitivity (monoP g xy); exact: fg.
Qed.

Next Obligation.
move=> T S; apply/continuous2P; split.
  by move=> /= x y; congr sup; apply/eq_mono.
by move=> /= x y; rewrite -contP; congr sup; apply/eq_mono.
Qed.

Lemma cont_ccCatAxioms : CCCat.axioms_of cont_curry cont_eval.
Proof.
split; first by move=> /= T S R f; apply/eq_cont; case.
by move=> /= T S R f; apply/eq_cont=> x; apply/eq_cont.
Qed.

Definition cont_ccCatMixin := CCCatMixin cont_ccCatAxioms.
Canonical cont_ccCatType :=
  Eval hnf in CCCatType cpoType cont cont_ccCatMixin.

Lemma continuous_cont_compR (T S R : cpoType)
  (f : {cont S -> R}) (g : chain {cont T -> S}) :
  f ∘ sup g = sup (mono_cont_compp ∘ mono_pairf (mono_const _ f) g).
Proof.
apply/eq_cont=> x /=; rewrite -contP; congr sup.
by apply/eq_mono.
Qed.

Lemma continuous_cont_compL (T S R : cpoType)
  (f : chain {cont S -> R}) (g : {cont T -> S}) :
  sup f ∘ g = sup (mono_cont_compp ∘ mono_pairf f (mono_const _ g)).
Proof.
apply/eq_cont=> x /=; rewrite /sup /= /dfun_sup; congr sup.
by apply/eq_mono.
Qed.

Lemma continuous_cont_compp (T S R : cpoType) :
  continuous (@mono_cont_compp T S R).
Proof.
apply/continuous2P; split;
[exact: continuous_cont_compL|exact: continuous_cont_compR].
Qed.

Definition cont_compp (T S R : cpoType) :
  {cont {cont S -> R} * {cont T -> S} -> {cont T -> R}} :=
  Sub (@mono_cont_compp T S R) (@continuous_cont_compp T S R).
Arguments cont_compp {_ _ _}.

Section Kleene.

Variable T : pcpoType.

Lemma kfix_body_proof (f : {cont T -> T}) : monotone (fun n => iter n f ⊥).
Proof.
move=> n m; elim: m n=> [|m IH] [|n] //= H; try exact: botP.
by apply: monoP; apply: IH.
Qed.

Definition kfix_body f : chain T := Mono _ (kfix_body_proof f).

Lemma monotone_kfix_body : monotone kfix_body.
Proof.
move=> f g fg n /=; elim: n=> [|n IH]; first exact: appr_refl.
by apply: transitivity (monoP f IH) _; apply: fg.
Qed.

Definition mono_kfix_body : {mono {cont T -> T} -> chain T} :=
  Mono _ monotone_kfix_body.
Canonical mono_kfix_body.

Lemma continuous_kfix_body : continuous mono_kfix_body.
Proof.
move=> /= f; apply/eq_mono=> n /=.
rewrite {1}/sup /= /dfun_sup /=.
set F : nat -> {mono nat -> T} := mono_dflip _.
elim: n=> [|n IH] /=.
  by rewrite -[RHS]sup_const; congr sup; apply/eq_mono.
rewrite -{}IH 2!contP -[RHS]contP.
have -> : F n.+1 = uncurry (λ (eval _ _ ∘ ⟨mono_val' ∘ f ∘ 'π1, F n ∘ 'π2⟩)) ∘ ⟨1, 1⟩.
  by apply/eq_mono.
rewrite -supD; by do 2![congr sup; apply/eq_mono=> ?].
Qed.

Definition cont_kfix_body : {cont {cont T -> T} -> chain T} :=
  Cont _ continuous_kfix_body.
Canonical cont_kfix_body.

Definition kfix : {cont {cont T -> T} -> T} :=
  cont_sup _ ∘ cont_kfix_body.

Lemma kfixP (f : {cont T -> T}) : f (kfix f) = kfix f.
Proof.
rewrite /kfix -contP -[RHS](sup_shift _ 1); congr sup; exact/eq_mono.
Qed.

End Kleene.

Section SubsingCpo.

Variables (T : cpoType).

Definition subsing_sup_def (X : chain (subsing T)) x :=
  exists (y : chain T) (n : nat),
  (forall m, X (n + m) (y m)) /\ x = sup y.

Lemma subsing_sup_subproof X x1 x2 :
  subsing_sup_def X x1 -> subsing_sup_def X x2 -> x1 = x2.
Proof.
move=> [y1 [n1 [y1X ->]]] [y2 [n2 [y2X ->]]].
rewrite -(sup_shift y1 (n2 - n1)) -(sup_shift y2 (n1 - n2)).
congr sup; apply/eq_mono=> m /=; apply: subsing_of_inj.
rewrite /shift /= -(in_subsing (y1X _)) -(in_subsing (y2X _)).
by rewrite !addnA -!maxnE maxnC.
Qed.

Definition subsing_sup (X : chain (subsing T)) : subsing T :=
  Eval hnf in Sub (subsing_sup_def X) (@subsing_sup_subproof X).

Lemma subsing_supP (X : chain (subsing T)) : supremum X (subsing_sup X).
Proof.
split.
- move=> n x /= Xnx.
  have H : forall m, exists x', X (n + m) x'.
    by move=> m; case: (valP X _ _ (leq_addr m n) _ Xnx)=> x'; eauto.
  pose y x' := val (choose (H x')).
  have y_mono : monotone y.
    move=> n1 n2 n1n2.
    have X_n1 : X (n + n1) (y n1) := valP _.
    have X_n2 : X (n + n2) (y n2) := valP _.
    have {n1n2} n1n2: (n + n1) <= (n + n2) by rewrite leq_add2l.
    have [x' X_n2' ?] := valP X _ _ n1n2 _ X_n1.
    by rewrite (valP (X (n + n2)) _ _ X_n2 X_n2').
  exists (sup (Mono _ y_mono)).
    exists (Mono _ y_mono), n; split=> //.
    by move=> m; apply/(valP (choose (H m))).
  suffices -> : x = y 0.
    by case: (supP (Mono _ y_mono))=> [/= ub_y _]; apply: ub_y.
  rewrite /y; case: (choose _)=> z; rewrite /= addn0=> zP.
  by rewrite (valP (X n) _ _ Xnx zP).
- move=> /= ub_X ub_XP _ [y [n [eq_y ->]]].
  move/(_ (n + 0)): (ub_XP); rewrite (in_subsing (eq_y _)).
  case/(_ _ erefl)=> z zP _; exists z=> //.
  case: (supP y)=> _; apply=> m; apply/subsing_of_appr.
  rewrite -(in_subsing (eq_y _)) -(in_subsing zP); exact: ub_XP.
Qed.

Definition subsing_cpoMixin := CpoMixin subsing_supP.
Canonical subsing_cpoType := Eval hnf in CpoType (subsing T) subsing_cpoMixin.
Canonical subsing_pcpoType := Eval hnf in PcpoType (subsing T).

Lemma continuous_subsing_of : continuous (@mono_subsing_of T).
Proof.
move=> x; apply: val_inj; apply: functional_extensionality=> y /=.
apply: propositional_extensionality; split; last first.
  move=> <- {y}; exists x, 0; split=> //; exact: supP.
case=> [x' [n [/= x'E ->]]].
rewrite -(sup_shift x n); congr sup; apply/eq_mono=> m /=; exact: x'E.
Qed.

Definition cont_subsing_of : {cont T -> subsing T} :=
  Sub mono_subsing_of continuous_subsing_of.
Canonical cont_subsing_of.

End SubsingCpo.

Arguments cont_subsing_of {_}.

Lemma continuous_liftss (T S : cpoType) (f : {cont T -> subsing S}) :
  continuous (mono_liftss f).
Proof.
move=> /= X; apply: val_inj; apply: functional_extensionality=> sup_y /=.
apply: propositional_extensionality; split.
- case=> [y [n [fXE ->]]].
  pose P m x := X (n + m) x /\ f x (y m).
  have Pss : forall m x1 x2, P m x1 -> P m x2 -> x1 = x2.
    by move=> m x1 x2 [/= H1 _] [/= H2 _]; apply: subsingP H1 H2.
  have {fXE} fXE: forall m, exists x, (Subsing _ (Pss m)) x.
    by move=> m; rewrite /=; case: (fXE m); rewrite /P /=; eauto.
  pose x m := val (choose (fXE m)).
  have x_mono : monotone x.
    move=> m1 m2 m12; rewrite /x.
    case: (choose (fXE m1))=> [x1 /= [x1P fx1]].
    case: (choose (fXE m2))=> [x2 /= [x2P fx2]].
    move: m12; rewrite {1}/appr /= -(leq_add2l n).
    case/(monoP X)/(_ _ x1P)=> [x2' x2'P].
    by rewrite (subsingP x2P x2'P).
  exists (sup (Mono _ x_mono)).
    exists (Mono _ x_mono), n; split=> // m; rewrite /= /x.
    by case: (choose _)=> [? [??]].
  rewrite -contP; exists y, 0; split=> // m; rewrite /= /x.
  by case: (choose _)=> [? []].
- case=> [_ [x [n [XE ->]]]].
  rewrite -contP; case=> [y [n' [fXE ->]]].
  exists y, (n' + n); split=> // m; rewrite /=.
  exists (x (n' + m)); last exact: fXE.
  rewrite [n' + n]addnC -addnA; exact: XE.
Qed.

Definition cont_liftss (T S : cpoType) (f : {cont T -> subsing S}) :
  {cont subsing T -> subsing S} :=
  Sub (mono_liftss f) (continuous_liftss f).
Canonical cont_liftss.

Lemma monotone2_cont_liftss (T S : cpoType) : monotone (@cont_liftss T S).
Proof. exact: monotone2_liftss. Qed.

Definition mono2_cont_liftss (T S : cpoType) :
  {mono {cont T -> subsing S} -> {cont subsing T -> subsing S}} :=
  Sub _ (@monotone2_cont_liftss T S).
Canonical mono2_cont_liftss.
Arguments mono2_cont_liftss {_ _}.

Lemma continuous2_liftss (T S : cpoType) : continuous (@mono2_cont_liftss T S).
Proof.
move=> /= f; apply/eq_cont=> /= X; apply/eq_subsing=> sup_fx; split.
- case=> y [/= n [fXE ->]] {sup_fx}.
  case/(_ 0): (fXE)=> [x Xx _]; exists x=> //.
  exists y, n; split=> // m /=; rewrite /flip /=.
  by case/(_ m): (fXE)=> _ /(subsingP Xx) <-.
- case=> [x Xx [y [n [/= fXE ->]]]]; exists y, n; split=> // m /=.
  exists x=> //; exact: fXE.
Qed.

Definition cont2_liftss (T S : cpoType) :
  {cont {cont T -> subsing S} -> {cont subsing T -> subsing S}} :=
  Sub _ (@continuous2_liftss T S).
Canonical cont2_liftss.
Arguments cont2_liftss {_ _}.

Program Definition subsing_functor : {functor cpoType -> pcpoType} :=
  Functor subsing_pcpoType
          (fun T S f => cont_liftss (cont_subsing_of ∘ f))
          _ _.

Next Obligation.
move=> T /=; rewrite compf1; do 2![apply/val_inj]=> /=.
by rewrite liftss1.
Qed.

Next Obligation.
move=> T S R f g /=; do 2![apply/val_inj]=> /=.
rewrite liftss_comp -!fun_compE [in LHS]compA [in RHS]compA !fun_compE.
by rewrite liftss_comp1.
Qed.

(*Section InverseLimit.

Variable T : nat -> pcpoType.
Variable p : forall n, pcpo_cont (T n.+1) (T n).

Record invlim := InvLim {
  invlim_val : dfun T;
  _          : forall n, invlim_val n = p n (invlim_val n.+1)
}.

Canonical invlim_subType := [subType for invlim_val].
Definition invlim_choiceMixin := [choiceMixin of invlim by <:].
Canonical invlim_choiceType :=
  Eval hnf in ChoiceType invlim invlim_choiceMixin.
Definition invlim_poMixin := [poMixin of invlim by <:].
Canonical invlim_poType :=
  Eval hnf in PoType invlim invlim_poMixin.
Canonical invlim_subPoType := Eval hnf in [subPoType of invlim].
Canonical invlim_poChoiceType := Eval hnf in PoChoiceType invlim.

Lemma invlim_sup_clos : subCpo_axiom_of invlim_subPoType.
Proof.
move=> /= x n; set f := mono_comp mono_val' x.
rewrite /sup /= /dfun_sup -(valP (p n)) /=; congr sup.
apply: val_inj; apply: functional_extensionality=> m /=.
rewrite /flip /=; exact: (valP (x m)).
Qed.

Canonical invlim_subCpoType := SubCpoType invlim_sup_clos.
Definition invlim_cpoMixin := [cpoMixin of invlim by <:].
Canonical invlim_cpoType := Eval hnf in CpoType invlim invlim_cpoMixin.

Program Definition invlim_bot : invlim :=
  @InvLim (fun _ => ⊥) _.

Next Obligation.
move=> n /=; apply: appr_anti; first exact: botP.
rewrite -(embK (p n) ⊥); apply: monoP; exact: botP.
Qed.

Lemma invlim_botP x : invlim_bot ⊑ x.
Proof. move=> y; exact: botP. Qed.

Definition invlim_ppoMixin := PpoMixin invlim_botP.
Canonical invlim_ppoType := Eval hnf in PpoType (invlim p) invlim_ppoMixin.
Canonical invlim_pcpoType := Eval hnf in PcpoType (invlim p).

Lemma eq_invlim (x y : invlim) :
  (forall n, invlim_val x n = invlim_val y n) <-> x = y.
Proof.
split; last by move=> ->.
by move=> e; apply/val_inj/functional_extensionality_dep.
Qed.

Program Definition invlim_tuple
  (S : pcpoType)
  (f : forall n, pcpo_cont S (T n))
  (fP : forall n, f n = p n ∘ f n.+1) : pcpo_cont S invlim_pcpo :=
  Cont (Mono (fun x => @InvLim (fun n => f n x) _) _) _.

Next Obligation. by move=> S f fP x n; rewrite /= fP. Qed.
Next Obligation. move=> S f fP x y xy; move=> n /=; exact: monoP. Qed.
Next Obligation.
move=> S f fP x /=; apply/eq_invlim=> n /=; rewrite -contP; congr sup.
exact/eq_mono.
Qed.

Program Definition invlim_proj n : {cont invlim -> T n} :=
  Cont (Mono (fun x => invlim_val x n) (fun _ _ xy => xy n)) _.

Next Obligation. move=> n x /=; congr sup; exact/eq_mono. Qed.

Lemma invlim_proj_cone n : invlim_proj n = p n ∘ invlim_proj n.+1.
Proof. by apply/eq_cont; case=> [x xP] /=. Qed.

Lemma invlim_tupleK
  (S : cpoType)
  (f : forall n, {cont S -> T n})
  (fP : forall n, f n = p n ∘ f n.+1) n :
  invlim_proj n ∘ invlim_tuple fP = f n.
Proof. exact/eq_cont. Qed.

Lemma invlim_tupleL (S : cpoType) (f g : {cont S -> invlim}) :
  (forall n, invlim_proj n ∘ f ⊑ invlim_proj n ∘ g) -> f ⊑ g.
Proof. move=> fg x; move=> n; exact: (fg n x). Qed.

Lemma invlim_tupleP (S : cpoType) (f g : {cont S -> invlim}) :
  (forall n, invlim_proj n ∘ f = invlim_proj n ∘ g) -> f = g.
Proof.
move=> e; apply/eq_cont=> x; apply/eq_invlim=> n.
by move/(_ n)/eq_cont/(_ x): e=> /= ->.
Qed.

End InverseLimit.

Arguments InvLim {_ _} _ _.

*)

Module CpoCat.

Section ClassDef.

Set Primitive Projections.

Record mixin_of (C : catType@{u0 u1}) := Mixin {
  hom_base : forall X Y, Cpo.class_of (C X Y);
  comp_mono : forall X Y Z,
    @monotone [poType of Cpo.Pack (hom_base Y Z) *
                         Cpo.Pack (hom_base X Y)]
              (Cpo.Pack (hom_base X Z))
              (fun fg => fg.1 ∘ fg.2);
  comp_mono' : forall X Y Z,
    @monotone [poType of Cpo.Pack (hom_base Z Y) *
                         Cpo.Pack (hom_base Y X)]
              (Cpo.Pack (hom_base Z X))
              (fun fg => fg.2 ∘ fg.1);
  comp_cont : forall X Y Z, continuous (Mono _ (@comp_mono X Y Z));
  comp_cont' : forall X Y Z, continuous (Mono _ (@comp_mono' X Y Z))
}.

Program Definition pack_mixin (C  : catType@{u0 u1})
                 (cC : forall X Y, Cpo.class_of (C X Y))
                 (cm : forall X Y Z, @monotone [poType of Cpo.Pack (cC Y Z) *
                                                          Cpo.Pack (cC X Y)]
                                               (Cpo.Pack (cC X Z))
                                               (fun fg => fg.1 ∘ fg.2))
                 (cc : forall X Y Z, continuous (Mono _ (cm X Y Z))) :
  mixin_of C :=
  @Mixin C cC cm _ cc _.

Next Obligation.
move=> C cC cm cc X Y Z [/= g1 f1] [/= g2 f2] [/= g12 f12].
by apply: (cm Z Y X (f1, g1) (f2, g2)); split.
Qed.

Next Obligation.
move=> C cC cm cc X Y Z; move=> /= fg /=.
move: (cc Z Y X (⟨'π2, 'π1⟩ ∘ fg))=> /=.
rewrite !compA pairKL pairKR=> <-; apply: congr1; by apply/eq_mono.
Qed.

Record class_of (obj : Type1) (hom : obj -> obj -> Type0) := Class {
  base  : Cat.mixin_of@{u0 u1} hom;
  mixin : mixin_of (Cat.Pack@{u0 u1} base)
}.

Record type := Pack {obj; hom : obj -> obj -> Type0; class : class_of hom}.
Local Coercion obj : type >-> Sortclass.
Local Coercion hom : type >-> Funclass.
Local Coercion base : class_of >-> Cat.mixin_of.
Variables (C0 : Type1) (C1 : C0 -> C0 -> Type0) (cC : type).
Definition clone c of phant_id (class cC) c := @Pack C0 C1 c.

Definition catType := @Cat.Pack _ _ (class cC).

Definition pack :=
  [find c : Cat.type | @Cat.hom c ~ C1 | "not a catType" ]
  [find b : Cat.mixin_of _ | Cat.class c ~ b ]
  fun m => @Pack C0 C1 (@Class _ _ b m).

Unset Primitive Projections.

End ClassDef.

Module Exports.
Coercion obj : type >-> Sortclass.
Coercion hom : type >-> Funclass.
Coercion base : class_of >-> Cat.mixin_of.
Coercion catType : type >-> Cat.type.
Canonical catType.
Notation cpoCatType := type.
Notation CpoCatMixin := pack_mixin.
Notation CpoCatType C0 C1 m := (@pack C0 C1 _ unify _ unify m).
End Exports.

End CpoCat.

Export CpoCat.Exports.

Section CpoCatTheory.

Variable C : cpoCatType.

Implicit Types X Y Z W : C.

Canonical cpoCatHom_poType X Y :=
  PoType (C X Y) (CpoCat.hom_base (CpoCat.mixin (CpoCat.class C)) X Y).
Canonical cpoCatHom_choiceType X Y : choiceType :=
  ChoiceType (C X Y) (CpoCat.hom_base (CpoCat.mixin (CpoCat.class C)) X Y).
Canonical cpoCatHom_poChoiceType X Y :=
  Eval hnf in PoChoiceType (C X Y).
Canonical cpoCatHom_cpoType X Y :=
  Eval hnf in CpoType (C X Y) (Cpo.mixin (CpoCat.hom_base (CpoCat.mixin (CpoCat.class C)) X Y)).

Definition monotone_cpo_compp X Y Z :
  monotone (@compp C X Y Z) :=
  @CpoCat.comp_mono _ (CpoCat.mixin (CpoCat.class C)) X Y Z.

Canonical mono_cpo_compp X Y Z := Mono _ (@monotone_cpo_compp X Y Z).

Definition continuous_cpo_compp X Y Z :
  continuous (mono_cpo_compp X Y Z) :=
  @CpoCat.comp_cont _ (CpoCat.mixin (CpoCat.class C)) X Y Z.

Canonical cont_cpo_compp X Y Z := Cont _ (@continuous_cpo_compp X Y Z).

Lemma monotone_cpo_comp X Y Z (f1 f2 : C Y Z) (g1 g2 : C X Y) :
  f1 ⊑ f2 -> g1 ⊑ g2 -> f1 ∘ g1 ⊑ f2 ∘ g2.
Proof.
by move=> f12 g12; apply: monotone_cpo_compp; split.
Qed.

Lemma monotone_cpo_compL X Y Z (f1 f2 : C Y Z) (g : C X Y) :
  f1 ⊑ f2 -> f1 ∘ g ⊑ f2 ∘ g.
Proof. move=> f12; apply: monotone_cpo_comp f12 _; reflexivity. Qed.

Lemma monotone_cpo_compR X Y Z (f : C Y Z) (g1 g2 : C X Y) :
  g1 ⊑ g2 -> f ∘ g1 ⊑ f ∘ g2.
Proof. move=> g12; apply: monotone_cpo_comp _ g12; reflexivity. Qed.

Lemma continuous_cpo_compL X Y Z (f : {mono nat -> C Y Z}) (g : C X Y) :
  sup f ∘ g = sup (mono_cpo_compp _ _ _ ∘ ⟨f, mono_const _ g⟩).
Proof.
by case/continuous2P: (@continuous_cpo_compp X Y Z)=> [/(_ f g)].
Qed.

Lemma continuous_cpo_compR X Y Z (f : C Y Z) (g : {mono nat -> C X Y}) :
  f ∘ sup g = sup (mono_cpo_compp _ _ _ ∘ ⟨mono_const _ f, g⟩).
Proof.
by case/continuous2P: (@continuous_cpo_compp X Y Z)=> [_ /(_ f g)].
Qed.

Lemma continuous_cpo_comp X Y Z (f : chain (C Y Z)) (g : chain (C X Y)) :
  sup f ∘ sup g = sup (mono_cpo_compp _ _ _ ∘ ⟨f,g⟩).
Proof. by rewrite contP sup_pairf. Qed.

End CpoCatTheory.

Section CpoCpoCat.

Definition cpo_cpoCatMixin :=
  @CpoCatMixin cont_catType (fun T S => Cpo.class (cont_cpoType T S))
               monotone_cont_compp continuous_cont_compp.

Canonical cpo_cpoCatType :=
  Eval hnf in CpoCatType cpoType cont cpo_cpoCatMixin.

Definition pcpo_cpoCatMixin :=
  @CpoCatMixin pcpo_cont_catType (fun T S => Cpo.class (cont_cpoType T S))
               monotone_cont_compp continuous_cont_compp.

Canonical pcpo_cpoCatType :=
  Eval hnf in CpoCatType pcpoType pcpo_cont pcpo_cpoCatMixin.

Lemma pcpo_compE (T S R : pcpoType) :
  @comp pcpo_cpoCatType T S R = @comp cont_catType T S R.
Proof. by []. Qed.

End CpoCpoCat.

Section OppositeCpoCat.

Variable C : cpoCatType.

Definition op_cpoCatMixin :=
  @CpoCat.Mixin
    (op_catType C)
    (fun T S => CpoCat.hom_base (CpoCat.mixin (CpoCat.class C)) S T)
    (@CpoCat.comp_mono' _ (CpoCat.mixin (CpoCat.class C)))
    (@CpoCat.comp_mono  _ (CpoCat.mixin (CpoCat.class C)))
    (@CpoCat.comp_cont' _ (CpoCat.mixin (CpoCat.class C)))
    (@CpoCat.comp_cont  _ (CpoCat.mixin (CpoCat.class C))).

Canonical op_cpoCatType :=
  Eval hnf in CpoCatType (op C) (op_hom C) op_cpoCatMixin.

End OppositeCpoCat.

Section ProdCpoCat.

Variables C D : cpoCatType.

Program Definition prod_cat_cpoCatMixin :=
  @CpoCatMixin
    (prod_cat_catType C D)
    (fun T S => Cpo.class [cpoType of C T.1 S.1 * D T.2 S.2])
    _ _.

Next Obligation.
case=> /= [T1 T2] [S1 S2] [R1 R2].
case=> [[/= f1 g1] [/= f2 g2]] [[/= h1 k1] [/= h2 k2]].
case=> [[/= fh1 gk1] [/= fh2 gk2]]; split=> /=;
exact: monotone_cpo_comp.
Qed.

Next Obligation.
case=> /= [T1 T2] [S1 S2] [R1 R2]; apply/continuous2P; split=> /=.
- move=> fg [/= h k]; congr pair=> /=;
  by rewrite continuous_cpo_compL; congr sup; apply/eq_mono.
- move=> [/= f g] hk; congr pair=> /=;
  by rewrite continuous_cpo_compR; congr sup; apply/eq_mono.
Qed.

Canonical prod_cat_cpoCatType :=
  Eval hnf in CpoCatType (C * D) (@prod_cat_hom C D) prod_cat_cpoCatMixin.

End ProdCpoCat.

Section CpoFunctor.

Implicit Types C D E : cpoCatType.

Record cpo_functor C D := CpoFunctor {
  cpo_f_val :> {functor C -> D};
  cpo_monotone_fmap : forall X Y, monotone (@fmap _ _ cpo_f_val X Y);
  cpo_continuous_fmap : forall X Y, continuous (Mono _ (@cpo_monotone_fmap X Y))
}.

Lemma cpo_f_val_inj C D : injective (@cpo_f_val C D).
Proof.
case=> [/= F Fmono Fcont] [/= G Gmono Gcont] e.
move: Gmono Gcont; rewrite -{}e {G} => Gmono.
rewrite -(proof_irrelevance _ Fmono Gmono) => Gcont.
by rewrite -(proof_irrelevance _ Fcont Gcont).
Qed.

Canonical mono_fmap C D (F : cpo_functor C D) X Y :
  {mono C X Y -> D (F X) (F Y)} :=
  Mono _ (@cpo_monotone_fmap C D F X Y).

Canonical cont_fmap C D (F : cpo_functor C D) X Y :
  {cont C X Y -> D (F X) (F Y)} :=
  Cont (mono_fmap F X Y) (@cpo_continuous_fmap C D F X Y).

Definition cpo_functor_id C : cpo_functor C C :=
  @CpoFunctor _ _ 1
    (fun X Y => @monotone_id [poType of C X Y])
    (fun X Y => @continuous_id [cpoType of C X Y]).

Definition cpo_functor_comp C D E (F : cpo_functor D E) (G : cpo_functor C D) :
  cpo_functor C E :=
  @CpoFunctor _ _ (cpo_f_val F ∘ cpo_f_val G)
    (fun X Y => monotone_comp (@cpo_monotone_fmap _ _ F _ _) (@cpo_monotone_fmap _ _ G X Y))
    (fun X Y => continuous_comp (@cpo_continuous_fmap _ _ F _ _) (@cpo_continuous_fmap _ _ G X Y)).

Lemma cpo_functor_compP : Cat.axioms cpo_functor_comp cpo_functor_id.
Proof.
by split=> *; apply: cpo_f_val_inj; rewrite /= ?comp1f ?compf1 ?compA.
Qed.

Definition cpo_functor_catMixin := CatMixin cpo_functor_compP.

Canonical cpo_functor_catType :=
  Eval hnf in CatType cpoCatType cpo_functor cpo_functor_catMixin.

End CpoFunctor.

Definition cpo_functor_of (C D : cpoCatType) (p : phant (C -> D)) :=
  cpo_functor C D.

Notation "{ 'cpo_functor' T }" := (@cpo_functor_of _ _ (Phant T))
  (at level 0, format "{ 'cpo_functor'  T }") : type_scope.

Arguments CpoFunctor {_ _} _ _ _.

Section CpoCatTermCat.

Definition cpoCat_term_cpoCatMixin :=
  @CpoCatMixin
    cat_term
    (fun _ _ => Cpo.class [cpoType of unit])
    (fun _ _ _ _ _ _ => I)
    (fun _ _ _ _ => erefl).

Canonical cpoCat_term :=
  CpoCatType unit (@indisc_hom unit) cpoCat_term_cpoCatMixin.

Definition cpoCat_bang (C : cpoCatType) : {cpo_functor C -> unit} :=
  CpoFunctor '! (fun _ _ _ _ _ => I) (fun _ _ _ => erefl).

Lemma cpoCat_bangP (C : cpoCatType) (F : {cpo_functor C -> unit}) :
  F = cpoCat_bang _.
Proof. exact/cpo_f_val_inj/bangP. Qed.

Definition cpoCat_termCatMixin := TermCatMixin cpoCat_bangP.
Canonical cpoCat_termCatType :=
  Eval hnf in TermCatType cpoCatType cpo_functor cpoCat_termCatMixin.

End CpoCatTermCat.

Section CpoCatProdCat.

Definition cpoCat_proj1 (C D : cpoCatType) : {cpo_functor C * D -> C} :=
  CpoFunctor 'π1 (fun X Y => @monotone_fst _ _) (fun X Y => @continuous_fst _ _).

Definition cpoCat_proj2 (C D : cpoCatType) : {cpo_functor C * D -> D} :=
  CpoFunctor 'π2 (fun X Y => @monotone_snd _ _) (fun X Y => @continuous_snd _ _).

Definition cpoCat_pair
           (C D E : cpoCatType)
           (F : {cpo_functor E -> C})
           (G : {cpo_functor E -> D}) : {cpo_functor E -> C * D} :=
  CpoFunctor ⟨cpo_f_val F, cpo_f_val G⟩
             (fun X Y => @monotone_pairf
                           _ _ _
                           (Mono _ (@cpo_monotone_fmap _ _ F _ _))
                           (Mono _ (@cpo_monotone_fmap _ _ G _ _)))
             (fun X Y => @continuous_pairf
                           _ _ _
                           (Cont _ (@cpo_continuous_fmap _ _ F _ _))
                           (Cont _ (@cpo_continuous_fmap _ _ G _ _))).

Lemma cpoCat_pairP : ProdCat.axioms_of cpoCat_pair cpoCat_proj1 cpoCat_proj2.
Proof.
split.
- move=> /= C D E F G; apply/cpo_f_val_inj=> /=; exact: pairKL.
- move=> /= C D E F G; apply/cpo_f_val_inj=> /=; exact: pairKR.
- move=> /= C D E F G.
  case=> /(congr1 (@cpo_f_val _ _))/= H1 /(congr1 (@cpo_f_val _ _))/= H2.
  by apply/cpo_f_val_inj/pairP; split.
Qed.

Definition cpoCat_prodCatMixin := ProdCatMixin cpoCat_pairP.
Canonical cpoCat_prodCatType :=
  Eval hnf in ProdCatType cpoCatType cpo_functor cpoCat_prodCatMixin.

End CpoCatProdCat.

Canonical cpoCat_cartCatType :=
  Eval hnf in CartCatType cpoCatType cpo_functor.

Definition cpoCat_consts (C : cpoCatType) := CpoCat.obj C.

Program Definition cpoCat_of_consts (C : cpoCatType) (X : cpoCat_consts C) :
  {cpo_functor unit -> C} :=
  CpoFunctor (@of_const _ (CpoCat.catType C) X)
             (fun _ _ _ _ _ => appr_refl _) _.

Next Obligation.
move=> /= C X [] []; move=> /= x; apply: (etrans _ (sup_const _)).
by congr sup; apply/eq_mono.
Qed.

Definition cpoCat_constCatMixin := ConstCatMixin cpoCat_of_consts.

Canonical cpoCat_constCatType :=
  Eval hnf in ConstCatType cpoCatType cpo_functor cpoCat_constCatMixin.

Program Definition subsing_cpo_functor : {cpo_functor cpoType -> pcpoType} :=
  CpoFunctor subsing_functor _ _.

Next Obligation.
move=> /= T S; move=> /= f g fg; apply: monoP.
by apply: monotone_cpo_compp; split=> //; reflexivity.
Qed.

Next Obligation.
move=> /= T S; move=> /= x.
rewrite continuous_cont_compR -contP; congr sup.
by apply/eq_mono.
Qed.

Definition cpo_of_pcpo_functor : {functor pcpoType -> cpoType} :=
  Functor Pcpo.cpoType (fun _ _ f => f)
          (fun _ => erefl) (fun _ _ _ _ _ => erefl).

Definition cpo_of_pcpo_cpo_functor : {cpo_functor pcpoType -> cpoType} :=
  CpoFunctor cpo_of_pcpo_functor
             (fun _ _ => @monotone_id _)
             (fun _ _ => @continuous_id _).

Definition op_cpo_functor (C D : cpoCatType) (F : {cpo_functor C -> D})
  : {cpo_functor op C -> op D} :=
  CpoFunctor (op_functor F)
             (fun _ _ => @cpo_monotone_fmap _ _ F _ _)
             (fun _ _ => @cpo_continuous_fmap _ _ F _ _).

(* TODO: These proof obligations might be discharged by showing that products
   and exponentials can be enriched in any CCC (cf. icomp above). *)

Program Definition prod_cpo_functor : {cpo_functor cpoType * cpoType -> cpoType} :=
  CpoFunctor (prod_functor _) _ _.

Next Obligation.
move=> [/= T1 T2] [/= S1 S2].
by move=> [/= f1 f2] [/= g1 g2] [/= fg1 fg2]; split=> /=; eauto.
Qed.

Next Obligation.
move=> [/= T1 T2] [/= S1 S2]; apply/continuous2P; split.
- move=> /= f g; apply/eq_cont=> - [/= x y]; congr pair=> /=.
  + by congr sup; apply/eq_mono.
  + by rewrite -[LHS]sup_const; congr sup; apply/eq_mono.
- move=> /= f g; apply/eq_cont=> - [/= x y]; congr pair=> /=.
  + by rewrite -[LHS]sup_const; congr sup; apply/eq_mono.
  + by congr sup; apply/eq_mono.
Qed.

Program Definition pcont_functor :
  {functor op cpoType * pcpoType -> pcpoType} :=
  Functor (fun T => cont_pcpoType T.1 T.2)
          (fun T S => @fmap _ _ (exp_functor cont_ccCatType) (T.1, T.2) (S.1, S.2))
          (fun T => @fmap1 _ _ (exp_functor cont_ccCatType) (T.1, T.2))
          (fun T S R => @fmapD _ _ (exp_functor cont_ccCatType)
                               (T.1, T.2) (S.1, S.2) (R.1, R.2)).

Program Definition pcont_cpo_functor :
  {cpo_functor op cpoType * pcpoType -> pcpoType} :=
  CpoFunctor pcont_functor _ _.

Next Obligation.
move=> [/= T1 T2] [/= S1 S2].
move=> [/= f1 f2] [/= g1 g2] [/= fg1 fg2].
move=> h /=; move=> x /=.
apply: transitivity (fg2 _).
apply: monoP.
apply: monoP.
apply: fg1.
Qed.

Next Obligation.
move=> [/= T1 T2] [/= S1 S2].
apply/continuous2P; split.
- move=> /= f g; apply/eq_cont=> /= h; apply/eq_cont=> x /=.
  rewrite {1}/sup /= /dfun_sup.
  by rewrite -2!contP; congr sup; apply/eq_mono=> n.
- move=> /= f g; apply/eq_cont=> /= h; apply/eq_cont=> x /=.
  by congr sup; apply/eq_mono=> n.
Qed.

Section Retractions.

Variable C : cpoCatType.

Definition retraction (T S : C) (r : C T S) (e : C S T) :=
  r ∘ e = 1 /\ e ∘ r ⊑ 1.

Record retr (T S : C) := Retr {
  retr_val :> C T S * C S T;
  _        :  retraction retr_val.1 retr_val.2
}.

Canonical retr_subType (T S : C) :=
  [subType for @retr_val T S].
Definition retr_choiceMixin (T S : C) :=
  [choiceMixin of retr T S by <:].
Canonical retr_choiceType (T S : C) :=
  Eval hnf in ChoiceType (retr T S) (retr_choiceMixin T S).

Lemma embedding_unique (T S : C) (r : C T S) (e1 e2 : C S T) :
  retraction r e1 -> retraction r e2 -> e1 = e2.
Proof.
move=> e1P e2P; apply: appr_anti.
- rewrite -[e1]compf1 -[e2]comp1f -(proj1 e2P) compA.
  exact: monotone_cpo_compL (proj2 e1P).
- rewrite -[e2]compf1 -[e1]comp1f -(proj1 e1P) compA.
  apply: monotone_cpo_compL (proj2 e2P).
Qed.

Lemma retrP (T S : C) (r : retr T S) : retraction r.1 r.2.
Proof. exact: (valP r). Qed.

Lemma retr_retr_inj (T S : C) (r1 r2 : retr T S) : r1.1 = r2.1 -> r1 = r2.
Proof.
move=> e; apply: val_inj; case: r1 r2 e=> [[r1 e1] /= e1P] [[r2 e2] /= e2P] e.
by rewrite -e in e1P e2P *; rewrite (embedding_unique e1P e2P).
Qed.

Implicit Types T S R U : C.

Lemma embK T S (r : retr T S) : r.1 ∘ r.2 = 1.
Proof. exact: (proj1 (retrP r)). Qed.

Lemma retr1 T S (r : retr T S) : r.2 ∘ r.1 ⊑ 1.
Proof. exact: (proj2 (retrP r)). Qed.

Lemma retrA (T S R : C) (r : retr T S) (f : C R S) (g : C R T) :
  f ⊑ r.1 ∘ g <-> r.2 ∘ f ⊑ g.
Proof.
split.
- move=> /(monotone_cpo_compR r.2) e; apply: transitivity e _.
  rewrite -{2}(comp1f g) compA; apply: monotone_cpo_compL.
  exact: retr1.
- by move=> /(monotone_cpo_compR r.1); rewrite compA embK comp1f.
Qed.

Lemma emb_iso (T S R : C) (r : retr T S) (f g : C R S) :
  r.2 ∘ f ⊑ r.2 ∘ g <-> f ⊑ g.
Proof.
split; last exact: monotone_cpo_compR.
by move=> /(monotone_cpo_compR r.1); rewrite !compA embK !comp1f.
Qed.

Lemma comp_emb_inj (T S R : C) (r : retr T S) (f g : C R S) :
  r.2 ∘ f = r.2 ∘ g -> f = g.
Proof.
move=> e; apply: appr_anti; apply/(emb_iso r); rewrite e; reflexivity.
Qed.

Lemma retraction_id T : retraction (cat_id T) (cat_id T).
Proof. by split; rewrite comp1f //; reflexivity. Qed.

Definition retr_id T : retr T T :=
  Eval hnf in Sub (cat_id T, cat_id T) (retraction_id T).

Lemma retraction_comp T S R (r1 : retr S R) (r2 : retr T S) :
  retraction (r1.1 ∘ r2.1) (r2.2 ∘ r1.2).
Proof.
split; first by rewrite compA -(compA r1.1) embK compf1 embK.
apply: transitivity (retr1 r2).
rewrite -[in X in _ ⊑ X](compf1 r2.2) compA -(compA r2.2).
apply: monotone_cpo_compL; apply: monotone_cpo_compR; exact: retr1.
Qed.

Definition retr_comp T S R (r1 : retr S R) (r2 : retr T S) : retr T R :=
  @Retr _ _ (r1.1 ∘ r2.1, r2.2 ∘ r1.2) (retraction_comp r1 r2).

Lemma retr_compP : Cat.axioms retr_comp retr_id.
Proof.
split.
- by move=> T S f; apply: val_inj; rewrite /= compf1 comp1f.
- by move=> T S f; apply: val_inj; rewrite /= compf1 comp1f.
- by move=> T S R U f g h; apply: val_inj; rewrite /= !compA.
Qed.

Definition retr_catMixin := CatMixin retr_compP.
Canonical retr_catType := Eval hnf in CatType C retr retr_catMixin.

Lemma retrD T S R (r1 : retr S R) (r2 : retr T S) : (r1 ∘ r2).1 = r1.1 ∘ r2.1.
Proof. by []. Qed.

Lemma embD T S R (r1 : retr S R) (r2 : retr T S) : (r1 ∘ r2).2 = r2.2 ∘ r1.2.
Proof. by []. Qed.

Program Definition retr_functor : {functor retr_catType -> C} :=
  Functor id (fun _ _ => fst) (fun _ => erefl) (fun _ _ _ _ _ => erefl).

Program Definition emb_functor : {functor retr_catType -> op C} :=
  Functor id (fun _ _ => snd) (fun _ => erefl) (fun _ _ _ _ _ => erefl).

End Retractions.

Arguments Retr {_ _ _} _ _.
Arguments retr_id {_}.

Program Definition retr_cat_functor : {functor cpoCatType -> catType} :=
  Functor
    retr_catType
    (fun C D F => Functor F
                          (fun X Y f => Retr (fmap F (val f).1,
                                              fmap F (val f).2) _) _ _) _ _.

Next Obligation.
move=> /= C D F X Y r; split; first by rewrite -fmapD embK fmap1.
rewrite -(fmap1 F) -fmapD; apply: monoP; exact: retr1.
Qed.

Next Obligation.
by move=> /= C D F X; apply: retr_retr_inj; rewrite /= fmap1.
Qed.

Next Obligation.
by move=> /= C D F X Y Z f g; apply: retr_retr_inj; rewrite /= fmapD.
Qed.

Next Obligation.
move=> /= C; apply/eq_functor=> /=; congr Tagged.
apply/functional_extensionality_dep=> X.
apply/functional_extensionality_dep=> Y.
apply/functional_extensionality=> r.
exact: val_inj.
Qed.

Next Obligation.
move=> /= C D E F G.
apply/eq_functor; congr Tagged=> /=.
apply/functional_extensionality_dep=> X.
apply/functional_extensionality_dep=> Y.
apply/functional_extensionality=> f.
exact: val_inj.
Qed.

Program Definition retr_prod (C D : cpoCatType) :
  iso (retr_catType (C × D))
      (retr_catType C × retr_catType D) :=
  @Iso _ _ _
       (Functor id (fun X Y f => (Retr (f.1.1, f.2.1) _, Retr (f.1.2, f.2.2) _)) _ _)
       (Functor id (fun X Y f => Retr ((f.1.1, f.2.1), (f.1.2, f.2.2)) _) _ _) _ _.

Next Obligation.
move=> /= C D X Y f; split; first by case: (embK f).
by case: (retr1 f).
Qed.

Next Obligation.
move=> /= C D X Y f; split; first by case: (embK f).
by case: (retr1 f).
Qed.

Next Obligation.
by move=> /= C D X; congr pair; apply/retr_retr_inj.
Qed.

Next Obligation.
by move=> /= C D X Y Z f g; congr pair; apply/retr_retr_inj.
Qed.

Next Obligation.
move=> /= C D X Y f; split; rewrite prod_cat_compE /= ?embK //.
split; exact: retr1.
Qed.

Next Obligation.
by move=> /= C D X; apply/retr_retr_inj.
Qed.

Next Obligation.
by move=> /= C D X Y Z f g; apply/retr_retr_inj; rewrite /= prod_cat_compE /=.
Qed.

Next Obligation.
move=> C D; apply/eq_functor; congr Tagged=> /=.
apply/functional_extensionality_dep=> X.
apply/functional_extensionality_dep=> Y.
apply/functional_extensionality=> f.
by apply/retr_retr_inj.
Qed.

Next Obligation.
move=> C D; apply/eq_functor; congr Tagged=> /=.
apply/functional_extensionality_dep=> X.
apply/functional_extensionality_dep=> Y.
apply/functional_extensionality=> f.
congr pair; by apply/retr_retr_inj.
Qed.

Program Definition retr_op (C : cpoCatType) :
  iso (retr_catType C)
      (retr_catType (op_cpoCatType C)) :=
  @Iso _ _ _
    (Functor id (fun X Y f => Retr (f.2, f.1) _) _ _)
    (Functor id (fun X Y f => Retr (f.2, f.1) _) _ _) _ _.

Next Obligation.
move=> /= C X Y f; split; rewrite op_compE /of_op ?embK //.
exact: retr1.
Qed.

Next Obligation.
move=> /= C X; exact: retr_retr_inj.
Qed.

Next Obligation.
by move=> /= C X Y Z f g; apply: retr_retr_inj.
Qed.

Next Obligation.
move=> /= C X Y f; split; first exact: (embK f).
exact: (retr1 f).
Qed.

Next Obligation.
by move=> /= C X; apply: retr_retr_inj.
Qed.

Next Obligation.
by move=> /= C X Y Z f g; apply: retr_retr_inj.
Qed.

Next Obligation.
move=> /= C; apply/eq_functor; congr Tagged=> /=.
by do 3![apply/functional_extensionality_dep=> ?]; apply: retr_retr_inj.
Qed.

Next Obligation.
move=> /= C; apply/eq_functor; congr Tagged=> /=.
by do 3![apply/functional_extensionality_dep=> ?]; apply: retr_retr_inj.
Qed.

Section Projections.

Variable C : cpoCatType.
Variable T : C.

Definition projection (p : C T T) :=
  p ⊑ 1 /\ p ∘ p = p.

Record proj := Proj {
  proj_val :> C T T;
  _        :  projection proj_val
}.

Implicit Types p q s : proj.

Canonical proj_subType := [subType for proj_val].
Definition proj_choiceMixin :=
  [choiceMixin of proj by <:].
Canonical proj_choiceType :=
  Eval hnf in ChoiceType proj proj_choiceMixin.

Definition projP p : projection p := valP p.

Lemma projI p : proj_val p ∘ proj_val p = proj_val p.
Proof. exact: (proj2 (projP p)). Qed.

Lemma proj_appr1 p : proj_val p ⊑ 1.
Proof. exact: (proj1 (projP p)). Qed.

(* FIXME: This can be simplified to qpq = p *)
Definition proj_appr p q : Prop :=
  proj_val p ∘ proj_val q = proj_val p /\
  proj_val q ∘ proj_val p = proj_val p.

Lemma proj_apprP : Po.axioms proj_appr.
Proof.
split.
- by move=> p; split; case: (projP p).
- move=> p q s [pq qp] [qs sq]; split.
  + by rewrite -{1}pq -compA qs pq.
  + by rewrite -{1}qp  compA sq qp.
- by move=> p q [pq _] [_ pq']; apply/val_inj; rewrite /= -[LHS]pq -[RHS]pq'.
Qed.

Definition proj_poMixin := PoMixin proj_apprP.
Canonical proj_poType := Eval hnf in PoType proj proj_poMixin.
Canonical proj_poChoiceType := Eval hnf in PoChoiceType proj.

Lemma proj_apprE p q :
  p ⊑ q <-> proj_val q ∘ proj_val p ∘ proj_val q = proj_val p.
Proof.
split; first by case=> [pq ->].
by move=> e; split; rewrite -e -!compA ?projI // !compA projI.
Qed.

Lemma monotone_proj_val : monotone proj_val.
Proof.
move=> p q [<- qp]; rewrite -{2}[proj_val q]comp1f.
apply: monotone_cpo_compL; exact: proj_appr1.
Qed.

Definition mono_proj_val : {mono proj -> C T T} :=
  Mono proj_val monotone_proj_val.
Canonical mono_proj_val.

Program Definition proj_sup (p : chain proj) : proj :=
  Sub (sup (mono_proj_val ∘ p)) _.

Next Obligation.
move=> p; split.
- have [_ least_p] := supP (mono_proj_val ∘ p); apply: least_p.
  move=> n; exact: proj_appr1.
- rewrite continuous_cpo_comp; congr sup; apply/eq_mono=> n /=.
  by rewrite -[RHS]projI.
Qed.

Lemma proj_supP (p : chain proj) : supremum p (proj_sup p).
Proof.
rewrite /proj_sup; split.
- move=> n; split=> /=.
  + rewrite continuous_cpo_compR -(sup_shift _ n) -[RHS]sup_const.
    congr sup; apply/eq_mono=> m /=; rewrite /constfun.
    by have [e _] := monoP p (leq_addr m n); rewrite -[RHS]e.
  + rewrite continuous_cpo_compL -(sup_shift _ n) -[RHS]sup_const.
    congr sup; apply/eq_mono=> m /=; rewrite /constfun.
    by have [_ e] := monoP p (leq_addr m n); rewrite -[RHS]e.
- move=> q ub_q; split=> /=.
  + rewrite continuous_cpo_compL; congr sup; apply/eq_mono=> n /=.
    by have [e _] := ub_q n; rewrite -[RHS]e.
  + rewrite continuous_cpo_compR; congr sup; apply/eq_mono=> n /=.
    by have [_ e] := ub_q n; rewrite -[RHS]e.
Qed.

Definition proj_cpoMixin := CpoMixin proj_supP.
Canonical proj_cpoType := Eval hnf in CpoType proj proj_cpoMixin.

Program Definition proj_top : proj := @Proj 1 _.
Next Obligation. by split; [reflexivity|rewrite comp1f]. Qed.

Lemma proj_topP p : p ⊑ proj_top.
Proof. by split; rewrite ?comp1f ?compf1. Qed.

Program Definition proj_of_retr (S : C) (r : retr T S) : proj :=
  @Proj (r.2 ∘ r.1) _.

Next Obligation.
move=> S r; split; first exact: retr1.
by rewrite compA -(compA r.2) (embK r) compf1.
Qed.

Lemma proj_of_retr_comp (S R : C) (r1 : retr S R) r2 :
  proj_of_retr (r1 ∘ r2) ⊑ proj_of_retr r2.
Proof.
split=> /=.
- by rewrite -!compA (compA _ r2.2 _) embK comp1f.
- by rewrite !compA -(compA _ _ r2.2) embK compf1.
Qed.

Program Definition mono_proj_of_retr
  (S : nat -> C)
  (rS : forall n, retr (S n.+1) (S n))
  (rT : forall n, retr T (S n))
  (rP : forall n, rT n = rS n ∘ rT n.+1) : chain proj :=
  Mono (fun n => proj_of_retr (rT n)) _.

Next Obligation.
move=> S rS rT rP n m nm; rewrite (down_coneP rP nm); exact: proj_of_retr_comp.
Qed.

(*Section RetrOfProj.

Variable p : proj.

Record rop := ROP {
  rop_val : T;
  _       : exists x, p x = rop_val
}.

Lemma ropP (x : rop) : p (rop_val x) = rop_val x.
Proof.
by case: x=> [x [x' xP]] /=; rewrite -xP -[in RHS](proj2 (projP p)).
Qed.

Canonical rop_subType := [subType for rop_val].
Definition rop_choiceMixin := [choiceMixin of rop by <:].
Canonical rop_choiceType := Eval hnf in ChoiceType rop rop_choiceMixin.
Definition rop_poMixin := [poMixin of rop by <:].
Canonical rop_poType := Eval hnf in PoType rop rop_poMixin.
Canonical rop_subPoType := [subPoType of rop].
Canonical rop_poChoiceType := Eval hnf in PoChoiceType rop.

Lemma rop_sup_clos : subCpo_axiom_of rop_subPoType.
Proof.
move=> /= x; exists (sup (mono_val' ∘ x)).
by rewrite -contP; congr sup; apply/eq_mono=> n /=; rewrite ropP.
Qed.

Canonical rop_subCpoType := Eval hnf in SubCpoType rop_sup_clos.
Definition rop_cpoMixin := [cpoMixin of rop by <:].
Canonical rop_cpoType := Eval hnf in CpoType rop rop_cpoMixin.

Program Definition retr_of_proj : {retr T -> rop} :=
  @Retr _ _ (Cont (Mono (fun x => Sub (p x) _) _) _, cont_val') _.

Next Obligation. by simpl; eauto. Qed.
Next Obligation. move=> x1 x2 /(monoP p); exact. Qed.
Next Obligation.
by move=> x; apply/val_inj; rewrite /= -contP; congr sup; apply/eq_mono.
Qed.
Next Obligation.
split; first by apply/eq_cont=> x /=; apply/val_inj; exact: ropP.
move=> x /=; exact: (proj1 (projP p)).
Qed.

End RetrOfProj.

Lemma retr_of_projK p : proj_of_retr (retr_of_proj p) = p.
Proof. exact/eq_proj. Qed.
*)

End Projections.

Arguments Proj {_} _ _.
Arguments proj_val {_ _}.
Arguments proj_top {_ _}.

Definition cone_proj_of_retr
  (C : cpoCatType) (X : {functor op nat -> retr_catType C}) (Y : cone X) :
  chain (proj (cone_tip Y)) :=
  @mono_proj_of_retr
    C (cone_tip Y) X
    (fun n => fmap X (leqnSn n))
    (cone_proj Y)
    (fun n => coneP Y (leqnSn n)).

Section PointedProj.

Variable T : pcpoType.

Program Definition proj_bot : @proj pcpo_cpoCatType T := Proj _ (@cont_const T T ⊥) _.
Next Obligation. split; [exact/botP|exact/eq_cont]. Qed.

Lemma proj_botP p : proj_bot ⊑ p.
Proof.
split; first exact/eq_cont.
apply/eq_cont=> x /=; rewrite /constfun.
apply/appr_anti; last exact: botP.
exact: (proj1 (projP p)).
Qed.

Definition proj_ppoMixin := PpoMixin proj_botP.
Canonical proj_ppoType := Eval hnf in PpoType (@proj pcpo_cpoCatType T) proj_ppoMixin.
Canonical proj_pcpoType := Eval hnf in PcpoType (@proj pcpo_cpoCatType T).

End PointedProj.

Record cont_functor (C D : cpoCatType) := ContFunctor {
  cont_f_val  :> {functor retr_catType C -> retr_catType D};
  cont_f_valP :
    forall (X : nat -> C) (f : forall n, @retr C (X n.+1) (X n))
           Y (g : forall n, @retr C Y (X n)) (gP : forall n, g n = f n ∘ g n.+1),
      sup (mono_proj_of_retr gP) = proj_top ->
      sup (mono_proj_of_retr (down_comp_cone gP cont_f_val)) = proj_top
}.
Arguments ContFunctor {_ _} _ _.
Arguments cont_f_val {_ _}.

Lemma cont_f_val_inj C D : injective (@cont_f_val C D).
Proof.
case=> [F FP] [G GP] /= e.
move: FP GP; rewrite -e=> FP GP.
by rewrite (proof_irrelevance _ FP GP).
Qed.

Program Definition cont_functor_id (C : cpoCatType) : cont_functor C C :=
  @ContFunctor C C 1 _.

Next Obligation.
by move=> /= C X f Y g gP <-; congr sup; apply/eq_mono.
Qed.

Program Definition cont_functor_comp
  (C D E : cpoCatType)
  (F : cont_functor D E) (G : cont_functor C D) :
  cont_functor C E :=
  ContFunctor (cont_f_val F ∘ cont_f_val G) _.

Next Obligation.
move=> C D E F G X f Y g gP e.
rewrite -(cont_f_valP F (cont_f_valP G e)).
by congr sup; apply/eq_mono.
Qed.

Lemma cont_functor_compP : Cat.axioms cont_functor_comp cont_functor_id.
Proof.
split.
- by move=> C D F; apply/cont_f_val_inj=> /=; rewrite comp1f.
- by move=> C D F; apply/cont_f_val_inj=> /=; rewrite compf1.
- by move=> B C D E F G H; apply/cont_f_val_inj=> /=; rewrite compA.
Qed.

Definition cont_functor_catMixin := CatMixin cont_functor_compP.
Canonical cont_functor_catType :=
  Eval hnf in CatType cpoCatType cont_functor cont_functor_catMixin.

Program Definition cont_functor_termCatMixin :=
  @TermCatMixin
    cpoCatType cont_functor (@term cpoCat_termCatType)
    (fun X => @ContFunctor X _ (Functor (fun _ => tt) (fun A B f => 1) _ _) _) _.

Next Obligation. by []. Qed.
Next Obligation. by move=> *; rewrite compf1. Qed.
Next Obligation.
move=> C X f Y g gP _; rewrite -[RHS]sup_const.
congr sup; apply/eq_mono=> /= x.
by apply/val_inj=> /=; rewrite comp1f.
Qed.
Next Obligation.
move=> C F; apply/cont_f_val_inj=> /=.
apply/eq_functor=> /=.
case: F=> [/= F _].
case: F=> [/= Fobj Fmap _ _].
move: Fmap; have {Fobj} -> : Fobj = fun x => tt.
  by apply/functional_extensionality=> x; case: (Fobj _).
move=> Fmap; congr Tagged.
apply/functional_extensionality_dep=> X.
apply/functional_extensionality_dep=> Y.
apply/functional_extensionality=> f.
by case: (Fmap X Y f)=> [[[] []] r]; apply/val_inj.
Qed.

(* FIXME: Coq gets confused because TermCatType infers the catType structure
   using objects instead of arrows, and we have already declared the category of
   cpo functors as canonical. *)

Canonical cont_functor_termCatType :=
  @TermCat.Pack cpoCatType cont_functor
    (TermCat.Class cont_functor_catMixin cont_functor_termCatMixin).

Program Definition cont_functor_prodCatMixin :=
  @ProdCatMixin
    cont_functor_catType prod_cat_cpoCatType
    (fun C D E F G =>
       ContFunctor
         (Functor (fun X => (F X, G X))
                  (fun X Y f =>
                     Retr (((fmap F f).1, (fmap G f).1),
                           ((fmap F f).2, (fmap G f).2))
                          _)
                  _ _)
         _)
    (fun C D => ContFunctor (fmap retr_cat_functor 'π1) _)
    (fun C D => ContFunctor (fmap retr_cat_functor 'π2) _)
    _.

Next Obligation.
move=> C D E F G X Y f; split; rewrite prod_cat_compE /= ?embK //.
split; exact/retr1.
Qed.

Next Obligation.
by move=> C D E F G X; apply/retr_retr_inj; rewrite /= !fmap1.
Qed.

Next Obligation.
move=> C D E F G X Y Z f g; apply/retr_retr_inj; rewrite /=.
by rewrite !fmapD !retrD.
Qed.

Next Obligation.
move=> C D E F G X f Y g gP e.
have /(congr1 proj_val) /= eF := cont_f_valP F e.
have /(congr1 proj_val) /= eG := cont_f_valP G e.
apply/val_inj=> /=.
rewrite [in RHS]/cat_id /=; unfold prod_cat_id; rewrite -eF -eG.
by congr (sup _, sup _); apply/eq_mono.
Qed.

Next Obligation.
move=> C D X f Y g gP /(congr1 proj_val) /= [e1 e2].
by apply/val_inj; rewrite /= -e1; congr sup; apply/eq_mono.
Qed.

Next Obligation.
move=> C D X f Y g gP /(congr1 proj_val) /= [e1 e2].
by apply/val_inj; rewrite /= -e2; congr sup; apply/eq_mono.
Qed.

Next Obligation.
split.
- move=> C D E F G; apply/cont_f_val_inj; rewrite /=.
  apply/eq_functor; congr Tagged.
  do 3![apply/functional_extensionality_dep=> ? /=].
  exact/retr_retr_inj.
- move=> C D E F G; apply/cont_f_val_inj; rewrite /=.
  apply/eq_functor; congr Tagged.
  do 3![apply/functional_extensionality_dep=> ? /=].
  exact/retr_retr_inj.
- move=> /= C D E [F FP] [G GP]
            [/(congr1 cont_f_val)/eq_functor /= eF
             /(congr1 cont_f_val)/eq_functor /= eG].
  apply/cont_f_val_inj/eq_functor; rewrite /=.
  case: F G eF eG {FP GP}=> [Fobj Fmap _ _] [Gobj Gmap _ _] /= eF eG.
  have eobj : Fobj = Gobj.
    apply/functional_extensionality=> X.
    move: (congr1 tag eF) (congr1 tag eG)=> /=.
    move=> /(congr1 (fun H => H X)) eobj1 /(congr1 (fun H => H X)) eobj2.
    by case: (Fobj X) (Gobj X) eobj1 eobj2 => [??] [??] /= -> ->.
  move: Gmap eF eG; rewrite -{}eobj=> {Gobj} Gmap e1 e2.
  have := eq_tagged e1.
  rewrite /= (proof_irrelevance _ (congr1 tag e1) erefl) /= => {e1} e1.
  have := eq_tagged e2.
  rewrite /= (proof_irrelevance _ (congr1 tag e2) erefl) /= => {e2} e2.
  congr Tagged.
  apply/functional_extensionality_dep=> X.
  apply/functional_extensionality_dep=> Y.
  apply/functional_extensionality_dep=> r.
  move: e1 e2=> /(congr1 (fun H => val (H X Y r))) /= [e11 e12].
  move=>        /(congr1 (fun H => val (H X Y r))) /= [e21 e22].
  apply/retr_retr_inj.
  by case: (Fmap X Y r).1 (Gmap X Y r).1 e11 e21=> [??] [??] /= -> ->.
Qed.

Canonical cont_functor_prodCatType :=
  @ProdCat.Pack
    cpoCatType cont_functor
    (ProdCat.Class cont_functor_prodCatMixin).

Canonical cont_functor_cartCatType :=
  @CartCat.Pack
    cpoCatType cont_functor
    (CartCat.Class cont_functor_termCatMixin cont_functor_prodCatMixin).

(* Promote a CPO-functor to a continuous functor.  This could be made into
   a functor, but we won't need the additional structure. *)

Program Definition cont_of_cpo_functor
  (C D : cpoCatType) (F : {cpo_functor C -> D}) : cont_functor C D :=
  ContFunctor (Functor F (fun X Y f => Retr (fmap F f.1, fmap F f.2) _) _ _) _.

Next Obligation.
move=> C D F X Y f; split; rewrite /= -fmapD ?embK ?fmap1 //.
rewrite -fmap1; apply: monoP; exact/retr1.
Qed.

Next Obligation.
by move=> C D F X; apply/retr_retr_inj; rewrite /= fmap1.
Qed.

Next Obligation.
by move=> C D F X Y Z f g; apply/retr_retr_inj; rewrite /= fmapD.
Qed.

Next Obligation.
move=> C D F X f Y g gP /(congr1 (fmap F \o proj_val)) /=.
rewrite -contP fmap1 => e; apply/val_inj=> /=.
by rewrite -e; congr sup; apply/eq_mono=> n /=; rewrite fmapD.
Qed.

Program Definition cont_functor_op C : cont_functor C (op_cpoCatType C) :=
  ContFunctor (iso1 (retr_op C)) _.

Next Obligation.
move=> C X f Y g gP /(congr1 proj_val) /= e; apply/val_inj=> /=.
rewrite [in RHS]/cat_id /=; unfold op_id; rewrite -e.
by congr sup; apply/eq_mono.
Qed.

Section BiLimit.

Variable T : nat -> pcpoType.
Variable r : forall n, retr (T n.+1) (T n).

Record bilim := Bilim {
  bilim_val : dfun T;
  _         : forall n, bilim_val n = (r n).1 (bilim_val n.+1)
}.

Canonical bilim_subType := [subType for bilim_val].
Definition bilim_choiceMixin := [choiceMixin of bilim by <:].
Canonical bilim_choiceType :=
  Eval hnf in ChoiceType bilim bilim_choiceMixin.
Definition bilim_poMixin := [poMixin of bilim by <:].
Canonical bilim_poType :=
  Eval hnf in PoType bilim bilim_poMixin.
Canonical bilim_subPoType := Eval hnf in [subPoType of bilim].
Canonical bilim_poChoiceType := Eval hnf in PoChoiceType bilim.

Program Definition bilim_bot : bilim :=
  @Bilim (fun _ => ⊥) _.

Next Obligation.
move=> n /=; apply: appr_anti; first exact: botP.
rewrite (_ : ⊥ = ((r n).1 ∘ (r n).2) ⊥); last by rewrite embK.
rewrite /=; apply: monoP; exact: botP.
Qed.

Lemma bilim_botP x : bilim_bot ⊑ x.
Proof. move=> y; exact: botP. Qed.

Definition bilim_ppoMixin := PpoMixin bilim_botP.
Canonical bilim_ppoType := Eval hnf in PpoType bilim bilim_ppoMixin.

Lemma bilim_sup_clos : subCpo_axiom_of bilim_subPoType.
Proof.
move=> /= x n; set f := mono_comp mono_val' x.
rewrite /sup /= /dfun_sup -(valP (r n).1) /=; congr sup.
apply: val_inj; apply: functional_extensionality=> m /=.
rewrite /flip /=; exact: (valP (x m)).
Qed.

Canonical bilim_subCpoType := SubCpoType bilim_sup_clos.
Definition bilim_cpoMixin := [cpoMixin of bilim by <:].
Canonical bilim_cpoType := Eval hnf in CpoType bilim bilim_cpoMixin.
Canonical bilim_pcpoType := Eval hnf in PcpoType bilim.

Lemma eq_bilim (x y : bilim) :
  (forall n, bilim_val x n = bilim_val y n) <-> x = y.
Proof.
split; last by move=> ->.
by move=> e; apply/val_inj/functional_extensionality_dep.
Qed.

Program Definition bilim_tuple
  (S : pcpoType)
  (f : forall n, pcpo_cont S (T n))
  (fP : forall n, f n = (r n).1 ∘ f n.+1) : pcpo_cont S bilim_pcpoType :=
  Cont (Mono (fun x => @Bilim (fun n => f n x) _) _) _.

Next Obligation. by move=> S f fP x n; rewrite /= fP. Qed.
Next Obligation. move=> S f fP x y xy; move=> n /=; exact: monoP. Qed.
Next Obligation.
move=> S f fP x /=; apply/eq_bilim=> n /=; rewrite -contP; congr sup.
exact/eq_mono.
Qed.

Program Definition bilim_proj n : pcpo_cont bilim_pcpoType (T n) :=
  Cont (Mono (fun x => bilim_val x n) (fun _ _ xy => xy n)) _.

Next Obligation. move=> n x /=; congr sup; exact/eq_mono. Qed.

Lemma bilim_proj_cone n : bilim_proj n = (r n).1 ∘ bilim_proj n.+1.
Proof. by apply/eq_cont; case=> [x xP] /=. Qed.

Lemma bilim_tupleK
  (S : pcpoType)
  (f : forall n, pcpo_cont S (T n))
  (fP : forall n, f n = (r n).1 ∘ f n.+1) n :
  bilim_proj n ∘ bilim_tuple fP = f n.
Proof. exact/eq_cont. Qed.

Lemma bilim_tupleL (S : pcpoType) (f g : pcpo_cont S bilim_pcpoType) :
  (forall n, bilim_proj n ∘ f ⊑ bilim_proj n ∘ g) -> f ⊑ g.
Proof. move=> fg x; move=> n; exact: (fg n x). Qed.

Lemma bilim_tupleP (S : pcpoType) (f g : pcpo_cont S bilim_pcpoType) :
  (forall n, bilim_proj n ∘ f = bilim_proj n ∘ g) -> f = g.
Proof.
move=> e; apply/eq_cont=> x; apply/eq_bilim=> n.
by move/(_ n)/eq_cont/(_ x): e=> /= ->.
Qed.

Program Definition bilim_rproj n : @retr pcpo_cpoCatType bilim_pcpoType (T n) :=
  Retr (bilim_proj n,
        @bilim_tuple _ (fun m => (down r (leq_addr n m)).1 ∘
                                 (down r (leq_addl m n)).2) _) _.

Next Obligation.
move=> n m /=.
rewrite compA -retrD -down1 -downD.
rewrite (eq_irrelevance (leq_trans _ _) (leq_trans (leq_addr n m) (leqnSn _))).
rewrite downD down1 retrD.
rewrite (eq_irrelevance (leq_addl m.+1 n) (leq_trans (leq_addl m n) (leqnSn _))).
by rewrite downD down1 embD compA -(compA _ (r (m + n)).1) embK compf1.
Qed.

Next Obligation.
move=> n; split=> /=.
  by rewrite bilim_tupleK (eq_irrelevance (leq_addl n n) (leq_addr n n)) embK.
apply: bilim_tupleL=> m; rewrite compA bilim_tupleK compf1 /=.
have [nm|/ltnW mn] := leqP n m.
- rewrite (eq_irrelevance (leq_addl m n) (leq_trans nm (leq_addr n m))).
  rewrite downD embD compA embK comp1f; apply/(retrA (down r nm)).
  rewrite (down_coneP bilim_proj_cone nm).
  rewrite -(down_comp r (retr_functor pcpo_cpoCatType) nm).
  reflexivity.
- rewrite (eq_irrelevance (leq_addr n m) (leq_trans mn (leq_addl m n))).
  rewrite downD retrD.
  rewrite (down_coneP bilim_proj_cone mn).
  rewrite -(down_comp r (retr_functor pcpo_cpoCatType) mn) /=.
  rewrite -!compA; apply: monotone_cpo_compR.
  rewrite compA embK comp1f; reflexivity.
Qed.

Lemma bilim_rproj_cone n : bilim_rproj n = r n ∘ bilim_rproj n.+1.
Proof. apply: retr_retr_inj=> /=; exact: bilim_proj_cone. Qed.

Lemma sup_bilim_rproj : sup (mono_proj_of_retr bilim_rproj_cone) = proj_top.
Proof.
apply: sup_unique; split; first by move=> ?; exact: proj_topP.
move=> /= f ub_f; suffices ->: f = proj_top by reflexivity.
apply/val_inj/bilim_tupleP=> n /=; rewrite compf1.
apply: (@comp_emb_inj _ _ _ _ (bilim_rproj n)); rewrite compA /=.
by case/(_ n): ub_f.
Qed.

Section Universal.

Variable S : pcpoType.
Variable rS : forall n, retr S (T n).
Hypothesis rSP : forall n, rS n = r n ∘ rS n.+1.

Program Definition bilim_rtuple : retr S bilim_pcpoType :=
  Retr (sup (Mono (fun n => (bilim_rproj n).2 ∘ (rS n).1) _),
        sup (Mono (fun n => (rS n).2 ∘ (bilim_rproj n).1) _)) _.

Next Obligation.
move=> n m nm.
rewrite (down_coneP bilim_rproj_cone nm) (down_coneP rSP nm) embD.
rewrite -compA (compA (down r nm).2) compA.
rewrite -{2}(compf1 (bilim_rproj m).2).
apply: monotone_cont_comp; last by reflexivity.
apply: monotone_cont_comp; first by reflexivity.
exact: (retr1 (down r nm)).
Qed.
Next Obligation.
move=> n m nm.
rewrite (down_coneP rSP nm) (down_coneP bilim_rproj_cone nm) embD.
rewrite -compA (compA (down r nm).2) compA.
rewrite -{2}(compf1 (rS m).2).
apply: monotone_cont_comp; last by reflexivity.
apply: monotone_cont_comp; first by reflexivity.
exact: (retr1 (down r nm)).
Qed.
Next Obligation.
split; rewrite continuous_cpo_comp.
- move: (congr1 proj_val sup_bilim_rproj)=> /= <-.
  congr sup; apply/eq_mono=> n /=; unfold compp; rewrite /=.
  by rewrite compA -(compA _ (rS n).1) embK compf1.
- set c := mono_cpo_compp _ _ _ ∘ _.
  have [_ least] := supP c; apply: least=> n.
  rewrite /c /=; unfold compp=> /=.
  rewrite compA -(compA _ (bilim_proj n)) bilim_tupleK.
  rewrite (eq_irrelevance (leq_addr n n) (leq_addl n n)) embK compf1.
  exact: retr1.
Qed.

Lemma bilim_rtupleK n : bilim_rproj n ∘ bilim_rtuple = rS n.
Proof.
suffices e: (rS n).1 = (bilim_rproj n).1 ∘ bilim_rtuple.1.
  by apply/retr_retr_inj; rewrite e.
rewrite /= continuous_cpo_compR -(sup_shift _ n) -[LHS]sup_const.
congr sup; apply/eq_mono=> m /=; rewrite /shift /=; unfold compp.
rewrite /constfun /=.
rewrite (down_coneP rSP (leq_addr m n)) compA; congr comp.
rewrite bilim_tupleK.
rewrite (eq_irrelevance (leq_addr (n + m) n) (leq_trans (leq_addr m n) (leq_addl n (n + m)))).
by rewrite downD retrD -compA embK compf1.
Qed.

Lemma proj_of_retr_bilim_rtuple :
  sup (mono_proj_of_retr rSP) = proj_of_retr bilim_rtuple.
Proof.
rewrite /bilim_rtuple; apply/val_inj=> /=.
rewrite continuous_cpo_comp.
congr sup; apply/eq_mono=> n /=; unfold compp, pairf.
rewrite /= compA -(compA _ (bilim_proj n)) bilim_tupleK.
by rewrite (eq_irrelevance (leq_addr n n) (leq_addl n n)) embK compf1.
Qed.

End Universal.

End BiLimit.

Section Void.

Variant void : Set := .

Lemma void_choiceMixin : Choice.mixin_of void.
Proof.
split=> P ex; have [] : False.
by case: ex=> [[]].
Qed.

Canonical void_choiceType := Eval hnf in ChoiceType void void_choiceMixin.

Definition void_appr (x y : void) := False.

Lemma void_apprP : Po.axioms void_appr.
Proof. split; by case. Qed.

Definition void_poMixin := PoMixin void_apprP.
Canonical void_poType := Eval hnf in PoType void void_poMixin.
Canonical void_poChoiceType := Eval hnf in PoChoiceType void.

Definition void_sup (x : chain void) := x 0.
Lemma void_supP (x : chain void) : supremum x (void_sup x).
Proof. by case: (x 0). Qed.
Definition void_cpoMixin := CpoMixin void_supP.
Canonical void_cpoType := Eval hnf in CpoType void void_cpoMixin.

End Void.

Section RecType.

Variable F : {cpo_functor op pcpoType * pcpoType -> pcpoType}.

Definition chain_obj n : pcpoType :=
  iter n (fun T : pcpoType => F (T, T)) [pcpoType of subsing void].

Local Notation "'X_ n" := (chain_obj n)
  (at level 0, n at level 9, format "''X_' n").

Definition chain_mor0_def : pcpo_cont 'X_1 'X_0 * pcpo_cont 'X_0 'X_1 :=
  (⊥, ⊥).

Lemma chain_mor0_proof : retraction chain_mor0_def.1 chain_mor0_def.2.
Proof.
split.
- apply/eq_cont; move=> /= x; apply: val_inj.
  by apply: functional_extensionality=> - [].
- by move=> x; rewrite /= /constfun /=; apply: botP.
Qed.

Definition chain_mor0 : retr 'X_1 'X_0 :=
  Sub chain_mor0_def chain_mor0_proof.

Lemma f_retr_proof (T S : pcpoType) (f : retr T S) :
  retraction (fmap F (f.2, f.1)) (fmap F (f.1, f.2)).
Proof.
split; rewrite -fmapD prod_cat_compE /=.
  by rewrite op_compE /of_op embK fmap1.
(* FIXME: SSR rewrite does not work here *)
change 1 with (@cat_id pcpo_cpoCatType (F (T, T))).
rewrite -fmap1; apply: (cpo_monotone_fmap F); split; exact: (proj2 (retrP f)).
Qed.

Definition f_retr (T S : pcpoType) (f : retr T S) : retr (F (Op T, T)) (F (Op S, S)) :=
  Sub (fmap F (f.2, f.1), fmap F (f.1, f.2))
      (@f_retr_proof T S f).

Lemma f_retr1 (T : pcpoType) :
  f_retr 1 = 1 :> retr (F (Op T, T)) (F (Op T, T)).
Proof. by apply/retr_retr_inj/eq_cont=> x; rewrite /= fmap1. Qed.

Lemma f_retrD (T S R : pcpoType) (f : retr S R) (g : retr T S) :
  f_retr (f ∘ g) = f_retr f ∘ f_retr g.
Proof.
apply: retr_retr_inj; unfold comp, f_retr; simpl.
by rewrite fmapD.
Qed.

Fixpoint chain_mor n : retr 'X_n.+1 'X_n :=
  match n with
  | 0    => chain_mor0
  | n.+1 => f_retr (chain_mor n)
  end.

Definition mu : pcpoType := [pcpoType of bilim chain_mor].

Lemma chain_mor_outlim n :
  bilim_rproj chain_mor n = chain_mor n ∘ bilim_rproj chain_mor n.+1.
Proof. by case: n=> [|n] /=; rewrite [LHS]bilim_rproj_cone. Qed.

Definition roll_aux n : retr (F (Op mu, mu)) 'X_n :=
  match n return retr (F (Op mu, mu)) 'X_n with
  | 0    => chain_mor 0 ∘ f_retr (bilim_rproj chain_mor 0)
  | n.+1 => f_retr (bilim_rproj chain_mor n)
  end.

Lemma roll_aux_cone n : roll_aux n = chain_mor n ∘ roll_aux n.+1.
Proof.
case: n=> [|n] /=; first by apply/retr_retr_inj/eq_cont=> x /=.
by rewrite chain_mor_outlim f_retrD.
Qed.

Definition retr_roll : retr (F (Op mu, mu)) mu :=
  bilim_rtuple roll_aux_cone.

Lemma retr_rollP : proj_of_retr retr_roll = proj_top.
Proof.
rewrite /retr_roll -proj_of_retr_bilim_rtuple.
apply/val_inj=> /=; rewrite -[RHS](fmap1 F).
rewrite (_ : cat_id (Op mu, mu) = (@proj_val pcpo_cpoCatType _ proj_top, proj_val proj_top)) //.
rewrite -!sup_bilim_rproj -sup_pairf -[in LHS](sup_shift _ 1) -contP.
by congr sup; apply/eq_mono=> n /=; rewrite fmapD.
Qed.

Definition roll := retr_roll.1.
Definition unroll := retr_roll.2.

Lemma unrollK : roll ∘ unroll = 1.
Proof. exact: embK. Qed.

Lemma rollK : unroll ∘ roll = 1.
Proof. exact: (congr1 proj_val retr_rollP). Qed.

End RecType.

Section Disc.

Variable T : Type.

Record disc := Disc { disc_val : sing T }.

Canonical disc_newType := [newType for disc_val].
Definition disc_choiceMixin := [choiceMixin of disc by <:].
Canonical disc_choiceType := Eval hnf in ChoiceType disc disc_choiceMixin.
Lemma disc_apprP : Po.axioms (@eq disc).
Proof. split=> //; exact: eq_trans. Qed.
Definition disc_poMixin := PoMixin disc_apprP.
Canonical disc_poType := Eval hnf in PoType disc disc_poMixin.
Canonical disc_poChoiceType := Eval hnf in PoChoiceType disc.

Definition disc_sup (x : chain disc) := x 0.
Lemma disc_supP (x : chain disc) : supremum x (disc_sup x).
Proof.
rewrite /disc_sup; split.
- by move=> n; rewrite (valP x _ _ (leq0n n)).
- by move=> y /(_ 0) ->.
Qed.
Definition disc_cpoMixin := CpoMixin disc_supP.
Canonical disc_cpoType := Eval hnf in CpoType disc disc_cpoMixin.

End Disc.

Module Type UNIV.
Variable univ : pcpoType.
Variable univ_roll : {cont {cont univ -> subsing (disc nat * univ)} -> univ}.
Variable univ_unroll : {cont univ -> {cont univ -> subsing (disc nat * univ)}}.
Hypothesis univ_rollK : univ_unroll ∘ univ_roll = 1.
Hypothesis univ_unrollK : univ_roll ∘ univ_unroll = 1.
End UNIV.

Module UnivDef : UNIV.

Definition univ_def : {cpo_functor op pcpoType * pcpoType -> pcpoType} :=
  pcont_cpo_functor ∘ ⟨op_cpo_functor cpo_of_pcpo_cpo_functor ∘ 'π1,
                       subsing_cpo_functor ∘
                         prod_cpo_functor ∘
                           ⟨const (prod_cat_cpoCatType _ _) (disc_cpoType nat),
                            cpo_of_pcpo_cpo_functor ∘ 'π2⟩⟩.

Definition univ : pcpoType := mu univ_def.
Definition univ_roll := roll univ_def.
Definition univ_unroll := unroll univ_def.
Definition univ_rollK : univ_unroll ∘ univ_roll = 1 := rollK _.
Definition univ_unrollK : univ_roll ∘ univ_unroll = 1 := unrollK _.

End UnivDef.

Notation "'U" := UnivDef.univ.
Notation univ_roll := UnivDef.univ_roll.
Notation univ_unroll := UnivDef.univ_unroll.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
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

Section SubType.

Variables (T : Type) (P : T -> Prop).

Structure subType := SubType {
  sub_sort :> Type;
  val : sub_sort -> T;
  Sub : forall x, P x -> sub_sort;
  _   : forall K (_ : forall x Px, K (@Sub x Px)) u, K u;
  _   : forall x Px, val (@Sub x Px) = x
}.

Variable sT : subType.

Lemma SubP : forall K (_ : forall x Px, K (@Sub sT x Px)) u, K u.
Proof. by case: (sT). Qed.

Lemma SubK : forall x Px, val (@Sub sT x Px) = x.
Proof. by case: (sT). Qed.

Lemma val_inj : injective (@val sT).
Proof.
elim/SubP=> [x Px]; elim/SubP=> [y Py]; rewrite !SubK=> e.
by move: Px; rewrite e=> Px; rewrite (proof_irrelevance _ Px Py).
Qed.

Lemma valP : forall x : sT, P (val x).
Proof. by elim/SubP=> x Px; rewrite SubK. Qed.

Lemma vrefl : forall x, P x -> x = x. Proof. by []. Qed.
Definition vrefl_rect := vrefl.

Definition clone_subType U v :=
  fun sT & sub_sort sT -> U =>
  fun c Urec cK (sT' := @SubType U v c Urec cK) & phant_id sT' sT => sT'.

End SubType.

Local Notation inlined_sub_rect :=
  (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px).

Arguments SubType {_ _} _ _ _ _ _.
Arguments vrefl_rect {_ _} _ _.
Arguments Sub {_ _ _} _ _.
Arguments val {_ _ _} _.
Arguments clone_subType [T P] U v [sT] _ [c Urec cK].

Notation "[ 'subType' 'for' v ]" := (SubType _ v _ inlined_sub_rect vrefl_rect)
 (at level 0, only parsing) : form_scope.

Notation "[ 'subType' 'of' U ]" := (clone_subType U _ id id)
 (at level 0, format "[ 'subType'  'of'  U ]") : form_scope.

Local Notation inlined_new_rect :=
  (fun K K_S u => let (x) as u return K u := u in K_S x).

Definition NewType T U v c Urec :=
  let Urec' P IH := Urec P (fun x : T => IH x isT : P _) in
  SubType U v (fun x _ => c x) Urec'.

Arguments NewType [T U].

Notation "[ 'newType' 'for' v ]" := (NewType v _ inlined_new_rect vrefl_rect)
 (at level 0, only parsing) : form_scope.

Canonical sig_subType (T : Type) (P : T -> Prop) :=
  [subType for @sval T P].

Section Casts.

Variable (T : Type).
Implicit Types (x y z : T).

Definition cast (P : T -> Type) x y (e : x = y) : P x -> P y :=
  match e with erefl => ssrfun.id end.

Lemma castD (P : T -> Type) x y z (p : x = y) (q : y = z) (a : P x) :
  cast q (cast p a) = cast (etrans p q) a.
Proof. by case: z / q=> /=. Qed.

End Casts.

Arguments cast {T} P {x y} e.

Definition castK (T P : Type) (x y : T) (p : x = y) : cast (fun _ => P) p = id :=
  match p with erefl => erefl end.

Definition sapp_cast T S (P : T -> S -> Type) x1 x2 y (p : x1 = x2) :
  forall (f : forall y, P x1 y),
    cast (fun x => forall y, P x y) p f y = cast (fun x => P x y) p (f y) :=
  match p with erefl => fun _ => erefl end.

Definition cast_sapp T (S R : T -> Type) x1 x2 (p : x1 = x2) :
  forall (f : forall x, S x -> R x) (a : S x1),
  f x2 (cast S p a) = cast R p (f x1 a) :=
  match p with erefl => fun _ _ => erefl end.

Definition dapp_cast T (P : T -> Type) (Q : forall x, P x -> Type) x y
  (p : x = y) :
  forall (f : forall a : P x, Q x a) (a : P y),
  cast (fun x => forall a : P x, Q x a) p f a =
  match esym p as q in _ = z return Q z (cast P q a) -> Q y a with
  | erefl => id
  end (f (cast P (esym p) a)) :=
  match p with
  | erefl => fun _ _ => erefl
  end.

Definition cast_congr1 T (P : T -> Type) x y (p : x = y) :
  forall (a : P x), cast P p a = cast id (congr1 P p) a :=
  match p with erefl => fun a => erefl end.

Definition eq_tagged (I : Type) (T_ : I -> Type) (x y : {i : I & T_ i}) (e : x = y) :
  cast T_ (congr1 tag e) (tagged x) = tagged y :=
  match e with
  | erefl => erefl
  end.

Lemma eq_Tagged (I : Type) (T_ : I -> Type) (x y : {i : I & T_ i}) :
  forall (p : tag x = tag y),
    cast T_ p (tagged x) = tagged y ->
    x = y.
Proof.
by case: x y=> [i xi] [j yj] /= p; case: j / p yj => yj /= <-.
Qed.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

Definition dfun T (S : T -> Type) := forall x, S x.
Polymorphic Definition sfun@{i} (T S : Type@{i}) : Type@{i} := T -> S.

Polymorphic Definition flip@{i} (T S : Type@{i}) (R : T -> S -> Type@{i})
  (f : forall x y, R x y) y x := f x y.

Identity Coercion fun_of_dfun : dfun >-> Funclass.
Identity Coercion fun_of_sfun : sfun >-> Funclass.

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

Reserved Notation "g ∘ f" (at level 20, left associativity).

Module Cat.

Section WithUniverse.

Universe i j.
Constraint i <= j.

Section ClassDef.

Variable T : Type@{j}.
Variable hom : T -> T -> Type@{i}.
Variable comp : forall X Y Z, hom Y Z -> hom X Y -> hom X Z.
Variable id : forall X, hom X X.
Arguments id {_}.

Definition axioms :=
  [/\ (forall X Y (f : hom X Y), comp id f = f),
      (forall X Y (f : hom X Y), comp f id = f) &
      (forall X Y Z W (h : hom Z W) (g : hom Y Z) (f : hom X Y),
          comp h (comp g f) = comp (comp h g) f)].

Set Primitive Projections.

(** We add a symmetric version of the associativity axiom so that
    taking opposites is an involution definitionally. *)

Record axioms_ := Axioms_ {
  comp1f : forall X Y (f : hom X Y), comp id f = f;
  compf1 : forall X Y (f : hom X Y), comp f id = f;
  compA  : forall X Y Z W (h : hom Z W) (g : hom Y Z) (f : hom X Y),
             comp h (comp g f) = comp (comp h g) f;
  compAV : forall X Y Z W (h : hom Z W) (g : hom Y Z) (f : hom X Y),
             comp (comp h g) f = comp h (comp g f)
}.

Lemma pack_axioms : axioms -> axioms_.
Proof. by case=> H1 H2 H3; split. Qed.

End ClassDef.

Record mixin_of (T : Type@{j}) (hom : T -> T -> Type@{i}) := Mixin {
  comp  : forall X Y Z, hom Y Z -> hom X Y -> hom X Z;
  id    : forall X, hom X X;
  compP : axioms_ comp id
}.

Notation class_of := mixin_of (only parsing).

Record type : Type := Pack {
  obj : Type@{j};
  hom : obj -> obj -> Type@{i};
  class : mixin_of hom
}.
Local Coercion obj : type >-> Sortclass.
Variables (T : Type@{j}) (cT : type).
Definition clone h c of phant_id class c := @Pack T h c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Unset Primitive Projections.

End WithUniverse.

Module Exports.
Coercion obj : type >-> Sortclass.
Coercion hom : type >-> Funclass.
Notation catType := type.
Notation CatMixin a := (Mixin (pack_axioms a)).
Notation CatType T h m := (@Pack T h m).
End Exports.

End Cat.

Export Cat.Exports.

Section CatTheory.

Universe i j.
Constraint i <= j.

Variable C : catType@{i j}.

Definition hom := @Cat.hom@{i j} C.
Definition comp := @Cat.comp@{i j} _ _ (@Cat.class C).
Definition cat_id := @Cat.id@{i j} _ _ (@Cat.class C).
Arguments cat_id {_}.

Local Notation "g ∘ f" := (comp g f).
Local Notation "1" := cat_id.

Lemma comp1f X Y (f : C X Y) : 1 ∘ f = f.
Proof. by rewrite /comp /cat_id; case: (@Cat.class C)=> ?? []. Qed.

Lemma compf1 X Y (f : C X Y) : f ∘ 1 = f.
Proof. by rewrite /comp /cat_id; case: (@Cat.class C)=> ?? []. Qed.

Lemma compA X Y Z W (h : C Z W) (g : C Y Z) (f : C X Y) :
  h ∘ (g ∘ f) = h ∘ g ∘ f.
Proof. by rewrite /comp; case: (@Cat.class C)=> ?? []. Qed.

Definition compp X Y Z (p : C Y Z * C X Y) : C X Z := p.1 ∘ p.2.

Record iso X Y := Iso {
  iso1  : C X Y;
  iso2  : C Y X;
  iso1K : iso2 ∘ iso1 = 1;
  iso2K : iso1 ∘ iso2 = 1
}.

End CatTheory.

Notation "g ∘ f" := (comp g f) : cat_scope.
Notation "1" := (@cat_id _ _) : cat_scope.
Arguments cat_id {_}.

Open Scope cat_scope.

Section Opposite.

Universe i j.
Constraint i <= j.

Variable C : catType@{i j}.

Definition op (T : Type@{j}) : Type@{j} := T.
Definition op_hom (T : Type@{j}) (hom : T -> T -> Type@{i}) X Y : Type@{i} :=
  hom Y X.
Definition op_comp X Y Z (f : op_hom C Y Z) (g : op_hom C X Y) : op_hom C X Z :=
  comp@{i j} g f.
Definition op_id X : op_hom C X X := cat_id@{i j} X.

Definition op_catMixin :=
  @Cat.Mixin (op C) (op_hom C) op_comp op_id
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
Definition Op (T : Type@{j}) (x : T) : op T := x.
Definition of_op (T : Type@{j}) (hom : T -> T -> Type@{i}) X Y :
  op_hom hom X Y -> hom Y X :=
  id.
Definition to_op (T : Type@{j}) (hom : T -> T -> Type@{i}) X Y :
  hom X Y -> op_hom hom Y X := id.
Lemma op_compE X Y Z (f : op_hom C Y Z) (g : op_hom C X Y) :
  f ∘ g = of_op g ∘ of_op f.
Proof. by []. Qed.

End Opposite.

Notation "C '^op'" := (op_catType C)
  (at level 2, left associativity, format "C ^op") : cat_scope.

Section CatBaseChange.

Universes i j.
Constraint i <= j.

Variables (T : Type@{j}) (C : catType@{i j}) (f : T -> C).

Definition base_change_hom (X Y : T) := C (f X) (f Y).

Notation base_change_comp :=
  (fun (X Y Z : T) (f : base_change_hom Y Z) (g : base_change_hom X Y) =>
     f ∘ g).

Notation base_change_id := (fun (X : T) => 1).

Lemma base_change_compP :
  @Cat.axioms T base_change_hom base_change_comp base_change_id.
Proof. by split=> *; rewrite ?comp1f ?compf1 ?compA. Qed.

Definition BaseChangeCatMixin := CatMixin base_change_compP.

End CatBaseChange.

Section DiscCat.

Universe i.

Variable T : Type@{i}.

Definition disc_obj : Type@{i} := T.
Definition disc_hom (x y : T) : Set := x = y.
Definition disc_id (x : T) : disc_hom x x := erefl.
Definition disc_comp (x y z : T)
                     (f : disc_hom y z) (g : disc_hom x y) : disc_hom x z :=
  etrans g f.

Lemma disc_compP : Cat.axioms@{Set i} disc_comp disc_id.
Proof.
split=> //.
- by move=> X Y f; case: Y / f.
- by move=> A B C D h g f; case: D / h.
Qed.

Definition disc_catMixin := CatMixin@{Set i} disc_compP.
Canonical disc_catType : catType@{Set i} :=
  Eval hnf in CatType disc_obj disc_hom disc_catMixin.

End DiscCat.

Section IndiscCat.

Universe i.

Variable T : Type@{i}.

Definition indisc_obj : Type@{i} := T.
Definition indisc_hom (_ _ : T) : Set := unit.
Definition indisc_id (_ : T) := tt.
Definition indisc_comp (_ _ _ : T) (x y : unit) := tt.

Lemma indisc_compP : Cat.axioms@{Set i} indisc_comp indisc_id.
Proof. by rewrite /indisc_comp /indisc_id; split=> // ?? []. Qed.

Definition indisc_catMixin := CatMixin@{Set i} indisc_compP.
Canonical indisc_catType : catType@{Set i} :=
  Eval hnf in CatType indisc_obj indisc_hom indisc_catMixin.

End IndiscCat.

Canonical unit_catType : catType@{Set Set} :=
  CatType unit (@indisc_hom@{Set} unit) (indisc_catMixin@{Set} unit).

Section FunCat.

Universe i j.
Constraint i < j.

Definition sfun_catMixin :=
  @Cat.Mixin@{i j}
     Type@{i} sfun@{i} (fun _ _ _ f g x => f (g x)) (fun _ x => x)
     (@Cat.Axioms_
        Type@{i} sfun@{i} (fun _ _ _ f g x => f (g x)) (fun _ x => x)
        (fun _ _ _ => erefl) (fun _ _ _ => erefl)
        (fun _ _ _ _ _ _ _ => erefl) (fun _ _ _ _ _ _ _ => erefl)).

Canonical Sets := CatType Type@{i} sfun@{i} sfun_catMixin.

Lemma fun_compE (T S R : Type@{i}) (f : sfun S R) (g : sfun T S) :
  f ∘ g = f \o g.
Proof. by []. Qed.

End FunCat.

Section Functor.

Universe i j.
Constraint i <= j.

Variables C D : catType@{i j}.

(* FIXME: Why are the universe annotations needed? *)
Record functor := Functor {
  fobj  :> C -> D;
  fmap  :  forall X Y, C X Y -> D (fobj X) (fobj Y);
  fmap1 :  forall X, fmap 1 = 1 :> D (fobj X) (fobj X);
  fmapD :  forall X Y Z (f : C Y Z) (g : C X Y),
             fmap (comp@{i j} f g) = fmap f ∘ fmap g
}.

Definition functor_of of phant (C -> D) := functor.
Identity Coercion functor_of_functor : functor_of >-> functor.
Notation "{ 'functor' T }" := (functor_of (Phant T))
  (at level 0, format "{ 'functor'  T }") : type_scope.

Lemma eq_functor F G :
  Tagged (fun F => forall X Y, C X Y -> D (F X) (F Y)) (fmap F) =
  Tagged (fun F => forall X Y, C X Y -> D (F X) (F Y)) (fmap G) <->
  F = G.
Proof.
split; last by move=> ->.
case: F G=> [F0 F1 Fmap1 FmapD] [G0 G1 Gmap1 GmapD] /= e.
move: {e} (congr1 _ e) (eq_tagged e)=> /= e0 e1.
case: G0 / e0 G1 e1 Gmap1 GmapD => /= G1 e1; case: G1 / e1=> Gmap1 GmapD.
by rewrite (proof_irrelevance _ Fmap1 Gmap1) (proof_irrelevance _ FmapD GmapD).
Qed.

Implicit Types F G H : {functor C -> D}.

Record nat_trans F G := NatTrans {
  nt_val  :> forall X, D (F X) (G X);
  nt_valP :  forall X Y (f : C X Y),
               fmap G f ∘ nt_val X = nt_val Y ∘ fmap F f
}.

Arguments NatTrans {_ _} _ _.

Canonical nat_trans_subType F G :=
  [subType for @nt_val F G].

Lemma eq_nat_trans F G (α β : nat_trans F G) :
  (forall X, α X = β X) <-> α = β.
Proof.
split; last by move=> ->.
by move=> e; apply: val_inj; apply: functional_extensionality_dep.
Qed.

Program Definition nat_trans_comp F G H
  (α : nat_trans G H) (β : nat_trans F G) : nat_trans F H :=
  NatTrans (fun X => α X ∘ β X) _.

Next Obligation.
by move=> F G H α β X Y f /=; rewrite compA nt_valP -compA nt_valP compA.
Qed.

Program Definition nat_trans_id F : nat_trans F F :=
  NatTrans (fun X => 1) _.

Next Obligation. by move=> F X Y f /=; rewrite comp1f compf1. Qed.

Lemma nat_trans_compP : Cat.axioms nat_trans_comp nat_trans_id.
Proof.
split.
- by move=> F G α; apply/eq_nat_trans=> X /=; rewrite comp1f.
- by move=> F G α; apply/eq_nat_trans=> X /=; rewrite compf1.
- by move=> F G H K α β γ; apply/eq_nat_trans=> X /=; rewrite compA.
Qed.

Definition functor_catMixin := CatMixin nat_trans_compP.
Canonical functor_catType :=
  CatType functor nat_trans functor_catMixin.
Canonical functor_of_catType :=
  CatType {functor C -> D} nat_trans functor_catMixin.

End Functor.

Arguments fmap {_ _} _ {_ _}.
Arguments Functor {_ _} _ _ _ _.
Notation "{ 'functor' T }" := (functor_of _ _ (Phant T))
  (at level 0, format "{ 'functor'  T }") : type_scope.
Arguments NatTrans {_ _ _ _} _ _.

Section CatCat.

Universe i j k.
Constraint i <= j.
Constraint j < k.

Definition functor_id (C : catType@{i j}) : {functor C -> C} :=
  @Functor C C id (fun _ _ => id) (fun _ => erefl) (fun _ _ _ _ _ => erefl).

Program Definition functor_comp (C D E : catType@{i j})
                        (F : {functor D -> E}) (G : {functor C -> D})
  : {functor C -> E} :=
  Functor (fun X => F (G X)) (fun _ _ f => fmap F (fmap G f)) _ _.

Next Obligation. by move=> C D E F G X /=; rewrite !fmap1. Qed.
Next Obligation. by move=> C D E F G X Y Z f g /=; rewrite !fmapD. Qed.

Lemma functor_compP : @Cat.axioms@{j k} _ _ functor_comp functor_id.
Proof. split; by move=> *; apply/eq_functor. Qed.

Definition cat_catMixin := CatMixin functor_compP.
Canonical cat_catType :=
  Eval hnf in CatType catType functor cat_catMixin.

End CatCat.

Section ProdCatCat.

Universe i j.
Constraint i <= j.

Variables C D : catType@{i j}.

Definition prod_cat_hom (X Y : C * D) : Type@{i} := C X.1 Y.1 * D X.2 Y.2.
Definition prod_cat_id (X : C * D) : prod_cat_hom X X :=
  (cat_id@{i j} _, cat_id@{i j} _).
Definition prod_cat_comp (X Y Z : C * D)
                         (f : prod_cat_hom Y Z) (g : prod_cat_hom X Y)
                         : prod_cat_hom X Z :=
  (comp@{i j} f.1 g.1, comp@{i j} f.2 g.2).

Lemma prod_cat_compP : Cat.axioms prod_cat_comp prod_cat_id.
Proof.
rewrite /prod_cat_comp /prod_cat_id; split.
- by case=> [??] [??] [??] /=; rewrite !comp1f.
- by case=> [??] [??] [??] /=; rewrite !compf1.
- by case=> [??] [??] [??] [??] [??] [??] [??] /=; rewrite !compA.
Qed.

Definition prod_cat_catMixin := CatMixin prod_cat_compP.
Canonical prod_cat_catType :=
  Eval hnf in CatType (C * D) prod_cat_hom prod_cat_catMixin.

Lemma prod_cat_compE
  X Y Z (f : prod_cat_catType Y Z) (g : prod_cat_catType X Y) :
  f ∘ g = (f.1 ∘ g.1, f.2 ∘ g.2).
Proof. by []. Qed.

End ProdCatCat.

Module TermCat.

Section ClassDef.

Universe i j.
Constraint i <= j.

Record mixin_of (C : Type@{j}) (hom : C -> C -> Type@{i}) := Mixin {
  term : C;
  bang : forall X, hom X term;
  _    : forall X (f : hom X term), f = bang X
}.

Record class_of (C : Type@{j}) (hom : C -> C -> Type@{i}) :=
  Class {base : Cat.mixin_of@{i j} hom; mixin : mixin_of hom}.

Record type := Pack {
  obj : Type@{j};
  hom : obj -> obj -> Type@{i};
   _ : class_of hom
}.
Local Coercion obj : type >-> Sortclass.
Local Coercion base : class_of >-> Cat.mixin_of.
Variables (C0 : Type@{j}) (C1 : C0 -> C0 -> Type@{i}) (cC : type).
Definition class := let: Pack _ _ c as cC' := cC return class_of (@hom cC') in c.
Definition clone c of phant_id class c := @Pack C0 C1 c.

Definition catType := @Cat.Pack _ _ class.

Definition pack m :=
  [find c | @Cat.hom@{i j} c ~ C1 | "not a catType" ]
  [find b | Cat.class@{i j} c ~ b ]
  @Pack C0 C1 (@Class _ _ b m).

End ClassDef.

Module Exports.
Coercion obj : type >-> Sortclass.
Coercion hom : type >-> Funclass.
Coercion base : class_of >-> Cat.mixin_of.
Coercion catType : type >-> Cat.type.
Canonical catType.
Notation termCatType := type.
Notation TermCatMixin := Mixin.
Notation TermCatType C0 C1 m := (@pack C0 C1 m _ unify _ unify).
End Exports.

End TermCat.

Export TermCat.Exports.

Section TermCatTheory.

Universe i j.
Constraint i <= j.

Variable C : termCatType@{i j}.

Definition term : C :=
  TermCat.term@{i j} (TermCat.mixin (TermCat.class C)).

Definition bang (X : C) : C X term :=
  TermCat.bang@{i j} (TermCat.mixin (TermCat.class C)) X.

Local Notation "'!" := (bang _) (at level 0).
Local Notation "''!_' X" := (bang X)
  (at level 0, X at level 9, format "''!_' X").

Lemma bangP X (f : C X term) : f = '!.
Proof.
by move: X f; rewrite /term /bang; case: (TermCat.mixin _).
Qed.

End TermCatTheory.

Local Notation "'!" := (bang _) (at level 0) : cat_scope.
Local Notation "''!_' X" := (bang X)
  (at level 0, X at level 9, format "''!_' X") : cat_scope.
Arguments term {_}.

Section TermCatCat.

Universe i j k.
Constraint i <= j.
Constraint j < k.

Definition cat_term : catType@{i j} := unit_catType.
Definition cat_bang (C : catType@{i j}) : {functor C -> cat_term} :=
  @Functor _ cat_term (fun _ => tt) (fun _ _ _ => tt)
           (fun _ => erefl) (fun _ _ _ _ _ => erefl).

Lemma cat_bangP (C : catType@{i j}) (F : {functor C -> cat_term}) : F = cat_bang _.
Proof.
case: F=> F0 F1 H1 H2; apply/eq_functor=> /= {H1 H2}.
move: F1; have -> : F0 = fun _ => tt.
  by apply: functional_extensionality=> x; case: (F0 x).
move=> F1; f_equal; do 3![apply: functional_extensionality_dep=> ?].
by case: (F1 _ _ _).
Qed.

Definition cat_termCatMixin : TermCat.mixin_of@{j k} _ := TermCatMixin cat_bangP.
Canonical cat_termCatType : termCatType@{j k} :=
  @TermCat.Pack@{j k} catType@{i j} functor@{i j}
                      (TermCat.Class cat_catMixin@{i j k} cat_termCatMixin).

End TermCatCat.

Module ProdCat.

Section ClassDef.

Universe i j.
Constraint i <= j.

Record axioms_of (C : catType@{i j})
                 (prod : C -> C -> C)
                 (pair  : forall {X Y Z}, C Z X -> C Z Y -> C Z (prod X Y))
                 (proj1 : forall {X Y}, C (prod X Y) X)
                 (proj2 : forall {X Y}, C (prod X Y) Y) := Ax {
  pairKL : forall X Y Z (f : C Z X) (g : C Z Y),
             proj1 ∘ pair f g = f;
  pairKR : forall X Y Z (f : C Z X) (g : C Z Y),
             proj2 ∘ pair f g = g;
  pairP  : forall X Y Z (f g : C Z (prod X Y)),
             proj1 ∘ f = proj1 ∘ g /\
             proj2 ∘ f = proj2 ∘ g ->
             f = g
}.

Record mixin_of (C : catType@{i j}) := Mixin {
  prod; pair; proj1; proj2; _ : @axioms_of C prod pair proj1 proj2
}.

Definition axioms (C : catType@{i j}) (m : mixin_of C) :=
  let: Mixin _ _ _ _ ax := m return axioms_of (pair m) (proj1 m) (proj2 m) in
  ax.

Record class_of (C : Type@{j}) (hom : C -> C -> Type@{i}) := Class {
  base  : Cat.mixin_of hom;
  mixin : mixin_of (Cat.Pack base)
}.

Record type := Pack {
  obj : Type@{j};
  hom : obj -> obj -> Type@{i};
  _ : class_of hom
}.
Local Coercion obj : type >-> Sortclass.
Local Coercion hom : type >-> Funclass.
Local Coercion base : class_of >-> Cat.mixin_of.
Variables (C0 : Type@{j}) (C1 : C0 -> C0 -> Type@{i}) (cC : type).
Definition class := let: Pack _ _ c as cC' := cC return class_of (@hom cC') in c.
Definition clone c of phant_id class c := @Pack C0 C1 c.

Definition catType := @Cat.Pack _ _ class.

Definition pack :=
  [find c | @Cat.hom c ~ C1 | "not a catType" ]
  [find b | Cat.class c ~ b ]
  fun m => @Pack C0 C1 (@Class C0 C1 b m).

End ClassDef.

Module Exports.
Coercion obj : type >-> Sortclass.
Coercion hom : type >-> Funclass.
Coercion base : class_of >-> Cat.mixin_of.
Coercion catType : type >-> Cat.type.
Canonical catType.
Notation prodCatType := type.
Notation ProdCatMixin := Mixin.
Notation ProdCatType C0 C1 m := (@pack C0 C1 _ unify _ unify m).
End Exports.

End ProdCat.

Export ProdCat.Exports.

Section ProdCatTheory.

Universe i j.
Constraint i <= j.

Variable C : prodCatType@{i j}.

Definition cat_prod (X Y : C) : C :=
  ProdCat.prod@{i j} (ProdCat.mixin (ProdCat.class C)) X Y.
Local Notation "X × Y" := (cat_prod X Y)
  (at level 50, left associativity) : cat_scope.
Definition cat_pair X Y Z (f : C Z X) (g : C Z Y) : C Z (X × Y) :=
  ProdCat.pair@{i j} (ProdCat.mixin (ProdCat.class C)) f g.
Local Notation "⟨ f , g , .. , h ⟩" :=
  (cat_pair .. (cat_pair f g) .. h)
  (format "⟨ f ,  g ,  .. ,  h ⟩").
Definition cat_proj1 X Y : C (X × Y) X :=
  ProdCat.proj1@{i j} (ProdCat.mixin (ProdCat.class C)) X Y.
Definition cat_proj2 X Y : C (X × Y) Y :=
  ProdCat.proj2@{i j} (ProdCat.mixin (ProdCat.class C)) X Y.
Local Notation "'π1" := (cat_proj1 _ _).
Local Notation "'π2" := (cat_proj2 _ _).

Lemma pairKL X Y Z (f : C Z X) (g : C Z Y) : 'π1 ∘ ⟨f, g⟩ = f.
Proof. exact: (ProdCat.pairKL (ProdCat.axioms _)). Qed.

Lemma pairKR X Y Z (f : C Z X) (g : C Z Y) : 'π2 ∘ ⟨f, g⟩ = g.
Proof. exact: (ProdCat.pairKR (ProdCat.axioms _)). Qed.

Lemma pairP X Y Z (f g : C Z (X × Y)) :
  'π1 ∘ f = 'π1 ∘ g /\ 'π2 ∘ f = 'π2 ∘ g -> f = g.
Proof. exact: (ProdCat.pairP (ProdCat.axioms _)). Qed.

Lemma comp_pair X Y Z W (f : C Z X) (g : C Z Y) (h : C W Z) :
  ⟨f, g⟩ ∘ h = ⟨f ∘ h, g ∘ h⟩.
Proof. by apply: pairP; rewrite !compA !pairKL !pairKR. Qed.

Lemma projK X Y : ⟨'π1, 'π2⟩ = 1 :> C (X × Y) (X × Y).
Proof. by apply: pairP; rewrite pairKL pairKR !compf1. Qed.

Lemma split_pair X1 Y1 X2 Y2 (f : C X1 X2) (g : C Y1 Y2) :
  ⟨f ∘ 'π1, g ∘ 'π2⟩ = ⟨f ∘ 'π1, 'π2⟩ ∘ ⟨'π1, g ∘ 'π2⟩.
Proof. by rewrite comp_pair -compA pairKL pairKR. Qed.

Lemma split_pairV X1 Y1 X2 Y2 (f : C X1 X2) (g : C Y1 Y2) :
  ⟨f ∘ 'π1, g ∘ 'π2⟩ = ⟨'π1, g ∘ 'π2⟩ ∘ ⟨f ∘ 'π1, 'π2⟩.
Proof. by rewrite comp_pair -compA pairKL pairKR. Qed.

Definition prod_fobj (X : C * C) := X.1 × X.2.
Definition prod_fmap (X Y : C * C) f : C (prod_fobj X) (prod_fobj Y) :=
  ⟨f.1 ∘ 'π1, f.2 ∘ 'π2⟩.

Program Definition prod_functor :=
  @Functor _ _ prod_fobj prod_fmap _ _.

Next Obligation. by move=> [X Y]; rewrite /prod_fmap /= !comp1f projK. Qed.
Next Obligation.
move=> [X1 Y1] [X2 Y2] [X3 Y3] [/= f1 g1] [/= f2 g2]; rewrite /prod_fmap /=.
by rewrite comp_pair -![in RHS]compA pairKL pairKR !compA.
Qed.

End ProdCatTheory.

Notation "X × Y" := (cat_prod X Y)
  (at level 50, left associativity) : cat_scope.
Local Notation "⟨ f , g , .. , h ⟩" :=
  (cat_pair .. (cat_pair f g) .. h)
  (format "⟨ f ,  g ,  .. ,  h ⟩") : cat_scope.
Notation "'π1" := (cat_proj1 _ _).
Notation "'π2" := (cat_proj2 _ _).

Section CatProdCat.

Universe i j k.
Constraint i <= j.
Constraint j < k.

Program Definition prod_cat_pair (C D E : catType@{i j})
  (F : {functor E -> C}) (G : {functor E -> D}) :=
  Functor (fun X => (F X, G X)) (fun _ _ f => (fmap F f, fmap G f)) _ _.

Next Obligation. by move=> C D E F G X /=; rewrite !fmap1. Qed.
Next Obligation. by move=> C D E F G X Y Z f g /=; rewrite !fmapD. Qed.

Definition prod_cat_proj1 (C D : catType@{i j}) : {functor C * D -> C} :=
  Functor fst (fun _ _ f => f.1) (fun _ => erefl) (fun _ _ _ _ _ => erefl).

Definition prod_cat_proj2 (C D : catType@{i j}) : {functor C * D -> D} :=
  Functor snd (fun _ _ f => f.2) (fun _ => erefl) (fun _ _ _ _ _ => erefl).

Lemma cat_prodP : ProdCat.axioms_of@{j k} prod_cat_pair prod_cat_proj1 prod_cat_proj2.
Proof.
split; try by move=> *; apply/eq_functor.
move=> /= C D E [/= F0 F1 Fmap1 FmapD] [/= G0 G1 Gmap1 GmapD].
case=> [/eq_functor /= e1 /eq_functor /= e2].
have e_obj : F0 = G0.
  apply: functional_extensionality=> X.
  move/(congr1 (fun f => tag f X)): e1.
  move/(congr1 (fun f => tag f X)): e2=> /=.
  by case: (F0 X) (G0 X)=> [??] [??] /= -> ->.
move: G1 Gmap1 GmapD e1 e2; rewrite -{}e_obj {G0}.
move=> G1 Gmap1 GmapD e1 e2.
move: (eq_tagged e1) (eq_tagged e2).
rewrite (proof_irrelevance _ (congr1 tag e1) erefl) /=.
rewrite (proof_irrelevance _ (congr1 tag e2) erefl) /=.
move=> {e1 e2} e1 e2; apply/eq_functor; congr Tagged=> /=.
apply: functional_extensionality_dep=> X.
apply: functional_extensionality_dep=> Y.
apply: functional_extensionality=> f.
move: (congr1 (fun H => H X Y f) e1) (congr1 (fun H => H X Y f) e2).
by case: (F1 X Y f) (G1 X Y f)=> [??] [??] /= -> ->.
Qed.

Definition cat_prodCatMixin : ProdCat.mixin_of@{j k} _ :=
  @ProdCatMixin cat_catType@{i j k} _ _ _ _ cat_prodP.

Canonical cat_prodCatType : prodCatType@{j k} :=
  Eval hnf in ProdCatType catType functor cat_prodCatMixin.

End CatProdCat.

Section HomFunctor.

Universe i j k.
Constraint i <= j.
Constraint j < k.

Variable C : catType@{i j}.

Definition hom_fobj (X : prod@{j} C^op C) : Type@{i} := C X.1 X.2.
Definition hom_fmap (X Y : prod@{j} C^op C)
                    (f : hom _ X Y) :
  sfun (hom_fobj X) (hom_fobj Y) :=
  fun g => f.2 ∘ g ∘ f.1.
Lemma hom_fmap1 (X : prod@{j} C^op C) :
  hom_fmap (cat_id@{i j} X) = cat_id@{i j} (hom_fobj X).
Proof.
apply/functional_extensionality=> f; rewrite /hom_fmap /=.
by rewrite comp1f compf1.
Qed.
Lemma hom_fmapD (X Y Z : prod@{j} C^op C)
  (f : prod_cat_catType@{i j} C^op C Y Z) (g : hom _ X Y) :
  hom_fmap (comp@{i j} f g) = comp@{i j} (hom_fmap f) (hom_fmap g).
Proof.
apply/functional_extensionality=> x; rewrite /hom_fmap /= !fun_compE /=.
by rewrite op_compE !compA.
Qed.

Definition hom_functor@{} : {functor C^op * C -> Sets@{i j}} :=
  Functor hom_fobj hom_fmap hom_fmap1 hom_fmapD.

End HomFunctor.

Module CartCat.

Section ClassDef.

Universe i j.
Constraint i <= j.

Record class_of (C : Type@{j}) (hom : C -> C -> Type@{i}) := Class {
  base       : Cat.mixin_of@{i j} hom;
  term_mixin : TermCat.mixin_of@{i j} hom;
  prod_mixin : ProdCat.mixin_of@{i j} (Cat.Pack base)
}.

Record type := Pack {
  obj : Type@{j};
  hom : obj -> obj -> Type@{i};
  _   : class_of hom
}.
Local Coercion obj : type >-> Sortclass.
Local Coercion base : class_of >-> Cat.mixin_of.
Variables (C0 : Type@{j}) (C1 : C0 -> C0 -> Type@{i}) (cC : type).
Definition class := let: Pack _ _ c as cC' := cC return class_of (@hom cC') in c.
Definition clone c of phant_id class c := @Pack C0 C1 c.

Definition catType := @Cat.Pack _ _ class.
Definition termCatType :=
  @TermCat.Pack _ _ (TermCat.Class class (term_mixin class)).
Definition prodCatType :=
  @ProdCat.Pack _ _ (ProdCat.Class (prod_mixin class)).

Definition pack :=
  [find tc | @TermCat.hom@{i j} tc ~ C1 | "not a termCatType" ]
  [find tb | TermCat.class@{i j} tc ~ tb ]
  [find pc | @ProdCat.hom@{i j} pc ~ C1 | "not a prodCatType" ]
  [find m  | ProdCat.mixin (ProdCat.class pc) ~ m ]
  @Pack C0 C1 (@Class _ _ (TermCat.base tb) (TermCat.mixin tb) m).

End ClassDef.

Module Exports.
Coercion obj : type >-> Sortclass.
Coercion hom : type >-> Funclass.
Coercion base : class_of >-> Cat.mixin_of.
Coercion catType : type >-> Cat.type.
Canonical catType.
Coercion termCatType : type >-> TermCat.type.
Canonical termCatType.
Coercion prodCatType : type >-> ProdCat.type.
Canonical prodCatType.
Notation cartCatType := type.
Notation CartCatType C0 C1 := (@pack C0 C1 _ unify _ unify _ unify _ unify).
End Exports.

End CartCat.

Export CartCat.Exports.

Section CatCartCat.

Universe i j k.
Constraint i <= j.
Constraint j < k.

Canonical cat_cartCatType : cartCatType@{j k} :=
  Eval hnf in CartCatType catType@{i j} functor@{i j}.

End CatCartCat.

Module CCCat.

Section ClassDef.

Universe i j.
Constraint i <= j.

Record axioms_of (C : cartCatType@{i j})
                 (exp : C -> C -> C)
                 (curry : forall {X Y Z}, C (X × Y) Z -> C X (exp Y Z))
                 (eval : forall {X Y}, C (exp X Y × X) Y) := Ax {
  curryK : forall X Y Z (f : C (X × Y) Z),
             eval ∘ ⟨curry f ∘ 'π1, 'π2⟩ = f;
  evalK  : forall X Y Z (f : C X (exp Y Z)),
             curry (eval ∘ ⟨f ∘ 'π1, 'π2⟩) = f
}.

Record mixin_of (C : cartCatType@{i j}) := Mixin {
  exp; curry; eval; _ : @axioms_of C exp curry eval
}.

Definition axioms (C : cartCatType@{i j}) (m : mixin_of C) :=
  let: Mixin _ _ _ ax := m return axioms_of (curry m) (eval m) in
  ax.

Record class_of (C : Type@{j}) (hom : C -> C -> Type@{i}) := Class {
  base : CartCat.class_of hom;
  mixin : mixin_of (CartCat.Pack base)
}.

Record type := Pack {
  obj : Type@{j};
  hom : obj -> obj -> Type@{i};
  _   : class_of hom
}.
Local Coercion obj : type >-> Sortclass.
Local Coercion hom : type >-> Funclass.
Local Coercion base : class_of >-> CartCat.class_of.
Variables (C0 : Type@{j}) (C1 : C0 -> C0 -> Type@{i}) (cC : type).
Definition class := let: Pack _ _ c as cC' := cC return class_of (@hom cC') in c.
Definition clone c of phant_id class c := @Pack C0 C1 c.

Definition catType := @Cat.Pack _ _ class.
Definition termCatType :=
  @TermCat.Pack _ _ (TermCat.Class class (CartCat.term_mixin class)).
Definition prodCatType :=
  @ProdCat.Pack _ _ (ProdCat.Class (CartCat.prod_mixin class)).
Definition cartCatType := @CartCat.Pack _ _ class.

Definition pack :=
  [find cc | @CartCat.hom@{i j} cc ~ C1 | "not a cartCatType" ]
  [find cb | @CartCat.class@{i j} cc ~ cb ]
  fun m => @Pack C0 C1 (@Class _ _ cb m).

End ClassDef.

Module Exports.
Coercion obj : type >-> Sortclass.
Coercion base : class_of >-> CartCat.class_of.
Coercion catType : type >-> Cat.type.
Canonical catType.
Coercion termCatType : type >-> TermCat.type.
Canonical termCatType.
Coercion prodCatType : type >-> ProdCat.type.
Canonical prodCatType.
Coercion cartCatType : type >-> CartCat.type.
Canonical cartCatType.
Notation CCCatMixin := Mixin.
Notation ccCatType := type.
Notation CCCatType C0 C1 m := (@pack C0 C1 _ unify _ unify m).
End Exports.

End CCCat.

Export CCCat.Exports.

Section CCCatTheory.

Universe i j.
Constraint i <= j.

Variable C : ccCatType@{i j}.

Definition exp (X Y : C) :=
  CCCat.exp@{i j} (CCCat.mixin (CCCat.class C)) X Y.
Local Notation "X ⇒ Y" := (exp X Y)
  (at level 25, right associativity).
Definition curry (X Y Z : C) (f : C (X × Y) Z) : C X (Y ⇒ Z) :=
  CCCat.curry@{i j} (CCCat.mixin (CCCat.class C)) f.
Local Notation "'λ' f" := (curry f) (at level 0, f at level 9).
Definition eval (X Y : C) : C ((X ⇒ Y) × X) Y :=
  CCCat.eval@{i j} (CCCat.mixin (CCCat.class C)) X Y.
Arguments eval {_ _}.

Definition uncurry X Y Z (f : C X (Y ⇒ Z)) : C (X × Y) Z :=
  eval ∘ ⟨f ∘ 'π1, 'π2⟩.

Lemma curryK X Y Z (f : C (X × Y) Z) : uncurry λ f = f.
Proof. exact: (CCCat.curryK (CCCat.axioms _)). Qed.

Lemma uncurryK X Y Z (f : C X (Y ⇒ Z)) : λ (uncurry f) = f.
Proof. exact: (CCCat.evalK (CCCat.axioms _)). Qed.

Lemma comp_curry X1 X2 Y Z (f : C (X2 × Y) Z) (g : C X1 X2) :
  λ f ∘ g = λ (f ∘ ⟨g ∘ 'π1, 'π2⟩).
Proof.
rewrite -[LHS]uncurryK -[RHS]uncurryK; congr curry; rewrite curryK.
rewrite -{2}(curryK f) /uncurry -[RHS]compA comp_pair.
by rewrite -[in RHS]compA pairKL pairKR compA.
Qed.

Definition exp_fobj (X : C^op * C) := X.1 ⇒ X.2.
Definition exp_fmap (X Y : C^op * C) (f : hom _ X Y) :
  C (exp_fobj X) (exp_fobj Y) :=
  λ (f.2 ∘ eval ∘ ⟨'π1, of_op f.1 ∘ 'π2⟩).
Lemma exp_fmap1 (X : C^op * C) :
  exp_fmap 1 = 1 :> C (exp_fobj X) (exp_fobj X).
Proof.
by rewrite /exp_fmap /= !comp1f -(comp1f 'π1) -{2}(uncurryK 1).
Qed.
Lemma exp_fmapD (X Y Z : C^op * C) (g : Cat.hom _ Y Z) (f : Cat.hom _ X Y) :
  exp_fmap (g ∘ f) = exp_fmap g ∘ exp_fmap f.
Proof.
rewrite /exp_fmap /= comp_curry -!(compA g.2); congr (λ (g.2 ∘ _)).
rewrite -[RHS]compA /=.
rewrite comp_pair pairKL -(compA (of_op g.1)) pairKR.
rewrite split_pair compA.
move: (curryK (f.2 ∘ eval ∘ ⟨'π1, of_op f.1 ∘ 'π2⟩)).
by rewrite /uncurry=> ->; rewrite -!compA comp_pair pairKL -compA pairKR.
Qed.

Definition exp_functor : {functor C^op * C -> C} :=
  Functor exp_fobj exp_fmap exp_fmap1 exp_fmapD.

End CCCatTheory.

Local Notation "X ⇒ Y" := (exp X Y)
  (at level 25, right associativity) : cat_scope.
Local Notation "'λ' f" := (curry f) (at level 0, f at level 9) : cat_scope.

Section CatCCCat.

Universe i j k.
Constraint i <= j.
Constraint j < k.

Program Definition functor_curry
  (C D E : catType@{i j}) (F : {functor C * D -> E})
  : {functor C -> {functor D -> E}} :=
  Functor@{i j}
    (fun X => Functor@{i j}
                (fun Y => F (X, Y))
                (fun Y1 Y2 g => @fmap _ _ F (X, Y1) (X, Y2) (1, g))
                (fun Y => fmap1 F (X, Y)) _)
    (fun X1 X2 f => NatTrans@{i j}
                      (fun Y => @fmap _ _ F (X1, Y) (X2, Y) (f, 1)) _)
    _ _.

Next Obligation.
move=> C D E F X Y1 Y2 Y3 g1 g2 /=.
by rewrite -fmapD prod_cat_compE /= comp1f.
Qed.

Next Obligation.
move=> C D E F X1 X2 f Y1 Y2 g /=; rewrite -2!fmapD.
by do 2![rewrite prod_cat_compE /=]; rewrite !comp1f !compf1.
Qed.

Next Obligation.
move=> C D E F X /=; apply/eq_nat_trans=> Y /=.
by rewrite fmap1.
Qed.

Next Obligation.
move=> C D E F X1 X2 X3 f1 f2 /=; apply/eq_nat_trans=> Y /=.
by rewrite -fmapD prod_cat_compE /= comp1f.
Qed.

Program Definition functor_eval (C D : catType@{i j})
  : {functor {functor C -> D} * C -> D} :=
  Functor (fun FX => FX.1 FX.2)
          (fun FX1 FX2 α => α.1 FX2.2 ∘ fmap FX1.1 α.2) _ _.

Next Obligation. by move=> /= C D [F X]; rewrite comp1f fmap1. Qed.

Next Obligation.
move=> /= C D [F X] [G Y] [H Z] [/= α f] [/= β g].
rewrite fmapD -compA (compA (β Z)) -nt_valP.
by rewrite -compA (compA (α Z)).
Qed.

Arguments functor_eval {_ _}.

Lemma functor_ccCatAxioms@{} : CCCat.axioms_of@{j k} functor_curry (@functor_eval).
Proof.
split.
  move=> /= C D E F; apply/eq_functor=> /=; congr Tagged.
  apply: functional_extensionality_dep=> - [X1 Y1].
  apply: functional_extensionality_dep=> - [X2 Y2].
  apply: functional_extensionality=> - [/= f g].
  by rewrite -fmapD prod_cat_compE /= comp1f compf1.
(* FIXME: This proof is horrible *)
move=> /= C D E F; apply/eq_functor=> /=; apply: eq_Tagged=> /=.
- apply: functional_extensionality=> X.
  apply/eq_functor; congr Tagged=> /=.
  apply: functional_extensionality_dep=> Y1.
  apply: functional_extensionality_dep=> Y2.
  apply: functional_extensionality=> g.
  by rewrite fmap1 /= comp1f.
- case: F=> [/= F0 F1 Fmap1 FmapD] p.
  apply/functional_extensionality_dep=> X1.
  apply/functional_extensionality_dep=> X2.
  apply/functional_extensionality=> g.
  apply/eq_nat_trans=> Y /=.
  rewrite !sapp_cast /=.
  set α := NatTrans _ _.
  rewrite (@cast_sapp (C -> {functor D -> E})
                      (fun F => nat_trans (F X1) (F X2))
                      (fun F => forall Y, E (F X1 Y) (F X2 Y)) _ _ p
                    (fun F => @nt_val D E (F X1) (F X2)) α).
  rewrite /= sapp_cast fmap1 compf1 cast_congr1 /= {α}.
  rewrite (_ : congr1 _ p = congr1 (fun H : C -> D -> E => E (H X1 Y) (H X2 Y))
                                   (congr1 (fun F X => fobj (F X)) p)).
    by move: (congr1 _ p)=> /= => q; rewrite (proof_irrelevance _ q erefl) /=.
  exact: proof_irrelevance.
Qed.

Definition cat_ccCatMixin@{} := CCCatMixin functor_ccCatAxioms.
Canonical cat_ccCatType : ccCatType@{j k} :=
  Eval hnf in CCCatType catType@{i j} functor@{i j} cat_ccCatMixin.

End CatCCCat.

Module ConstCat.

Section ClassDef.

Universe i j.
Constraint i <= j.

(* Ideally, this would say that consts is a functor that is represented by
   C(term, -), but this seems tricky to get right with universes *)

Record mixin_of (C : termCatType@{i j}) := Mixin {
  consts   : C -> Type@{i};
  of_const : forall X, consts X -> C term X;
}.

Record class_of (C : Type@{j}) (hom : C -> C -> Type@{i}) := Class {
  base  : TermCat.class_of hom;
  mixin : mixin_of (TermCat.Pack base)
}.

Record type := Pack {
  obj : Type@{j};
  hom : obj -> obj -> Type@{i};
  _   : class_of hom
}.
Local Coercion obj : type >-> Sortclass.
Local Coercion hom : type >-> Funclass.
Local Coercion base : class_of >-> TermCat.class_of.
Variables (C0 : Type@{j}) (C1 : C0 -> C0 -> Type@{i}) (cC : type).
Definition class := let: Pack _ _ c as cC' := cC return class_of (@hom cC') in c.
Definition clone c of phant_id class c := @Pack C0 C1 c.

Definition catType := @Cat.Pack _ _ class.
Definition termCatType := @TermCat.Pack _ _ class.

Definition pack :=
  [find cc | @TermCat.hom@{i j} cc ~ C1 | "not a termCatType" ]
  [find cb | @TermCat.class@{i j} cc ~ cb ]
  fun m => @Pack C0 C1 (@Class _ _ cb m).

End ClassDef.

Module Exports.
Coercion obj : type >-> Sortclass.
Coercion hom : type >-> Funclass.
Coercion base : class_of >-> TermCat.class_of.
Coercion catType : type >-> Cat.type.
Canonical catType.
Coercion termCatType : type >-> TermCat.type.
Canonical termCatType.
Notation ConstCatMixin := Mixin.
Notation constCatType := type.
Notation ConstCatType C0 C1 m := (@pack C0 C1 _ unify _ unify m).
End Exports.

End ConstCat.

Export ConstCat.Exports.

Section ConstCatTheory.

Universe i j.
Constraint i <= j.

Variable C : constCatType@{i j}.

Definition consts X :=
  @ConstCat.consts@{i j} C (ConstCat.mixin _) X.

Definition of_const X (x : consts X) : C term X :=
  @ConstCat.of_const@{i j} C (ConstCat.mixin _) X x.

Definition const X Y (x : consts Y) : C X Y := of_const x ∘ '!.

End ConstCatTheory.

Section CatConstCat.

Universe i j k.
Constraint i <= j.
Constraint j < k.

Definition cat_consts (C : catType@{i j}) := Cat.obj C.
Program Definition cat_of_consts (C : catType@{i j}) (X : cat_consts C) :
  {functor cat_term@{i j k} -> C} :=
  Functor@{i j} (fun _ => X) (fun _ _ _ => cat_id@{i j} _) (fun _ => erefl) _.

Next Obligation. by move=> C X ????? /=; rewrite comp1f. Qed.

Definition cat_constCatMixin := ConstCatMixin cat_of_consts.

Canonical cat_constCatType : constCatType@{j k} :=
  Eval hnf in ConstCatType catType@{i j} functor@{i j} cat_constCatMixin.

End CatConstCat.

Section FunctorTermCat.

Universe i j.
Constraint i <= j.

Variables (C : catType@{i j}) (D : termCatType@{i j}).

Definition functor_term : {functor C -> D} := const C term.
Program Definition functor_bang (F : {functor C -> D}) : nat_trans F functor_term :=
  NatTrans (fun X => '!) _.
Next Obligation. by move=> F X Y f /=; rewrite [RHS]bangP comp1f. Qed.

Lemma functor_bangP F (α : nat_trans F functor_term) : α = functor_bang F.
Proof. apply/eq_nat_trans=> X /=; exact: bangP. Qed.

Definition functor_termCatMixin :=
  TermCatMixin functor_bangP.
Canonical functor_termCatType : termCatType@{i j} :=
  Eval hnf in TermCatType (functor C D) (@nat_trans C D) functor_termCatMixin.

End FunctorTermCat.

Section FunctorProdCat.

Universe i j.
Constraint i <= j.

Variables (C : catType@{i j}) (D : prodCatType@{i j}).

Definition functor_prod (F G : {functor C -> D}) : {functor C -> D} :=
  prod_functor@{i j} D ∘ ⟨F, G⟩.

Program Definition functor_pair (F G H : {functor C -> D})
  (α : nat_trans H F) (β : nat_trans H G) :
  nat_trans H (functor_prod F G) :=
  NatTrans (fun X => ⟨α X, β X⟩) _.

Next Obligation.
move=> F G H α β X Y f /=; unfold prod_fmap; rewrite /=.
by rewrite comp_pair -!compA pairKL pairKR !nt_valP -comp_pair.
Qed.

Program Definition functor_proj1 (F G : {functor C -> D}) :
  nat_trans (functor_prod F G) F :=
  NatTrans (fun X => 'π1) _.

Next Obligation.
by move=> F G X Y f /=; unfold prod_fmap; rewrite /= pairKL.
Qed.

Program Definition functor_proj2 (F G : {functor C -> D}) :
  nat_trans (functor_prod F G) G :=
  NatTrans (fun X => 'π2) _.

Next Obligation.
by move=> F G X Y f /=; unfold prod_fmap; rewrite /= pairKR.
Qed.

Lemma functor_prodP : ProdCat.axioms_of functor_pair functor_proj1 functor_proj2.
Proof.
split.
- by move=> /= F G H α β; apply/eq_nat_trans=> X /=; rewrite pairKL.
- by move=> /= F G H α β; apply/eq_nat_trans=> X /=; rewrite pairKR.
- move=> /= F G H α β [/eq_nat_trans /= H1 /eq_nat_trans /= H2].
  apply/eq_nat_trans=> X; apply: pairP; split; [exact: H1|exact: H2].
Qed.

Definition functor_prodCatMixin := ProdCatMixin functor_prodP.
Canonical functor_prodCatType : prodCatType@{i j} :=
  Eval hnf in ProdCatType (functor C D) (@nat_trans C D) functor_prodCatMixin.

End FunctorProdCat.

Definition constfun (T S : Type) (x : S) (y : T) := x.

Unset Universe Polymorphism.

Universe u0.
Universe u1.
Constraint u0 < u1.
Notation Type0 := Type@{u0} (only parsing).
Notation Type1 := Type@{u1} (only parsing).

Module Choice.

Variant mixin_of (T : Type0) :=
  Mixin of forall (P : T -> Prop), (exists! x, P x) -> {x : T | P x}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Record type : Type1 := Pack {sort : Type0; base : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type0) (cT : type).

Definition class := let: Pack _ c := cT return class_of cT in c.

Definition clone := fun c & cT -> T & phant_id (@Pack T c) cT => Pack c.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Notation choiceType := type.
Notation ChoiceType T m := (@Pack T m).
Notation "[ 'choiceType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'choiceType'  'of'  T ]") : form_scope.

End Exports.

End Choice.

Export Choice.Exports.

Section ChoiceTheory.

Variables (T : choiceType) (P : T -> Prop).

Lemma choiceP : (exists! x, P x) -> {x : T | P x}.
Proof. by case: (T) P=> [? []]. Qed.

End ChoiceTheory.

Section SubChoice.

Variables (T : choiceType) (P : T -> Prop) (sT : subType P).

Lemma subType_choiceMixin : Choice.mixin_of sT.
Proof.
split=> Q H.
pose PQ x := P x /\ exists Px : P x, Q (Sub _ Px).
have {H} /choiceP [x [Px Qx]] : exists! x, PQ x.
  case: H=> x; elim/SubP: x=> [x Px] [Qx unique_x].
  exists x; repeat split=> //; first by exists Px.
  by move=> y [_ [Py /unique_x /(congr1 val)]]; rewrite !SubK.
exists (Sub x Px).
by case: Qx=> [Px' Qx]; rewrite (proof_irrelevance _ Px Px').
Qed.

Canonical subType_choiceType := ChoiceType sT subType_choiceMixin.

End SubChoice.

Notation "[ 'choiceMixin' 'of' T 'by' <: ]" :=
  (@subType_choiceMixin _ _ [subType of T])
  (at level 0, format "[ 'choiceMixin'  'of'  T  'by'  <: ]") : form_scope.

Lemma unit_choiceMixin : Choice.mixin_of unit.
Proof. by split=> P H; exists tt; case: H=> [[] []]. Qed.

Canonical unit_choiceType :=
  ChoiceType unit unit_choiceMixin.

Section SigChoice.

Variables (T : choiceType) (P : T -> Prop).

Definition sig_choiceMixin := [choiceMixin of {x | P x} by <:].
Canonical sig_choiceType := Eval hnf in ChoiceType {x | P x} sig_choiceMixin.

End SigChoice.

Section CanChoice.

Variables (T : Type) (S : choiceType) (f : T -> S) (g : S -> T).
(* The hypothesis of cancelability is crucial: otherwise we could derive unique
   choice for every type from singleton_of_inj below.  *)
Hypothesis fK : cancel f g.

Lemma CanChoiceMixin : Choice.mixin_of T.
Proof.
split=> P ex.
pose Q y := exists2 x, P x & y = f x.
have {ex} /choiceP [y Qy]: exists! y, Q y.
  case: ex=> [x [Px x_unique]].
  exists (f x); split; first by exists x.
  by move=> _ [x' Px' ->]; rewrite (x_unique _ Px').
by exists (g y); case: Qy => [x Px ->]; rewrite fK.
Qed.

End CanChoice.

Section DFunChoice.

Variables (I : Type) (T_ : I -> choiceType).

Lemma dfun_choiceMixin : Choice.mixin_of (forall i, T_ i).
Proof.
split=> P ex.
pose R i x := forall f, P f -> f i = x.
have ex1 : forall i, exists! x, R i x.
  move=> i.
  case: ex=> f [Pf unique_f].
  exists (f i); split.
  - by move=> g /unique_f ->.
  - by move=> x /(_ _ Pf).
pose f i := sval (choiceP (ex1 i)).
exists f.
case: ex=> g [Pg unique_g].
rewrite (_ : f = g) //.
apply: functional_extensionality_dep=> i.
by move: (svalP (choiceP (ex1 i)) _ Pg)=> ->.
Qed.

Canonical dfun_choiceType :=
  Eval hnf in ChoiceType (dfun T_) dfun_choiceMixin.

End DFunChoice.

Canonical sfun_choiceType T (S : choiceType) :=
  Eval hnf in ChoiceType (sfun T S) (dfun_choiceMixin _).

Section ProdChoice.

Variables T S : choiceType.

Definition prod_choiceMixin :=
  CanChoiceMixin (@dfun_of_prodK _ Choice.sort T S).
Canonical prod_choiceType := Eval hnf in ChoiceType (T * S) prod_choiceMixin.

End ProdChoice.

Section Singletons.

Variable T : Type.

Record subsing := Subsing {
  subsing_val :> T -> Prop;
  _           :  forall x y, subsing_val x -> subsing_val y -> x = y
}.

Canonical subsing_subType := [subType for subsing_val].

Lemma subsingP (X : subsing) x y : X x -> X y -> x = y.
Proof. by case: X => [X]; apply. Qed.

Lemma eq_subsing (X Y : subsing) :
  (forall x, X x <-> Y x) <-> X = Y.
Proof.
split; last by move=> ->.
move=> H; apply: val_inj; apply: functional_extensionality.
by move=> x; apply: propositional_extensionality.
Qed.

Lemma subsing_of_proof (x : T) :
  forall y z, x = y -> x = z -> y = z.
Proof. by move=> ?? <-. Qed.

Definition subsing_of (x : T) :=
  @Subsing (eq x) (@subsing_of_proof x).

Lemma subsing_of_inj : injective subsing_of.
Proof. by move=> x y [->]. Qed.

Lemma in_subsing (X : subsing) (x : T) : X x -> X = subsing_of x.
Proof.
move=> Xx; apply: val_inj; apply: functional_extensionality=> y /=.
apply: propositional_extensionality; split; last by move=> <-.
exact: (valP X) Xx.
Qed.

Lemma subsing_choiceMixin : Choice.mixin_of subsing.
Proof.
split=> P ex.
pose A x := P (subsing_of x).
have unique_A : forall x y, A x -> A y -> x = y.
  case: ex=> [B [PB unique_B]] x y Ax Ay.
  apply: subsing_of_inj.
  by rewrite -(unique_B _ Ax) -(unique_B _ Ay).
pose X : subsing := Subsing unique_A.
exists X.
case ex=> [B [PB unique_B]].
rewrite (_ : X = B) //.
apply: val_inj=> /=.
apply/functional_extensionality=> x.
apply/propositional_extensionality; split.
  by move=> /unique_B ->.
move=> Bx.
rewrite /A (_ : subsing_of x = B) //.
apply/val_inj.
apply/functional_extensionality=> y /=.
apply/propositional_extensionality; split=> [<- //|].
by case: (B) Bx=> /= ?; apply.
Qed.

Canonical subsing_choiceType :=
  Eval hnf in ChoiceType subsing subsing_choiceMixin.

Definition bot_subsing_def (x : T) := False.

Lemma bot_subsing_proof x y : bot_subsing_def x -> bot_subsing_def y -> x = y.
Proof. by []. Qed.

Definition bot_subsing : subsing :=
  Sub bot_subsing_def bot_subsing_proof.

Record sing := Sing {
  sing_val :> subsing;
  _        :  exists x, sing_val x
}.

Canonical sing_subType := [subType for sing_val].
Definition sing_choiceMixin := [choiceMixin of sing by <:].
Canonical sing_choiceType := Eval hnf in ChoiceType sing sing_choiceMixin.

Lemma sing_of_proof (x : T) : exists y, x = y.
Proof. by exists x; split. Qed.

Definition sing_of (x : T) : sing :=
  @Sing (subsing_of x) (sing_of_proof x).

Lemma singleton_of_inj : injective sing_of.
Proof. by rewrite /sing_of=> x y /(congr1 val)/subsing_of_inj. Qed.

End Singletons.

Arguments bot_subsing {_}.
Arguments subsing_of {_}.

Lemma choose (T : choiceType) (X : subsing T) :
  (exists x, X x) -> {x : T | X x}.
Proof.
move=> ex; apply/choiceP.
case: ex=> [x Xx]; exists x; split=> //.
by move=> x'; move: Xx; apply: (valP X).
Qed.

Section SingletonMap.

Variables T S : Type.

Definition liftss_def (f : T -> subsing S) (x : subsing T) (y : S) :=
  exists2 x0, x x0 & f x0 y.

Lemma liftss_proof f x y1 y2 :
  liftss_def f x y1 -> liftss_def f x y2 -> y1 = y2.
Proof.
case=> [x1 x1P1 x1P2] [x2 /(valP x _ _ x1P1) <-].
exact: (valP (f x1)).
Qed.

Definition liftss f x : subsing S :=
  Sub (liftss_def f x) (@liftss_proof f x).

Definition mapss (f : T -> S) := liftss (subsing_of \o f).

End SingletonMap.

Lemma liftss1 T : @liftss T T subsing_of = id.
Proof.
apply/functional_extensionality=> X.
apply/eq_subsing=> x; split; first by case=> y Xy <-.
by move=> ?; exists x.
Qed.

Lemma liftss_comp T S R (f : S -> subsing R) (g : T -> subsing S) :
  liftss f \o liftss g = liftss (liftss f \o g).
Proof.
apply/functional_extensionality=> X; apply/eq_subsing=> z; split.
- by case=> y [x Xx gx] fy; exists x=> //; exists y.
- by case=> x Xx [y gx fy]; exists y=> //; exists x.
Qed.

Lemma liftss_comp1 T S (f : T -> subsing S) : liftss f \o subsing_of = f.
Proof.
apply/functional_extensionality=> /= x.
apply/eq_subsing=> y; split; first by case => _ <-.
by move=> ?; exists x.
Qed.

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

Record mono (T S : poType) := Mono {
  mono_val :> sfun T S;
  _        :  monotone mono_val
}.

Arguments Mono {_ _}.

Definition mono_of (T S : poType) of phant (T -> S) := mono T S.

Canonical mono_subType (T S : poType) :=
  [subType for @mono_val T S].

Notation "{ 'mono' T }" := (mono_of (Phant T))
  (at level 0, format "{ 'mono'  T }") : type_scope.

Identity Coercion mono_of_mono_of : mono_of >-> mono.

Canonical mono_of_subType (T S : poType) :=
  Eval hnf in [subType of {mono T -> S}].

Lemma monoP (T S : poType) (f : {mono T -> S}) : monotone f.
Proof. case: f=> [? fP]; exact: fP. Defined.

Lemma eq_mono (T S : poType) (f g : {mono T -> S}) : f =1 g <-> f = g.
Proof.
split; last by move=> ->.
by move=> e; apply: val_inj; apply: functional_extensionality.
Qed.

Definition mono_comp (T S R : poType) (f : {mono S -> R}) (g : {mono T -> S}) : {mono T -> R} :=
  Eval hnf in Sub (f \o g) (monotone_comp (monoP f) (monoP g)).

Canonical mono_comp.

Lemma mono_compA (A B C D : poType) (f : {mono C -> D}) (g : {mono B -> C}) (h : {mono A -> B}) :
  mono_comp f (mono_comp g h) = mono_comp (mono_comp f g) h.
Proof. exact/val_inj. Qed.

Lemma monotone_id (T : poType) : monotone (@id T).
Proof. by []. Qed.

Definition mono_id (T : poType) : {mono T -> T} :=
  Eval hnf in Sub idfun (@monotone_id T).

Canonical mono_id.

Arguments mono_id {_}.

Lemma mono_comp1f (T S : poType) (f : {mono T -> S}) : mono_comp mono_id f = f.
Proof. by apply: val_inj. Qed.

Lemma mono_compf1 (T S : poType) (f : {mono T -> S}) : mono_comp f mono_id = f.
Proof. by apply: val_inj. Qed.

Definition mono_catMixin := CatMixin (And3 mono_comp1f mono_compf1 mono_compA).
Canonical mono_catType :=
  Eval hnf in CatType poType mono mono_catMixin.

Definition isotone (T S : poType) (f : T -> S) :=
  forall x y, f x ⊑ f y = x ⊑ y.

Lemma iso_mono (T S : poType) (f : T -> S) :
  isotone f -> monotone f.
Proof. by move=> iso_f x y; rewrite iso_f. Qed.

Definition unit_appr (x y : unit) := True.

Lemma unit_apprP : Po.axioms unit_appr.
Proof. by split=> // [] [] []. Qed.

Definition unit_poMixin := PoMixin unit_apprP.

Canonical unit_poType := PoType unit unit_poMixin.

Definition mono_bang (T : poType) : {mono T -> unit} :=
  Sub (fun _ => tt) (fun _ _ _ => I).

Program Definition mono_termCatMixin :=
  @TermCatMixin _ _ unit_poType mono_bang _.

Next Obligation.
move=> T f; apply/eq_mono=> x; by case: (f x).
Qed.

Canonical mono_termCatType :=
  Eval hnf in TermCatType poType mono mono_termCatMixin.

Lemma mono_compE (T S R : poType)
  (f : {mono S -> R}) (g : {mono T -> S}) (x : T)
  : (f ∘ g) x = f (g x).
Proof. by []. Qed.

Lemma monotone_cast T (S : T -> poType) (x y : T) (e : x = y) : monotone (cast S e).
Proof. by case: y / e. Qed.

Definition mono_cast T (S : T -> poType) (x y : T) (e : x = y) : {mono _ -> _} :=
  Eval hnf in Sub (cast S e) (monotone_cast e).

Canonical mono_cast.

Lemma mono_cast1 T (S : T -> poType) (x : T) (e : x = x) :
  mono_cast S e = mono_id.
Proof.
rewrite (proof_irrelevance _ e (erefl x)).
by apply: val_inj.
Qed.

Lemma monotone_const (T S : poType) (x : S) : monotone (@constfun T S x).
Proof. by move=> ???; reflexivity. Qed.

Definition mono_const (T S : poType) (x : S) : {mono T -> S} :=
  Eval hnf in Sub (@constfun T S x) (monotone_const x).
Canonical mono_const.

Lemma mono_comp_constL (T S R : poType) (x : R) (f : {mono T -> S}) :
  mono_const _ x ∘ f = mono_const _ x.
Proof. exact: val_inj. Qed.

Lemma mono_comp_constR (T S R : poType) (f : {mono S -> R}) (x : S) :
  f ∘ mono_const _ x = mono_const T (f x).
Proof. exact: val_inj. Qed.

Section SubPoType.

Variables (T : poType) (P : T -> Prop).

Structure subPoType := SubPoType {
  subPo_sort  :> subType P;
  subPo_mixin :  Po.mixin_of subPo_sort;
  _           :  Po.appr subPo_mixin = fun x y => val x ⊑ val y
}.

Definition subPoType_poType (sT : subPoType) :=
  PoType sT (subPo_mixin sT).

Canonical subPoType_poType.

Definition pack_subPoType U :=
  fun sT cT & sub_sort sT * Po.sort cT -> U * U =>
  fun m     & phant_id m (Po.class cT) => @SubPoType sT m.

Lemma appr_val (sT : subPoType) (x y : sT) : x ⊑ y = val x ⊑ val y.
Proof. by rewrite /appr; case: sT x y=> ? ? /= ->. Qed.

Lemma monotone_val (sT : subPoType) : monotone (@val _ _ sT).
Proof. by move=> x y; rewrite appr_val. Qed.

Definition mono_val' (sT : subPoType) : {mono sT -> T} :=
  Eval hnf in Sub val (@monotone_val sT).

Canonical mono_val'.

Variable sT : subType P.

Lemma sub_apprP : Po.axioms (fun x y : sT => val x ⊑ val y).
Proof.
split.
- by move=> ?; reflexivity.
- by move=> ???; apply: transitivity.
- by move=> x y xy yx; apply: val_inj; apply: appr_anti.
Qed.

Definition SubPoMixin := PoMixin sub_apprP.

End SubPoType.

Arguments monotone_val {_ _ _}.
Arguments mono_val' {_ _ _}.

Coercion subPoType_poType : subPoType >-> poType.

Notation "[ 'poMixin' 'of' T 'by' <: ]" :=
  (SubPoMixin _ : Po.mixin_of T)
  (at level 0, format "[ 'poMixin'  'of'  T  'by'  <: ]") : form_scope.

Notation "[ 'subPoType' 'of' T ]" :=
  (@pack_subPoType _ _ T _ _ id _ id erefl)
  (at level 0, format "[ 'subPoType'  'of'  T ]") : form_scope.

Section CanPo.

Variables (T : Type) (S : poType).
Variables (f : T -> S) (g : S -> T).
Hypothesis fK : cancel f g.

Definition can_appr (x y : T) := f x ⊑ f y.

Lemma can_apprP : Po.axioms can_appr.
Proof.
rewrite /can_appr; split.
- move=> x; reflexivity.
- move=> x y z; exact: transitivity.
- move=> x y xy yx; apply: (can_inj fK).
  exact: appr_anti xy yx.
Qed.

Definition CanPoMixin := PoMixin can_apprP.

End CanPo.

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

Definition unit_ppoMixin := @PpoMixin _ tt (fun _ => I).
Canonical unit_ppoType := Eval hnf in PpoType unit unit_ppoMixin.

Section DFunPo.

Variables (I : Type) (T_ : I -> poType).

Definition fun_appr (f g : forall i, T_ i) := forall i, f i ⊑ g i.

Lemma fun_apprP : Po.axioms fun_appr.
Proof.
split.
- by move=> f i; reflexivity.
- by move=> f g h fg gh i; move: (fg i) (gh i); apply: transitivity.
- move=> f g fg gf; apply: functional_extensionality_dep=> i.
  apply: appr_anti; [exact: fg|exact: gf].
Qed.

Definition dfun_poMixin := PoMixin fun_apprP.
Canonical dfun_poType := Eval hnf in PoType (dfun T_) dfun_poMixin.

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

Lemma bot_subsingP X : bot_subsing ⊑ X.
Proof. by move=> x []. Qed.

Definition subsing_ppoMixin := PpoMixin bot_subsingP.
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

Definition pcpo_catMixin := BaseChangeCatMixin _ Pcpo.cpoType.
Canonical pcpo_catType :=
  Eval hnf in CatType pcpoType _ pcpo_catMixin.

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
Canonical mono_cont_compp.
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
Definition pcpo_contP : @Cat.axioms pcpoType pcpo_cont
                                    (fun T S R f g => f ∘ g)
                                    (fun T => 1).
Proof.
by split; move=> *; rewrite ?comp1f ?compf1 ?compA.
Qed.

Definition pcpo_cont_catMixin := CatMixin pcpo_contP.
Canonical pcpo_cont_catType :=
  Eval hnf in CatType pcpoType pcpo_cont pcpo_cont_catMixin.

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
Canonical cont_compp.
Arguments cont_compp {_ _ _}.

Definition mapp (T1 S1 T2 S2 : Type) (f1 : T1 -> S1) (f2 : T2 -> S2) :=
  fun x : T1 * T2 => (f1 x.1, f2 x.2).

Lemma monotone_mapp (T1 S1 T2 S2 : poType) (f1 : {mono T1 -> S1}) (f2 : {mono T2 -> S2}) :
  monotone (mapp f1 f2).
Proof.
by case=> [x1 y1] [x2 y2] [/= x12 y12]; split;
[apply: (valP f1 _ _ x12)|apply: (valP f2 _ _ y12)].
Qed.

Definition mono_mapp (T1 S1 T2 S2 : poType)
  (f1 : {mono T1 -> S1}) (f2 : {mono T2 -> S2}) : {mono _ -> _} :=
  Eval hnf in Sub (mapp f1 f2) (monotone_mapp f1 f2).
Canonical mono_mapp.

Lemma continuous_mapp (T1 S1 T2 S2 : cpoType)
  (f1 : {cont T1 -> S1}) (f2 : {cont T2 -> S2}) :
  continuous (mono_mapp f1 f2).
Proof.
move=> /= x; rewrite /mapp -2!contP {1}/sup /= /prod_sup.
congr (sup _, sup _); exact/eq_mono.
Qed.

Definition cont_mapp (T1 S1 T2 S2 : cpoType)
  (f1 : {cont T1 -> S1}) (f2 : {cont T2 -> S2}) :
  {cont T1 * T2 -> S1 * S2} :=
  Sub (mono_mapp f1 f2) (continuous_mapp f1 f2).
Canonical cont_mapp.

Definition cont2_mapp_def (T1 S1 T2 S2 : cpoType)
  (f : {cont T1 -> S1} * {cont T2 -> S2}) :
  {cont T1 * T2 -> S1 * S2} :=
  cont_mapp f.1 f.2.

Lemma monotone_cont2_mapp_def (T1 S1 T2 S2 : cpoType) :
  monotone (@cont2_mapp_def T1 S1 T2 S2).
Proof.
move=> /= [f1 g1] [f2 g2] [/= f12 g12] [x1 y1] /=; rewrite /mapp /=.
split; [exact: f12|exact: g12].
Qed.

Definition mono_cont2_mapp_def (T1 S1 T2 S2 : cpoType) :
  {mono {cont T1 -> S1} * {cont T2 -> S2} ->
        {cont T1 * T2 -> S1 * S2}} :=
  Sub (@cont2_mapp_def T1 S1 T2 S2) (@monotone_cont2_mapp_def T1 S1 T2 S2).
Canonical mono_cont2_mapp_def.

Lemma continuous_cont2_mapp_def (T1 S1 T2 S2 : cpoType) :
  continuous (@mono_cont2_mapp_def T1 S1 T2 S2).
Proof.
apply/continuous2P; split.
- move=> /= f g; apply/eq_cont=> /= p.
  congr (sup _, _); first by apply/eq_mono.
  by rewrite -[LHS]sup_const; congr sup; apply/eq_mono.
- move=> /= f g; apply/eq_cont=> /= p.
  congr (_, sup _); last by apply/eq_mono.
  by rewrite -[LHS]sup_const; congr sup; apply/eq_mono.
Qed.

Definition cont2_mapp (T1 S1 T2 S2 : cpoType) :
  {cont {cont T1 -> S1} * {cont T2 -> S2} ->
        {cont T1 * T2 -> S1 * S2}} :=
  Sub (@mono_cont2_mapp_def T1 S1 T2 S2)
      (@continuous_cont2_mapp_def T1 S1 T2 S2).
Canonical cont2_mapp.
Arguments cont2_mapp {_ _ _ _}.

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
  have {fXE} fXE: forall m, exists x, (Subsing (Pss m)) x.
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

Section InverseLimit.

Variable T : nat -> cpoType.
Variable p : forall n, {cont T n.+1 -> T n}.

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

End InverseLimit.

Arguments InvLim {_ _} _ _.

Section Retractions.

Definition retraction (T S : cpoType) (p : {cont T -> S}) (e : {cont S -> T}) :=
  p ∘ e = 1 /\ e ∘ p ⊑ 1.

Record retr (T S : cpoType) := Retr {
  retr_val : {cont T -> S} * {cont S -> T};
  _        : retraction retr_val.1 retr_val.2
}.

Definition retr_of (T S : cpoType) of phant (T -> S) := retr T S.
Identity Coercion retr_of_retr_of : retr_of >-> retr.

Canonical retr_subType (T S : cpoType) :=
  [subType for @retr_val T S].
Notation "{ 'retr' T }" := (retr_of (Phant T))
  (at level 0, format "{ 'retr'  T }") : type_scope.
Canonical retr_of_subType (T S : cpoType) :=
  Eval hnf in [subType of {retr T -> S}].
Definition retr_choiceMixin (T S : cpoType) :=
  [choiceMixin of {retr T -> S} by <:].
Canonical retr_choiceType (T S : cpoType) :=
  Eval hnf in ChoiceType (retr T S) (retr_choiceMixin T S).
Canonical retr_of_choiceType (T S : cpoType) :=
  Eval hnf in ChoiceType {retr T -> S} (retr_choiceMixin T S).

Lemma retractionA (T S : cpoType) (p : {cont T -> S}) (e : {cont S -> T}) x y :
  retraction p e -> e x ⊑ y <-> x ⊑ p y.
Proof.
case=> eK pD; split.
- by move=> /(monoP p); rewrite /= -cont_compE eK.
- by move=> /(monoP e) /= H; apply: transitivity H (pD _).
Qed.

Lemma embedding_iso (T S : cpoType) (p : {cont T -> S}) (e : {cont S -> T}) x y :
  retraction p e -> e x ⊑ e y -> x ⊑ y.
Proof.
by case=> eK _ /(monoP p); rewrite /= -2!cont_compE eK.
Qed.

Lemma embedding_unique (T S : cpoType) (p : {cont T -> S}) (e1 e2 : {cont S -> T}) :
  retraction p e1 -> retraction p e2 -> e1 = e2.
Proof.
move=> e1P e2P; apply: appr_anti.
- rewrite -[e1]compf1 -[e2]comp1f -(proj1 e2P) compA.
  apply: monotone_cont_comp; [apply: (proj2 e1P)|reflexivity].
- rewrite -[e2]compf1 -[e1]comp1f -(proj1 e1P) compA.
  apply: monotone_cont_comp; [apply: (proj2 e2P)|reflexivity].
Qed.

Definition retr_retr (T S : cpoType) (p : retr T S) : {cont T -> S} :=
  (val p).1.

Coercion retr_retr : retr >-> cont_of.

Definition retr_emb (T S : cpoType) (p : {retr T -> S}) : {cont S -> T} :=
  (val p).2.

Notation "p '^e'" := (retr_emb p) (at level 9, format "p ^e").

Lemma retrP (T S : cpoType) (p : {retr T -> S}) : retraction p p^e.
Proof. exact: (valP p). Qed.

Lemma retr_retr_inj (T S : cpoType) : injective (@retr_retr T S).
Proof.
rewrite /retr_retr=> p1 p2 p12; apply: val_inj=> /=.
case: p1 p2 p12=> [[p1 e1] /= e1P] [[p2 e2] /= e2P] /= p12.
by rewrite -p12 in e2P *; rewrite (embedding_unique e1P e2P).
Qed.

Lemma eq_retr (T S : cpoType) (p1 p2 : {retr T -> S}) : p1 =1 p2 <-> p1 = p2.
Proof.
split; last by move=> ->.
by move=> H; apply: retr_retr_inj; apply/eq_cont.
Qed.

Variables T S R : cpoType.

Lemma embK (p : {retr T -> S}) : cancel p^e p.
Proof.
by move=> x; rewrite -cont_compE (proj1 (retrP p)).
Qed.

Lemma retrD (p : {retr T -> S}) x : p^e (p x) ⊑ x.
Proof. exact: (proj2 (retrP p)). Qed.

Lemma retrA (p : {retr T -> S}) x y : p^e x ⊑ y <-> x ⊑ p y.
Proof. by apply: retractionA; apply: retrP. Qed.

Lemma retraction_id : retraction (@cont_id T) (@cont_id T).
Proof.
by split; first apply/eq_cont; move=> x; reflexivity.
Qed.

Definition retr_id : {retr T -> T} :=
  Eval hnf in Sub (cont_id, cont_id) retraction_id.

Lemma retraction_comp (p1 : {cont S -> R}) (e1 : {cont R -> S})
                      (p2 : {cont T -> S}) (e2 : {cont S -> T}) :
  retraction p1 e1 -> retraction p2 e2 -> retraction (p1 ∘ p2) (e2 ∘ e1).
Proof.
move=> [e1K p1D] [e2K p2D]; split.
  by rewrite -compA (compA p2) e2K comp1f e1K.
apply: transitivity p2D.
rewrite -{2}[p2]comp1f -compA (compA e1).
apply: monotone_cont_comp; first reflexivity.
apply: monotone_cont_comp; by [|reflexivity].
Qed.

Definition retr_comp (p1 : {retr S -> R}) (p2 : {retr T -> S}) : {retr T -> R} :=
  Eval hnf in Sub (cont_comp p1 p2, cont_comp p2^e p1^e)
                  (retraction_comp (retrP p1) (retrP p2)).

End Retractions.

Notation "{ 'retr' T }" := (retr_of (Phant T))
  (at level 0, format "{ 'retr'  T }") : type_scope.
Notation "p '^e'" := (retr_emb p) (at level 9, format "p ^e") : cpo_scope.

Arguments retr_id {_}.

Lemma retr_compA (A B C D : cpoType) (f : {retr C -> D}) (g : {retr B -> C}) (h : {retr A -> B}) :
  retr_comp f (retr_comp g h) = retr_comp (retr_comp f g) h.
Proof.
by apply: val_inj; rewrite /= cont_compA cont_compA.
Qed.

Lemma retr_compf1 (A B : cpoType) (f : {retr A -> B}) : retr_comp f retr_id = f.
Proof.
by case: f=> [[??] ?]; apply: val_inj; rewrite /= cont_compf1 cont_comp1f.
Qed.

Lemma retr_comp1f (A B : cpoType) (f : {retr A -> B}) : retr_comp retr_id f = f.
Proof.
by case: f=> [[??] ?]; apply: val_inj; rewrite /= cont_comp1f cont_compf1.
Qed.

Definition retr_catMixin := CatMixin (And3 retr_comp1f retr_compf1 retr_compA).
Canonical retr_catType := Eval hnf in CatType cpoType retr retr_catMixin.

Lemma embD (T S R : cpoType) (p1 : {retr S -> R}) (p2 : {retr T -> S}) :
  (p1 ∘ p2)^e = p2^e ∘ p1^e.
Proof. by []. Qed.

Section BiLimit.

Variables (T : nat -> cpoType) (p : forall n, {retr T n.+1 -> T n}).

Fixpoint down n m : {retr T (m + n) -> T n} :=
  match m with
  | 0    => 1
  | m.+1 => down n m ∘ p (m + n)
  end.

Lemma downSn n m x : p n (down n.+1 m x) = down n m.+1 (cast T (addnS _ _) x).
Proof.
elim: m x=> [|m IH] /=; first by move=> x; rewrite eq_axiomK.
move=> x; rewrite IH /=; congr (down _ _ (p _ _)).
move: (addnS m n) (addnS m.+1 n) x; rewrite -![m.+1 + _]/((m + _).+1).
move: (m + n.+1) (m + n).+1=> a b q.
by case: b / q=> q x /=; rewrite eq_axiomK.
Qed.

Definition downl n m (nm : n <= m) : {retr T m -> T n} :=
  cast (fun m => {retr T m -> T n}) (subnK nm) (down _ _).

Lemma downlS n m (nm : n <= m) (nm1 : n <= m.+1) :
  downl nm1 = retr_comp (downl nm) (p m).
Proof.
rewrite /downl.
move: (subnK nm) (subnK nm1); rewrite (subSn nm) /=.
move: {nm nm1} (m - n)=> o; rewrite -[o.+1 + n]/(o + n).+1 => e.
by case: m / e => ?; rewrite eq_axiomK.
Qed.

Lemma downl0 n (nn : n <= n) : downl nn = 1.
Proof.
by rewrite /downl; move: (subnK nn); rewrite subnn=> e; rewrite eq_axiomK.
Qed.

Lemma downl1 n (nSn : n <= n.+1) : downl nSn = p n.
Proof. by rewrite (downlS (leqnn n) nSn) downl0 retr_comp1f. Qed.

Lemma downlD n m o (nm : n <= m) (mo : m <= o) :
  downl (leq_trans nm mo) = downl nm ∘ downl mo.
Proof.
move: (mo) (leq_trans _ _); rewrite -(subnK mo) {mo}.
elim: (o - m)=> {o} [|o IH] /=.
  move=> mo no; rewrite /downl; move: (subnK mo).
  rewrite -![0 + m]/(m) subnn => {mo} mo; rewrite eq_axiomK /= compf1.
  by rewrite (eq_irrelevance no nm).
rewrite -![o.+1 + _]/(o + _).+1 => mo no.
rewrite (downlS (leq_trans nm (leq_addl o m)) no).
rewrite (IH (leq_addl o m) (leq_trans nm (leq_addl o m))).
by rewrite (downlS (leq_addl o m) mo) compA.
Qed.

Definition inlim_def n (x : T n) m : T m :=
  downl (leq_addr n m) ((downl (leq_addl m n))^e x).

Lemma inlim_defEL n (x : T n) m (nm : n <= m) : inlim_def x m = (downl nm)^e x.
Proof.
rewrite /inlim_def.
rewrite (eq_irrelevance (leq_addl m n) (leq_trans nm (leq_addr n m))).
by rewrite downlD embD /= embK.
Qed.

Lemma inlim_defER n (x : T n) m (mn : m <= n) : inlim_def x m = downl mn x.
Proof.
rewrite /inlim_def.
rewrite (eq_irrelevance (leq_addr n m) (leq_trans mn (leq_addl m n))).
by rewrite downlD /= embK.
Qed.

Lemma inlim_proof n (x : T n) m : inlim_def x m = p m (inlim_def x m.+1).
Proof.
case: (leqP n m)=> [nm|mn].
- rewrite (inlim_defEL _ nm) (inlim_defEL _ (leq_trans nm (leqnSn m))).
  by rewrite downlD embD downl1 /= embK.
- rewrite (inlim_defER _ mn) (inlim_defER _ (leq_trans (leqnSn m) mn)).
  by rewrite downlD downl1.
Qed.

Definition inlim n x : invlim p :=
  InvLim (@inlim_def n x) (@inlim_proof n x).

Lemma monotone_inlim n : monotone (@inlim n).
Proof.
move=> x y xy m; rewrite /= /inlim_def /=.
apply: (valP (val (retr_retr (downl _)))).
exact: (valP (val (downl _)^e)) xy.
Qed.

Definition mono_inlim n : {mono T n -> invlim p} :=
  Sub (@inlim n) (@monotone_inlim n).

Lemma continuous_inlim n : continuous (mono_inlim n).
Proof.
apply: continuous_valV; move=> x /=.
apply: functional_extensionality_dep=> m.
rewrite /inlim_def -2!contP; congr sup.
by apply: val_inj; apply: functional_extensionality=> k.
Qed.

Definition cont_inlim n : {cont T n -> invlim p} :=
  Sub (mono_inlim n) (@continuous_inlim n).

Definition outlim n (x : invlim p) : T n := val x n.

Lemma up_outlim n m x : (down n m)^e (outlim _ x) ⊑ outlim _ x.
Proof.
elim: m=> [|m IH /=]; first by reflexivity.
apply: transitivity (valP (val (p (m + n))^e) _ _ IH) _.
rewrite /outlim (valP x) /=; exact: retrD.
Qed.

Lemma down_outlim n m x : down n m (outlim _ x) = outlim _ x.
Proof.
elim: m=> [//|m IH /=]; by rewrite -(valP x (m + n)) -IH.
Qed.

Lemma downlE_outlim n m x (nm : n <= m) :
  (downl nm)^e (outlim _ x) ⊑ outlim _ x.
Proof.
rewrite /downl; move: (m - n) (subnK _)=> k e.
case: m / e {nm} => /=; exact: up_outlim.
Qed.

Lemma downl_outlim n m x (mn : m <= n) : downl mn (outlim _ x) = outlim _ x.
Proof.
rewrite /downl; move: (n - m) (subnK _)=> k e.
case: n / e {mn} => /=; exact: down_outlim.
Qed.

Lemma monotone_outlim n : monotone (outlim n).
Proof. by move=> x y; rewrite appr_val => /(_ n). Qed.

Definition mono_outlim n : {mono invlim p -> T n} :=
  Sub (outlim n) (monotone_outlim n).

Lemma continuous_outlim n : continuous (mono_outlim n).
Proof.
move=> /= x; rewrite /outlim /= [RHS]/sup /= /dfun_sup /=.
by congr sup; apply: val_inj.
Qed.

Definition cont_outlim n : {cont invlim p -> T n} :=
  Sub (mono_outlim n) (continuous_outlim n).

Lemma retraction_outlim n : retraction (cont_outlim n) (cont_inlim n).
Proof.
split.
  apply/eq_cont=> x /=.
  by rewrite /inlim /outlim /= (inlim_defER _ (leqnn n)) downl0.
move=> /= x; rewrite appr_val /=; move=> m.
case: (leqP n m)=> [nm|/ltnW mn].
  by rewrite (inlim_defEL _ nm); apply: downlE_outlim.
rewrite (inlim_defER _ mn) downl_outlim; reflexivity.
Qed.

Definition retr_outlim n : {retr invlim p -> T n} :=
  Sub (cont_outlim n, cont_inlim n) (retraction_outlim n).

Lemma retr_outlimS n : retr_outlim n = p n ∘ retr_outlim n.+1.
Proof. apply/eq_retr=> /= x; exact: (valP x). Qed.

Lemma downl_retr_outlim n m (nm : n <= m) :
  retr_outlim n = downl nm ∘ retr_outlim m.
Proof. by apply/eq_retr=> x /=; rewrite downl_outlim. Qed.

Lemma emb_outlim n : (retr_outlim n)^e = cont_inlim n.
Proof. by []. Qed.

Definition proj n : {cont invlim p -> invlim p} :=
  cont_inlim n ∘ cont_outlim n.

Lemma projI n m : proj n ∘ proj m = proj (minn n m).
Proof.
apply/eq_cont=> /= x; apply: val_inj.
rewrite /minn; case: ltnP=> [nm|mn] /=.
  suffices -> : outlim n (inlim (outlim m x)) = outlim n x by [].
  by rewrite {1}/outlim /= (inlim_defER _ (ltnW nm)) downl_outlim.
move: (outlim m x)=> {x} x.
rewrite /outlim /= (inlim_defEL _ mn).
apply: functional_extensionality_dep=> k.
case: (leqP k m)=> [km|/ltnW mk].
  rewrite (inlim_defER _ km) (inlim_defER _ (leq_trans km mn)).
  by rewrite downlD /= embK.
rewrite (inlim_defEL _ mk); case: (leqP k n)=> [kn|/ltnW nk].
  rewrite (inlim_defER _ kn).
  by rewrite (eq_irrelevance mn (leq_trans mk kn)) downlD embD /= embK.
rewrite (inlim_defEL _ nk) (eq_irrelevance mk (leq_trans mn nk)).
by rewrite downlD.
Qed.

Lemma leq_proj_id n : proj n ⊑ 1.
Proof. exact: (retrD (retr_outlim n)). Qed.

Lemma monotone_proj : monotone proj.
Proof.
move=> /= n m /minn_idPr <-; rewrite -projI=> x /=.
exact: (monoP (proj m) (leq_proj_id n x)).
Qed.

Definition mono_proj : {mono nat -> {cont invlim p -> invlim p}} :=
  Sub proj monotone_proj.
Canonical mono_proj.

Lemma sup_proj : sup mono_proj = 1.
Proof.
apply: sup_unique; split; first exact: leq_proj_id.
move=> /= f ub_f; move=> /= x; move=> /= n.
move: (ub_f n x n)=> /=.
by rewrite (inlim_defER _ (leqnn n)) downl0.
Qed.

End BiLimit.

Section BiLimitPointed.

Variables (T : nat -> pcpoType) (p : forall n, {retr T n.+1 -> T n}).

Program Definition invlim_bot : invlim p :=
  InvLim (fun _ => ⊥) _.

Next Obligation.
move=> n /=; apply: appr_anti; first exact: botP.
rewrite -(embK (p n) ⊥); apply: monoP; exact: botP.
Qed.

Lemma invlim_botP x : invlim_bot ⊑ x.
Proof. move=> y; exact: botP. Qed.

Definition invlim_ppoMixin := PpoMixin invlim_botP.
Canonical invlim_ppoType := Eval hnf in PpoType (invlim p) invlim_ppoMixin.
Canonical invlim_pcpoType := Eval hnf in PcpoType (invlim p).

End BiLimitPointed.

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

Definition monotone_cpo_comp X Y Z :
  monotone (fun fg : C Y Z * C X Y => fg.1 ∘ fg.2 : C _ _) :=
  @CpoCat.comp_mono _ (CpoCat.mixin (CpoCat.class C)) X Y Z.

Definition continuous_cpo_comp X Y Z :
  continuous (Mono _ (@monotone_cpo_comp X Y Z)) :=
  @CpoCat.comp_cont _ (CpoCat.mixin (CpoCat.class C)) X Y Z.

Lemma continuous_cpo_compL X Y Z (f : {mono nat -> C Y Z}) (g : C X Y) :
  sup f ∘ g = sup (Mono _ (@monotone_cpo_comp X Y Z) ∘ ⟨f, mono_const _ g⟩).
Proof.
by case/continuous2P: (@continuous_cpo_comp X Y Z)=> [/(_ f g)].
Qed.

Lemma continuous_cpo_compR X Y Z (f : C Y Z) (g : {mono nat -> C X Y}) :
  f ∘ sup g = sup (Mono _ (@monotone_cpo_comp X Y Z) ∘ ⟨mono_const _ f, g⟩).
Proof.
by case/continuous2P: (@continuous_cpo_comp X Y Z)=> [_ /(_ f g)].
Qed.

End CpoCatTheory.

Section CpoCpoCat.

Definition cpo_cpoCatMixin :=
  @CpoCatMixin cont_catType (fun T S => Cpo.class (cont_cpoType T S))
               monotone_cont_compp continuous_cont_compp.

Canonical cpo_cpoCatType :=
  Eval hnf in CpoCatType cpoType cont cpo_cpoCatMixin.

Definition pcpo_cpoCatMixin :=
  @CpoCatMixin pcpo_catType (fun T S => Cpo.class (cont_cpoType T S))
               monotone_cont_compp continuous_cont_compp.

Canonical pcpo_cpoCatType :=
  Eval hnf in CpoCatType pcpoType (fun T S => cont T S) pcpo_cpoCatMixin.

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
case=> [[/= fh1 gk1] [/= fh2 gk2]]; split=> /=.
- by apply: (@monotone_cpo_comp _ _ _ _ (f1, f2) (h1, h2)); split.
- by apply: (@monotone_cpo_comp _ _ _ _ (g1, g2) (k1, k2)); split.
Qed.

Next Obligation.
case=> /= [T1 T2] [S1 S2] [R1 R2]; apply/continuous2P; split=> /=.
- move=> fg [/= h k]; congr pair=> /=;
  by rewrite continuous_cpo_compL; congr sup; apply/eq_mono.
- move=> [/= f g] hk; congr pair=> /=;
  by rewrite continuous_cpo_compR; congr sup; apply/eq_mono.
Qed.

Canonical prod_cat_cpoCatType :=
  Eval hnf in CpoCatType (C * D) (prod_cat_hom C D) prod_cat_cpoCatMixin.

End ProdCpoCat.

Section CpoFunctor.

Implicit Types C D E : cpoCatType.

Record cpo_functor C D := CpoFunctor {
  cpo_f_val :> {functor C -> D};
  cpo_fmap_mono : forall X Y, monotone (@fmap _ _ cpo_f_val X Y);
  cpo_fmap_cont : forall X Y, continuous (Mono _ (@cpo_fmap_mono X Y))
}.

Lemma cpo_f_val_inj C D : injective (@cpo_f_val C D).
Proof.
case=> [/= F Fmono Fcont] [/= G Gmono Gcont] e.
move: Gmono Gcont; rewrite -{}e {G} => Gmono.
rewrite -(proof_irrelevance _ Fmono Gmono) => Gcont.
by rewrite -(proof_irrelevance _ Fcont Gcont).
Qed.

Definition cpo_functor_id C : cpo_functor C C :=
  @CpoFunctor _ _ 1
    (fun X Y => @monotone_id [poType of C X Y])
    (fun X Y => @continuous_id [cpoType of C X Y]).

Definition cpo_functor_comp C D E (F : cpo_functor D E) (G : cpo_functor C D) :
  cpo_functor C E :=
  @CpoFunctor _ _ (cpo_f_val F ∘ cpo_f_val G)
    (fun X Y => monotone_comp (@cpo_fmap_mono _ _ F _ _) (@cpo_fmap_mono _ _ G X Y))
    (fun X Y => continuous_comp (@cpo_fmap_cont _ _ F _ _) (@cpo_fmap_cont _ _ G X Y)).

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

Notation "{ 'cpo_functor' T }" := (cpo_functor_of _ _ (Phant T))
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
                           (Mono _ (@cpo_fmap_mono _ _ F _ _))
                           (Mono _ (@cpo_fmap_mono _ _ G _ _)))
             (fun X Y => @continuous_pairf
                           _ _ _
                           (Cont _ (@cpo_fmap_cont _ _ F _ _))
                           (Cont _ (@cpo_fmap_cont _ _ G _ _))).

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
by apply: monotone_cpo_comp; split=> //; reflexivity.
Qed.

Next Obligation.
move=> /= T S; move=> /= x.
rewrite continuous_cont_compR -contP; congr sup.
by apply/eq_mono.
Qed.

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

Definition chain_mor0_def : {cont 'X_1 -> 'X_0} * {cont 'X_0 -> 'X_1} :=
  (⊥, ⊥).

Lemma chain_mor0_proof : retraction chain_mor0_def.1 chain_mor0_def.2.
Proof.
split.
- apply/eq_cont; move=> /= x; apply: val_inj.
  by apply: functional_extensionality=> - [].
- by move=> x; rewrite /= /constfun /=; apply: botP.
Qed.

Definition chain_mor0 : {retr 'X_1 -> 'X_0} :=
  Sub chain_mor0_def chain_mor0_proof.

Lemma f_emb_proof (T S : pcpoType) (f : {retr T -> S}) :
  retraction (fmap F (f^e, retr_retr f)) (fmap F (retr_retr f, f^e)).
Proof.
split; rewrite -pcpo_compE -fmapD prod_cat_compE /=.
  by rewrite op_compE /of_op pcpo_compE (proj1 (retrP f)) fmap1.
(* FIXME: SSR rewrite does not work here *)
change 1 with (@cat_id pcpo_cpoCatType (F (T, T))).
rewrite -fmap1; apply: (cpo_fmap_mono F); split; exact: (proj2 (retrP f)).
Qed.

Definition f_emb (T S : pcpoType) (f : {retr T -> S}) : {retr F (Op T, T) -> F (Op S, S)} :=
  Sub (fmap F (f^e, retr_retr f), fmap F (retr_retr f, f^e))
      (@f_emb_proof T S f).

Lemma f_emb1 (T : pcpoType) : f_emb 1 = 1 :> {retr F (Op T, T) -> F (Op T, T)}.
Proof.
by apply/eq_retr=> x; rewrite /f_emb /= /retr_retr /= fmap1.
Qed.

Lemma f_embD (T S R : pcpoType) (f : {retr S -> R}) (g : {retr T -> S}) :
  f_emb (f ∘ g) = f_emb f ∘ f_emb g.
Proof.
apply: retr_retr_inj; unfold comp, f_emb, retr_retr; simpl.
by rewrite fmapD.
Qed.

Fixpoint chain_mor n : {retr 'X_n.+1 -> 'X_n} :=
  match n with
  | 0    => chain_mor0
  | n.+1 => f_emb (chain_mor n)
  end.

Definition mu := [pcpoType of invlim chain_mor].

Lemma chain_mor_outlim n :
  chain_mor n ∘ retr_outlim chain_mor n.+1 =
  retr_outlim chain_mor n.
Proof. by case: n=> [|n] /=; rewrite [RHS]retr_outlimS. Qed.

Definition f_proj n : {retr F (Op mu, mu) -> 'X_n} :=
  match n return {retr F (Op mu, mu) -> 'X_n} with
  | 0    => chain_mor 0 ∘ f_emb (retr_outlim chain_mor 0)
  | n.+1 => f_emb (retr_outlim chain_mor n)
  end.

Lemma f_emb_downl n m (nm : n <= m) :
  f_emb (downl chain_mor nm) = downl chain_mor (nm : n.+1 <= m.+1).
Proof.
move: (nm); rewrite /= -(subnK nm).
elim: (m - n)=> {m nm} [|m IH] /= nm.
  by rewrite !downl0 f_emb1.
rewrite {1}(eq_irrelevance nm (leq_trans (leq_addl m n) (leqnSn (m + n)))).
rewrite !downlD f_embD {}IH downl1.
pose a : n.+1 <= m.+1 + n := leq_addl m n.
rewrite (eq_irrelevance nm (leq_trans a (leqnSn (m.+1 + n)))).
by rewrite downlD downl1.
Qed.

Lemma downl_f_proj n m (nm : n <= m) : f_proj n = downl chain_mor nm ∘ f_proj m.
Proof.
case: n nm=> [|n] /= nm.
  apply/eq_retr=> x /=; apply: val_inj.
  by apply: functional_extensionality; case.
case: m nm => [|m] //= nm.
rewrite (downl_retr_outlim _ (@leq_trans m _ _ nm (leqnSn m))) downlD downl1.
by rewrite -compA f_embD chain_mor_outlim f_emb_downl.
Qed.

Lemma roll_proof n : f_proj n =1 chain_mor n ∘ f_proj n.+1.
Proof.
apply/eq_retr.
by case: n=> [|n] //=; rewrite -f_embD chain_mor_outlim.
Qed.

(* FIXME: This does not work with Sub *)
Definition roll (x : F (Op mu, mu)) : mu :=
  @InvLim _ _ (f_proj^~ x) (fun n => roll_proof n x).

Lemma monotone_roll : monotone roll.
Proof.
move=> x y xy; move=> n /=; exact: (monoP (f_proj n) xy).
Qed.

Definition mono_roll : {mono F (Op mu, mu) -> mu} :=
  Sub roll monotone_roll.

Lemma continuous_roll : continuous mono_roll.
Proof.
move=> x; apply: val_inj; apply: functional_extensionality_dep=> n /=.
rewrite {1}/sup /= -(contP (f_proj n)); congr sup; exact: val_inj.
Qed.

Definition cont_roll : {cont F (Op mu, mu) -> mu} :=
  Sub mono_roll continuous_roll.

Lemma unroll_proof :
  monotone (fun n => (f_proj n)^e ∘ cont_outlim chain_mor n).
Proof.
move=> n m nm.
rewrite (downl_f_proj nm) embD -compA.
apply: monotone_cont_comp; first reflexivity.
move=> x; exact: downlE_outlim.
Qed.

Definition unroll : {cont mu -> F (Op mu, mu)} := sup (Mono _ unroll_proof).

Lemma unrollK : cont_roll ∘ unroll = 1.
Proof.
rewrite /unroll continuous_cont_compR.
apply: sup_unique; split.
  move=> n /=; move=> x /=; move=> m /=.
  case: (leqP n m)=> [nm|/ltnW mn].
    rewrite (downl_f_proj nm) embD embK /=.
    exact: downlE_outlim.
  rewrite (downl_f_proj mn) /= embK downl_outlim; reflexivity.
move=> /= f ub_f; move=> x /=; move=> n /=.
by move: (ub_f n x n)=> /=; rewrite embK.
Qed.

Lemma rollK : unroll ∘ cont_roll = 1.
Proof.
rewrite /unroll continuous_cont_compL /= -[RHS](fmap1 F) /=.
change 1 with (cat_id (Pcpo.cpoType mu), cat_id (Pcpo.cpoType mu)); rewrite -sup_proj.
rewrite -sup_pairf.
change (fmap F (sup (mono_pairf (mono_proj chain_mor) (mono_proj chain_mor))))
  with (Mono _ (@cpo_fmap_mono _ _ F (Op mu, mu) (Op mu, mu))
             (sup (mono_pairf (mono_proj chain_mor) (mono_proj chain_mor)))).
rewrite -cpo_fmap_cont -(sup_shift _ 1); congr sup; apply/eq_mono=> /= n /=.
apply/eq_cont=> x /=; rewrite /outlim; unfold pairf; simpl.
by rewrite /f_emb /= /proj fmapD.
Qed.

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

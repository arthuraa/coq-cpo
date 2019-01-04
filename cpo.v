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

- Test whether wrapping functions in a definition helps with canonical structure
  inference.

- Fix canonical structure inference for mono, cont and friends.

- Better naming conventions for mono, cont, etc instances.

- Use mixins to define subtyping

*)

Obligation Tactic := idtac.
Definition phant_id_err {T1 T2} (t1 : T1) (t2 : T2) (s : string) :=
  phantom T1 t1 -> phantom T2 t2.
Definition unify {T} {t : T} (x : phantom T t) := x.
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

Definition dfun T (S : T -> Type) := forall x, S x.
Definition sfun T S := T -> S.

Definition flip T S (R : T -> S -> Type) (f : forall x y, R x y) y x := f x y.

Identity Coercion fun_of_dfun : dfun >-> Funclass.
Identity Coercion fun_of_sfun : sfun >-> Funclass.

Lemma compA A B C D (f : C -> D) (g : B -> C) (h : A -> B) :
  f \o (g \o h) = f \o g \o h.
Proof. by []. Qed.

Definition const (T S : Type) (x : S) (y : T) := x.

Section Casts.

Variable (T : Type).
Implicit Types (x y z : T).

Definition cast (P : T -> Type) x y (e : x = y) : P x -> P y :=
  match e with erefl => id end.

Lemma castD (P : T -> Type) x y z (p : x = y) (q : y = z) (a : P x) :
  cast q (cast p a) = cast (etrans p q) a.
Proof. by case: z / q=> /=. Qed.

End Casts.

Arguments cast {T} P {x y} e.

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

Module Choice.

Variant mixin_of (T : Type) :=
  Mixin of forall (P : T -> Prop), (exists! x, P x) -> {x : T | P x}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Record type := Pack {sort : Type; base : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).

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

Definition botss_def (x : T) := False.

Lemma botss_proof : forall x y : T, botss_def x -> botss_def y -> x = y.
Proof. by []. Qed.

Definition botss : subsing :=
  Sub botss_def botss_proof.

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

Arguments botss {_}.

Lemma choose (T : choiceType) (X : subsing T) :
  (exists x, X x) -> {x : T | X x}.
Proof.
move=> ex; apply/choiceP.
case: ex=> [x Xx]; exists x; split=> //.
by move=> x'; move: Xx; apply: (valP X).
Qed.

Section SingletonMap.

Variables T S : Type.

Definition mapss_def (f : T -> S) (x : subsing T) (y : S) :=
  exists2 x0, x x0 & y = f x0.

Lemma mapss_proof f x y1 y2 :
  mapss_def f x y1 -> mapss_def f x y2 -> y1 = y2.
Proof.
by case=> [x1 x1P ->] [x2 x2P ->]; rewrite (valP x x1 x2).
Qed.

Definition mapss f x : subsing S :=
  Sub (mapss_def f x) (@mapss_proof f x).

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

End SingletonMap.

Module Po.

Definition axioms T (appr : relation T) :=
  [/\ reflexive T appr, transitive T appr & antisymmetric T appr].

Record mixin_of T := Mixin {
  appr : relation T;
  _    : axioms appr
}.

Notation class_of := mixin_of.

Section ClassDef.

Record type := Pack {sort; base : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).

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

Record mono (T S : poType) (p : phant (T -> S)) := Mono {
  mono_val :> sfun T S;
  _        :  monotone mono_val
}.

Arguments Mono {_ _ _ _}.

Canonical mono_subType (T S : poType) p :=
  [subType for @mono_val T S p].

Notation "{ 'mono' T }" := (mono (Phant T))
  (at level 0, format "{ 'mono'  T }") : type_scope.

Lemma monoP (T S : poType) (f : {mono T -> S}) : monotone f.
Proof. exact: valP. Qed.

Definition mono_comp (T S R : poType) (f : {mono S -> R}) (g : {mono T -> S}) : {mono T -> R} :=
  Eval hnf in Sub (f \o g) (monotone_comp (valP f) (valP g)).

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

Lemma monotone_const (T S : poType) (x : S) : monotone (@const T S x).
Proof. by move=> ???; reflexivity. Qed.

Definition mono_const (T S : poType) (x : S) : {mono T -> S} :=
  Eval hnf in Sub (@const T S x) (monotone_const x).
Canonical mono_const.

Lemma mono_comp_constL (T S R : poType) (x : R) (f : {mono T -> S}) :
  mono_comp (mono_const _ x) f = mono_const _ x.
Proof. exact: val_inj. Qed.

Lemma mono_comp_constR (T S R : poType) (f : {mono S -> R}) (x : S) :
  mono_comp f (mono_const _ x) = mono_const T (f x).
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
  Eval hnf in PoType {mono T -> S} (mono_poMixin T S).
Canonical mono_subPoType (T S : poType) :=
  Eval hnf in [subPoType of {mono T -> S}].

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

Definition mono_fst : {mono _ -> _} :=
  Eval hnf in Sub (@fst T S) monotone_fst.
Canonical mono_fst.

Lemma monotone_snd : monotone (@snd T S).
Proof. by case=> [??] [??] []. Qed.

Definition mono_snd : {mono _ -> _} :=
  Eval hnf in Sub (@snd T S) monotone_snd.
Canonical mono_snd.

End ProdPo.

Arguments mono_fst {_ _}.
Arguments mono_snd {_ _}.

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

Record class_of T := Class {
  base_po : Po.class_of T;
  base_choice : Choice.class_of T
}.

Record type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Local Coercion base_po : class_of >-> Po.class_of.
Local Coercion base_choice : class_of >-> Choice.class_of.
Variables (T : Type) (cT : type).
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

Section MonotoneChoice.

Variables (T : poType) (S : poChoiceType).

Definition mono_choiceMixin :=
  [choiceMixin of {mono T -> S} by <:].
Canonical mono_choiceType :=
  Eval hnf in ChoiceType {mono T -> S} mono_choiceMixin.
Canonical mono_poChoiceType :=
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

Lemma botssP X : botss ⊑ X.
Proof. by move=> x []. Qed.

Definition sing_poMixin := [poMixin of sing T by <:].
Canonical sing_poType := Eval hnf in PoType (sing T) sing_poMixin.
Canonical sing_subPoType := Eval hnf in [subPoType of sing T].
Canonical sing_poChoiceType := Eval hnf in PoChoiceType (sing T).

End SubsingPo.

Lemma monotone_mapss (T S : poType) (f : {mono T -> S}) : monotone (mapss f).
Proof.
move=> X Y XY _ [x Xx ->]; case/(_ _ Xx): XY=> [y Yy xy].
exists (f y); last exact: (valP f _ _ xy).
by exists y.
Qed.

Definition mono_mapss (T S : poType) (f : {mono T -> S}) : {mono _ -> _} :=
  Eval hnf in Sub (mapss f) (@monotone_mapss _ _ f).
Canonical mono_mapss.

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

Lemma sup_shift (x : nat -> T) n sup_x :
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

Record class_of T :=
  Class {base: PoChoice.class_of T; mixin : mixin_of (Po.Pack base)}.
Local Coercion base : class_of >-> PoChoice.class_of.

Record type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
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

Section Basics.

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

End Basics.

Section SubCpo.

Variables (T : cpoType) (P : T -> Prop).

Definition subCpo_axiom_of (S : subPoType P) :=
  forall (x : chain S), P (sup (mono_comp mono_val' x)).

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
  Sub (sup (mono_comp mono_val' x)) (@subCpo_axiom sT x).

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
  monotone (mono_sflip (mono_comp mono_val' f)).
Proof.
move=> x1 x2 x12 y /=; rewrite /flip /=; exact: (valP (f y) _ _).
Qed.

Definition mono_flip (T S R : poType) (f : {mono T -> {mono S -> R}}) :
  {mono S -> {mono T -> R}} :=
  Eval hnf in Sub (mono_sflip (mono_comp mono_val' f)) (monotone_flip f).
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

Section ProdCpo.

Variables T S : cpoType.

Definition prod_sup (x : chain (T * S)) :=
  (sup (mono_comp mono_fst x), sup (mono_comp mono_snd x)).

Lemma prod_supP (x : chain (T * S)) : supremum x (prod_sup x).
Proof.
rewrite /prod_sup.
case: (supP (mono_comp mono_fst x)) => [ub_x1 least_x1].
case: (supP (mono_comp mono_snd x)) => [ub_x2 least_x2].
split.
  by move=> n; split=> /=; [apply: ub_x1|apply: ub_x2].
case=> y1 y2 ub_y; split; [apply: least_x1|apply: least_x2];
by move=> n; case: (ub_y n).
Qed.

Definition prod_cpoMixin := CpoMixin prod_supP.
Canonical prod_cpoType := Eval hnf in CpoType (T * S) prod_cpoMixin.

End ProdCpo.

Definition mapp (T1 S1 T2 S2 : Type) (f1 : T1 -> S1) (f2 : T2 -> S2) :=
  fun x : T1 * T2 => (f1 x.1, f2 x.2).

Lemma monotone_mapp (T1 S1 T2 S2 : poType) (f1 : {mono T1 -> S1}) (f2 : {mono T2 -> S2}) :
  monotone (mapp f1 f2).
Proof.
by case=> [x1 y1] [x2 y2] [/= x12 y12]; split;
[apply: (valP f1 _ _ x12)|apply: (valP f2 _ _ y12)].
Qed.

Definition mono_mapp (T1 S1 T2 S2 : poType) (f1 : {mono T1 -> S1}) (f2 : {mono T2 -> S2}) : {mono _ -> _} :=
  Eval hnf in Sub (mapp f1 f2) (monotone_mapp f1 f2).
Canonical mono_mapp.

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
Definition mono_cpoMixin := [cpoMixin of {mono T -> S} by <:].
Canonical mono_cpoType := Eval hnf in CpoType {mono T -> S} mono_cpoMixin.

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
  forall (x : chain T), sup (mono_comp f x) = f (sup x).

Record cont (p : phant (T -> S)) := Cont {
  cont_val :> {mono T -> S};
  _        :  continuous cont_val
}.

Local Notation "{ 'cont' R }" := (cont (Phant R))
  (at level 0, format "{ 'cont'  R }").

Canonical cont_subType p := [subType for @cont_val p].
Definition cont_poMixin := [poMixin of {cont T -> S} by <:].
Canonical cont_poType := Eval hnf in PoType {cont T -> S} cont_poMixin.
Canonical cont_subPoType := [subPoType of {cont T -> S}].
Definition cont_choiceMixin := [choiceMixin of {cont T -> S} by <:].
Canonical cont_choiceType := Eval hnf in ChoiceType {cont T -> S} cont_choiceMixin.
Canonical cont_poChoiceType := Eval hnf in PoChoiceType {cont T -> S}.

Lemma contP (f : {cont T -> S}) : continuous f.
Proof. exact: valP. Qed.

Lemma eq_cont (f g : {cont T -> S}) : (forall x, f x = g x) -> f = g.
Proof.
move=> e; do 2![apply: val_inj].
exact: functional_extensionality e.
Qed.

Lemma cont_sup_clos : subCpo_axiom_of cont_subPoType.
Proof.
move=> /= f x.
rewrite {3}/sup /= {3}/sup /= /dfun_sup /=.
have -> : mono_dflip (mono_comp mono_val' (mono_comp mono_val' f)) (sup x) =
          sup (mono_comp (mono_flip (mono_comp mono_val' f)) x).
  apply: val_inj; apply: functional_extensionality=> n /=.
  rewrite /flip /= -(valP (f n)); congr sup.
  by apply: val_inj; apply: functional_extensionality.
rewrite supC; congr sup; apply: val_inj.
apply: functional_extensionality=> m /=.
rewrite /sup /= /dfun_sup; congr sup; apply: val_inj.
by apply: functional_extensionality.
Qed.

Canonical cont_subCpoType := SubCpoType cont_sup_clos.
Definition cont_cpoMixin := [cpoMixin of {cont T -> S} by <:].
Canonical cont_cpoType := Eval hnf in CpoType {cont T -> S} cont_cpoMixin.

End Continuous.

Local Notation "{ 'cont' R }" := (cont (Phant R))
  (at level 0, format "{ 'cont'  R }") : type_scope.

Arguments Cont {_ _ _ _}.

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

Definition cont_sflip (T : cpoType) S (R : cpoType)
  (f : {cont T -> sfun S R}) x : {cont T -> R} :=
  Sub (mono_sflip f x) (@continuous_dflip T S (fun _ => R) f x).

Section ContinuousComp.

Variables (T S R : cpoType).

Lemma continuous_comp (f : {mono S -> R}) (g : {mono T -> S}) :
  continuous f -> continuous g -> continuous (mono_comp f g).
Proof.
by move=> f_cont g_cont x /=; rewrite -g_cont -f_cont mono_compA.
Qed.

Definition cont_comp (f : {cont S -> R}) (g : {cont T -> S}) : {cont T -> R} :=
  Sub (mono_comp f g) (continuous_comp (valP f) (valP g)).

Lemma continuous_id : continuous (@mono_id T).
Proof. by move=> x; rewrite mono_comp1f. Qed.

Definition cont_id : {cont T -> T} :=
  Sub mono_id continuous_id.

End ContinuousComp.

Arguments cont_id {_}.

Lemma cont_compA (A B C D : cpoType) (f : {cont C -> D}) (g : {cont B -> C}) (h : {cont A -> B}) :
  cont_comp f (cont_comp g h) = cont_comp (cont_comp f g) h.
Proof. exact/val_inj/mono_compA. Qed.

Lemma cont_compf1 (A B : cpoType) (f : {cont A -> B}) : cont_comp f cont_id = f.
Proof. by apply: val_inj; rewrite /= mono_compf1. Qed.

Lemma cont_comp1f (A B : cpoType) (f : {cont A -> B}) : cont_comp cont_id f = f.
Proof. by apply: val_inj; rewrite /= mono_comp1f. Qed.

Lemma continuous_cast T (S : T -> cpoType) x y (e : x = y) : continuous (mono_cast S e).
Proof. case: y / e=> /=; rewrite mono_cast1; exact: continuous_id. Qed.

Definition cont_cast T (S : T -> cpoType) x y (e : x = y) : {cont _ -> _} :=
  Sub (mono_cast S e) (continuous_cast e).

Lemma continuous_valV (T S : cpoType) (P : S -> Prop) (sS : subCpoType P) (f : {mono T -> sS}) :
  continuous (mono_comp mono_val' f) -> continuous f.
Proof.
move=> f_cont x; apply: val_inj.
rewrite {1}/sup /= /subCpo_sup SubK; move: (f_cont x)=> /= <-.
by rewrite mono_compA.
Qed.

Lemma continuous_const (T S : cpoType) (x : S) : continuous (@mono_const T S x).
Proof. by move=> y; rewrite mono_comp_constL sup_const. Qed.

Definition cont_const (T S : cpoType) (x : S) : {cont T -> S} :=
  Eval hnf in Sub (@mono_const T S x) (continuous_const x).

Section SubsingCpo.

Variables (T : cpoType).

Definition subsing_sup_def (X : chain (subsing T)) x :=
  exists (y : chain T) (n : nat),
  (forall m, X (n + m) = subsing_of (y m)) /\
  supremum y x.

Lemma subsing_sup_subproof X x1 x2 :
  subsing_sup_def X x1 -> subsing_sup_def X x2 -> x1 = x2.
Proof.
move=> [y1 [n1 [y1X x1P]]] [y2 [n2 [y2X x2P]]].
pose y := shift y1 (n2 - n1).
have {x1P} x1P : supremum y x1 by exact: sup_shift (valP y1) _.
suffices: supremum y x2 by apply: supremum_unique x1P.
have -> : y = shift y2 (n1 - n2).
  apply: functional_extensionality=> n.
  rewrite /y /shift.
  apply: subsing_of_inj.
  by rewrite -y1X -y2X !addnA -!maxnE maxnC.
by apply: sup_shift (valP y2) _.
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
  exists (sup (Mono y_mono)).
    exists (Mono y_mono), n; split; last exact: supP.
    by move=> m; apply/in_subsing/(valP (choose (H m))).
  suffices -> : x = y 0.
    by case: (supP (Mono y_mono))=> [/= ub_y _]; apply: ub_y.
  rewrite /y; case: (choose _)=> z; rewrite /= addn0=> zP.
  by rewrite (valP (X n) _ _ Xnx zP).
- move=> /= ub_X ub_XP x [y [n [eq_y sup_x]]].
  move/(_ (n + 0)): (ub_XP); rewrite eq_y.
  case/(_ _ erefl)=> z zP _; exists z=> //.
  case: sup_x=> _; apply=> m; apply/subsing_of_appr.
  rewrite -eq_y -(in_subsing zP); exact: ub_XP.
Qed.

Definition subsing_cpoMixin := CpoMixin subsing_supP.
Canonical subsing_cpoType := Eval hnf in CpoType (subsing T) subsing_cpoMixin.

End SubsingCpo.

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

Section Retractions.

Definition retraction (T S : cpoType) (p : T -> S) (e : S -> T) :=
  cancel e p /\ forall x, e (p x) ⊑ x.

Record retr (T S : cpoType) (p : phant (T -> S)) := Retr {
  retr_val : {cont T -> S} * {mono S -> T};
  _        : retraction retr_val.1 retr_val.2
}.

Canonical retr_subType (T S : cpoType) p :=
  [subType for @retr_val T S p].
Notation "{ 'retr' T }" := (retr (Phant T))
  (at level 0, format "{ 'retr'  T }") : type_scope.
Definition retr_choiceMixin (T S : cpoType) :=
  [choiceMixin of {retr T -> S} by <:].
Canonical retr_choiceType (T S : cpoType) :=
  Eval hnf in ChoiceType {retr T -> S} (retr_choiceMixin T S).

Lemma retractionA (T S : cpoType) (p : {mono T -> S}) (e : {mono S -> T}) x y :
  retraction p e -> e x ⊑ y <-> x ⊑ p y.
Proof.
case=> eK pD; split; first by move=> /(valP p) /=; rewrite eK.
by move=> /(valP e) /= H; apply: transitivity H (pD _).
Qed.

Lemma embedding_iso (T S : cpoType) (p : {mono T -> S}) (e : {mono S -> T}) x y :
  retraction p e -> e x ⊑ e y -> x ⊑ y.
Proof. by case=> eK _ /(valP p); rewrite /= !eK. Qed.

Lemma embedding_cont (T S : cpoType) (p : {mono T -> S}) (e : {mono S -> T}) :
  retraction p e -> continuous e.
Proof.
move=> pe x; case: (supP x)=> [/= ub_x least_x]; apply: sup_unique; split.
  by move=> n /=; apply: (valP e).
move=> y ub_y; apply/(retractionA _ _ pe); apply: least_x.
by move=> n; apply/(retractionA _ _ pe); apply: ub_y.
Qed.

Lemma embedding_unique (T S : cpoType) (p : {mono T -> S}) (e1 e2 : {mono S -> T}) :
  retraction p e1 -> retraction p e2 -> e1 = e2.
Proof.
move=> e1P e2P; apply: val_inj; apply: functional_extensionality=> x /=.
apply: appr_anti; rewrite retractionA; eauto.
- rewrite e2P.1; reflexivity.
- rewrite e1P.1; reflexivity.
Qed.

Definition retr_retr (T S : cpoType) (P : phant (T -> S)) (p : retr P) : {cont T -> S} :=
  (val p).1.

Coercion retr_retr : retr >-> cont.

Definition retr_emb (T S : cpoType) (p : {retr T -> S}) : {cont S -> T} :=
  Sub (val p).2 (embedding_cont (valP p)).

Notation "p '^e'" := (retr_emb p) (at level 9, format "p ^e").

Lemma retrP (T S : cpoType) (p : {retr T -> S}) : retraction p p^e.
Proof. exact: (valP p). Qed.

Variables T S R : cpoType.

Lemma embK (p : {retr T -> S}) : cancel p^e p.
Proof. by case: (retrP p). Qed.

Lemma retrD (p : {retr T -> S}) x : p^e (p x) ⊑ x.
Proof. by case: (retrP p). Qed.

Lemma retrA (p : {retr T -> S}) x y : p^e x ⊑ y <-> x ⊑ p y.
Proof. by apply: retractionA; apply: retrP. Qed.

Lemma retraction_id : retraction (@id T) id.
Proof. by split=> x; reflexivity. Qed.

Definition retr_id : {retr T -> T} :=
  Eval hnf in Sub (cont_id, mono_id) retraction_id.

Lemma retraction_comp (p1 : {mono S -> R}) (e1 : {mono R -> S})
                      (p2 : {mono T -> S}) (e2 : {mono S -> T}) :
  retraction p1 e1 -> retraction p2 e2 -> retraction (p1 \o p2) (e2 \o e1).
Proof.
move=> [e1K p1D] [e2K p2D]; split; first by apply: can_comp.
move=> x /=.
have /= H := valP e2 _ _ (p1D (p2 x)).
apply: transitivity H _; apply: p2D.
Qed.

Definition retr_comp (p1 : {retr S -> R}) (p2 : {retr T -> S}) : {retr T -> R} :=
  Eval hnf in Sub (cont_comp p1 p2, mono_comp p2^e p1^e)
                  (retraction_comp (retrP p1) (retrP p2)).

Lemma emb_retr_comp p1 p2 : (retr_comp p1 p2)^e = cont_comp p2^e p1^e.
Proof. by apply: val_inj. Qed.

End Retractions.

Notation "{ 'retr' T }" := (retr (Phant T))
  (at level 0, format "{ 'retr'  T }") : type_scope.
Notation "p '^e'" := (retr_emb p) (at level 9, format "p ^e") : cpo_scope.

Arguments retr_id {_}.

Lemma retr_compA (A B C D : cpoType) (f : {retr C -> D}) (g : {retr B -> C}) (h : {retr A -> B}) :
  retr_comp f (retr_comp g h) = retr_comp (retr_comp f g) h.
Proof.
by apply: val_inj; rewrite /= cont_compA mono_compA.
Qed.

Lemma retr_compf1 (A B : cpoType) (f : {retr A -> B}) : retr_comp f retr_id = f.
Proof.
by case: f=> [[??] ?]; apply: val_inj; rewrite /= cont_compf1 mono_comp1f.
Qed.

Lemma retr_comp1f (A B : cpoType) (f : {retr A -> B}) : retr_comp retr_id f = f.
Proof.
by case: f=> [[??] ?]; apply: val_inj; rewrite /= cont_comp1f mono_compf1.
Qed.

Section BiLimit.

Variables (T : nat -> cpoType) (p : forall n, {retr T n.+1 -> T n}).

Fixpoint down n m : {retr T (m + n) -> T n} :=
  match m with
  | 0    => @retr_id _
  | m.+1 => retr_comp (down n m) (p (m + n))
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

Lemma downl0 n (nn : n <= n) : downl nn = retr_id.
Proof.
by rewrite /downl; move: (subnK nn); rewrite subnn=> e; rewrite eq_axiomK.
Qed.

Lemma downl1 n (nSn : n <= n.+1) : downl nSn = p n.
Proof. by rewrite (downlS (leqnn n) nSn) downl0 retr_comp1f. Qed.

Lemma downlD n m o (nm : n <= m) (mo : m <= o) :
  downl (leq_trans nm mo) = retr_comp (downl nm) (downl mo).
Proof.
move: (mo) (leq_trans _ _); rewrite -(subnK mo) {mo}.
elim: (o - m)=> {o} [|o IH] /=.
  move=> mo no; rewrite /downl; move: (subnK mo).
  rewrite -![0 + m]/(m) subnn => {mo} mo; rewrite eq_axiomK /= retr_compf1.
  by rewrite (eq_irrelevance no nm).
rewrite -![o.+1 + _]/(o + _).+1 => mo no.
rewrite (downlS (leq_trans nm (leq_addl o m)) no).
rewrite (IH (leq_addl o m) (leq_trans nm (leq_addl o m))).
by rewrite (downlS (leq_addl o m) mo) retr_compA.
Qed.

Definition inlim_def n (x : T n) m : T m :=
  downl (leq_addr n m) ((downl (leq_addl m n))^e x).

Lemma inlim_defEL n (x : T n) m (nm : n <= m) : inlim_def x m = (downl nm)^e x.
Proof.
rewrite /inlim_def.
rewrite (eq_irrelevance (leq_addl m n) (leq_trans nm (leq_addr n m))).
by rewrite downlD emb_retr_comp /= embK.
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
  by rewrite downlD emb_retr_comp downl1 /= embK.
- rewrite (inlim_defER _ mn) (inlim_defER _ (leq_trans (leqnSn m) mn)).
  by rewrite downlD downl1.
Qed.

Definition inlim n x : invlim p :=
  Sub (@inlim_def n x) (@inlim_proof n x).

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

Lemma retraction_outlim n : retraction (outlim n) (@inlim n).
Proof.
split.
  by move=> x; rewrite /inlim /outlim /= (inlim_defER _ (leqnn n)) downl0.
move=> /= x; rewrite appr_val /=; move=> m.
case: (leqP n m)=> [nm|/ltnW mn].
  by rewrite (inlim_defEL _ nm); apply: downlE_outlim.
rewrite (inlim_defER _ mn) downl_outlim; reflexivity.
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

Definition retr_outlim n : {retr invlim p -> T n} :=
  Sub (cont_outlim n, mono_inlim n) (retraction_outlim n).

Lemma emb_outlim n : (retr_outlim n)^e = cont_inlim n.
Proof.
apply: val_inj; move: (retraction_outlim n)=> /=.
(* FIXME: Why can't this be solved by unification? *)
rewrite -[@inlim n]/(mono_val (mono_inlim n)).
rewrite -[outlim n]/(mono_val (retr_outlim n)).
apply: embedding_unique; exact: retrP.
Qed.

Definition proj n : {cont invlim p -> invlim p} :=
  cont_comp (cont_inlim n) (cont_outlim n).

Lemma projI n m : cont_comp (proj n) (proj m) = proj (minn n m).
Proof.
apply: eq_cont=> /= x; apply: val_inj.
rewrite /minn; case: ltnP=> [nm|mn].
  suffices -> : outlim n (inlim (outlim m x)) = outlim n x by [].
  by rewrite {1}/outlim /= (inlim_defER _ (ltnW nm)) downl_outlim.
move: (outlim m x)=> {x} x.
rewrite /outlim {2}/inlim /= (inlim_defEL _ mn).
apply: functional_extensionality_dep=> k.
case: (leqP k m)=> [km|/ltnW mk].
  rewrite (inlim_defER _ km) (inlim_defER _ (leq_trans km mn)).
  by rewrite downlD /= embK.
rewrite (inlim_defEL _ mk); case: (leqP k n)=> [kn|/ltnW nk].
  rewrite (inlim_defER _ kn).
  rewrite (eq_irrelevance mn (leq_trans mk kn)) downlD emb_retr_comp /=.
  by rewrite embK.
rewrite (inlim_defEL _ nk) (eq_irrelevance mk (leq_trans mn nk)).
by rewrite downlD emb_retr_comp.
Qed.

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

Section Universe.

Let F (T : cpoType) := {cont T -> subsing (disc nat * T)}.

Fixpoint chain_obj n : cpoType :=
  match n with
  | 0    => [cpoType of subsing void]
  | n.+1 => [cpoType of F (chain_obj n)]
  end.

Definition chain_mor0_def :
  {cont chain_obj 1 -> chain_obj 0} * {mono chain_obj 0 -> chain_obj 1} :=
  (cont_const _ botss, mono_const _ (cont_const _ botss)).

Lemma chain_mor0_proof : retraction chain_mor0_def.1 chain_mor0_def.2.
Proof.
split.
- move=> /= x; rewrite /const; apply: val_inj.
  by apply: functional_extensionality=> - [].
- by move=> x; move=> y; rewrite /= /const /=; apply: botssP.
Qed.

Definition chain_mor0 : {retr chain_obj 1 -> chain_obj 0} :=
  Sub chain_mor0_def chain_mor0_proof.

End Universe.

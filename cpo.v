From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Obligation Tactic := idtac.

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

End SubType.

Local Notation inlined_sub_rect :=
  (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px).

Arguments SubType {_ _} _ _ _ _ _.
Arguments vrefl_rect {_ _} _ _.
Arguments Sub {_ _ _} _ _.
Arguments val {_ _ _} _.

Notation "[ 'subType' 'for' v ]" := (SubType _ v _ inlined_sub_rect vrefl_rect)
 (at level 0, only parsing) : form_scope.

Canonical sig_subType (T : Type) (P : T -> Prop) :=
  [subType for @sval T P].

Module Choice.

Definition axiom (T : Type) :=
  forall (P : T -> Prop), (exists! x, P x) -> {x : T | P x}.

Notation mixin_of := axiom.
Notation class_of := axiom.

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

Variable T : choiceType.

Lemma choiceP : Choice.axiom T.
Proof. by case: (T). Qed.

End ChoiceTheory.

Section SubChoice.

Variables (T : choiceType) (P : T -> Prop) (sT : subType P).

Lemma subType_choiceMixin : Choice.axiom sT.
Proof.
move=> Q H.
pose PQ x := P x /\ exists Px : P x, Q (Sub _ Px).
have {H} /choiceP [x [Px Qx]] : exists! x, PQ x.
  case: H=> x; elim/SubP: x=> [x Px] [Qx unique_x].
  exists x; repeat split=> //; first by exists Px.
  by move=> y [_ [Py /unique_x /(congr1 val)]]; rewrite !SubK.
exists (Sub x Px).
by case: Qx=> [Px' Qx]; rewrite (proof_irrelevance _ Px Px').
Qed.

End SubChoice.

Notation "[ 'choiceMixin' 'of' T 'by' <: ]" :=
  (@subType_choiceMixin _ _ _ : Choice.axiom T)
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

Lemma CanChoiceMixin : Choice.axiom T.
Proof.
move=> P ex.
pose Q y := exists2 x, P x & y = f x.
have {ex} /choiceP [y Qy]: exists! y, Q y.
  case: ex=> [x [Px x_unique]].
  exists (f x); split; first by exists x.
  by move=> _ [x' Px' ->]; rewrite (x_unique _ Px').
by exists (g y); case: Qy => [x Px ->]; rewrite fK.
Qed.

End CanChoice.

Section DepFunChoice.

Variables (I : Type) (T_ : I -> choiceType).

Lemma depfun_choiceMixin : Choice.axiom (forall i, T_ i).
Proof.
move=> P ex.
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

Canonical depfun_choiceType := Eval hnf in ChoiceType (forall i, T_ i) depfun_choiceMixin.

End DepFunChoice.

Definition fun_choiceType T (S : choiceType) :=
  Eval hnf in @depfun_choiceType T (fun _ => S).

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

Lemma subsing_choiceMixin : Choice.axiom subsing.
Proof.
move=> P ex.
pose A x := P (subsing_of x).
have unique_A : forall x y, A x -> A y -> x = y.
  case ex=> [B [PB unique_B]] x y Ax Ay.
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

Section SubPoType.

Variables (T : poType) (P : T -> Prop) (sT : subType P).

Lemma sub_apprP : Po.axioms (fun x y : sT => val x ⊑ val y).
Proof.
split.
- by move=> ?; reflexivity.
- by move=> ???; apply: transitivity.
- by move=> x y xy yx; apply: val_inj; apply: appr_anti.
Qed.

Definition SubPoMixin := PoMixin sub_apprP.

End SubPoType.

Notation "[ 'poMixin' 'of' T 'by' <: ]" :=
  (SubPoMixin _ : Po.mixin_of T)
  (at level 0, format "[ 'poMixin'  'of'  T  'by'  <: ]") : form_scope.

Definition monotone (T S : poType) (f : T -> S) :=
  forall x y, x ⊑ y -> f x ⊑ f y.

Lemma monotone_comp (T S R : poType) (f : S -> R) (g : T -> S) :
  monotone f -> monotone g -> monotone (f \o g).
Proof. by move=> mono_f mono_g x y /mono_g/mono_f. Qed.

Record mono (T S : poType) := Mono {
  mono_val :> T -> S;
  _        :  monotone mono_val
}.

Canonical mono_subType (T S : poType) :=
  [subType for @mono_val T S].

Definition mono_comp T S R (f : mono S R) (g : mono T S) : mono T R :=
  Sub (f \o g) (monotone_comp (valP f) (valP g)).

Section DepFunPo.

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

Definition depfun_poMixin := PoMixin fun_apprP.
Canonical depfun_poType := Eval hnf in PoType _ depfun_poMixin.

End DepFunPo.

Canonical fun_poType (T : Type) (S : poType) :=
  Eval hnf in @depfun_poType T (fun _ => S).

Definition mono_poMixin (T S : poType) :=
  [poMixin of mono T S by <:].
Canonical mono_poType (T S : poType) :=
  Eval hnf in PoType (mono T S) (mono_poMixin T S).

Lemma nat_apprP : Po.axioms leq.
Proof.
split.
- exact: leqnn.
- by move=> ???; apply: leq_trans.
- by move=> n m nm mn; apply: anti_leq; rewrite nm.
Qed.

Definition nat_poMixin := PoMixin nat_apprP.
Canonical nat_poType := Eval hnf in PoType nat nat_poMixin.

Section Supremum.

Variable T : poType.

Definition ub (x : nat -> T) (ub_x : T) :=
  forall n, x n ⊑ ub_x.

Definition sup (x : nat -> T) (sup_x : T) :=
  ub x sup_x /\ forall ub_x, ub x ub_x -> sup_x ⊑ ub_x.

Lemma sup_unique (x : nat -> T) sup_x1 sup_x2 :
  sup x sup_x1 -> sup x sup_x2 -> sup_x1 = sup_x2.
Proof.
move=> [ub_x1 least_x1] [ub_x2 least_x2].
apply: appr_anti.
- exact: least_x1 ub_x2.
- exact: least_x2 ub_x1.
Qed.

Definition osup (x : nat -> T) : subsing T := Sub (sup x) (@sup_unique x).

Lemma supC (x : nat -> nat -> T) (x1 x2 : nat -> T) :
  (forall n, sup (x n) (x1 n)) ->
  (forall m, sup (x^~ m) (x2 m)) ->
  sup x1 = sup x2.
Proof.
have H: forall x x1 x2, (forall n, sup (x n) (x1 n)) ->
                        (forall m, sup (x^~ m) (x2 m)) ->
                        forall sup_x,
                        sup x1 sup_x -> sup x2 sup_x.
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

Definition axiom (T : poType) :=
  forall (x : mono _ T),
  exists sup_x, sup (val x) sup_x.

Notation mixin_of := axiom.

Section ClassDef.

Record class_of T := Class {
  base_choice : Choice.class_of T;
  base_po     : Po.class_of T;
  mixin       : axiom (Po.Pack base_po)
}.

Local Coercion base_choice : class_of >-> Choice.class_of.
Local Coercion base_po     : class_of >-> Po.class_of.

Record type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack (bT_po : Po.class_of T) (m : mixin_of (Po.Pack bT_po)) :=
  fun b bT_choice & phant_id (@Choice.class bT_choice) b => @Pack T (@Class T b bT_po m).

Definition choiceType := @Choice.Pack cT xclass.
Definition poType := @Po.Pack cT xclass.

End ClassDef.

Module Exports.
Coercion base_choice : class_of >-> Choice.class_of.
Coercion sort : type >-> Sortclass.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion poType : type >-> Po.type.
Canonical poType.
Notation cpoType := type.
Notation cpoMixin := mixin_of.
Notation CpoType T m := (@pack T _ m _ _ id).
Notation "[ 'cpoType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'cpoType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'cpoType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'cpoType'  'of'  T ]") : form_scope.
End Exports.

End Cpo.

Export Cpo.Exports.

Notation chain T := (mono nat_poType T) (only parsing).

Section Basics.

Variable T : cpoType.

Lemma appr_sup : Cpo.axiom T.
Proof. exact: Cpo.mixin. Qed.

Lemma supP (x : chain T) : {sup_x | sup (val x) sup_x}.
Proof.
apply/choiceP.
have [sup_x sup_xP] := appr_sup x.
exists sup_x; split=> // ?.
exact: sup_unique.
Qed.

End Basics.

Section Continuous.

Variables T S : cpoType.

Definition continuous (f : T -> S) :=
  forall (x : chain T),
  sup (f \o x) (f (val (supP x))).

Record cont := Cont {
  cont_val :> mono T S;
  _        :  continuous cont_val
}.

Canonical cont_subType := [subType for cont_val].
(* FIXME: This does not work if the form notation is used. *)
Definition mono_choiceMixin :=
  @subType_choiceMixin (fun_choiceType T S) _ _ : Choice.axiom (mono T S).
Canonical mono_choiceType :=
  Eval hnf in ChoiceType (mono T S) mono_choiceMixin.
Definition cont_poMixin :=
  [poMixin of cont by <:].
Canonical cont_poType :=
  Eval hnf in PoType cont cont_poMixin.
Definition cont_choiceMixin :=
  [choiceMixin of cont by <:].
Canonical cont_choiceType :=
  Eval hnf in ChoiceType cont cont_choiceMixin.

Lemma eq_cont (f g : cont) : (forall x, f x = g x) -> f = g.
Proof.
move=> e; do 2![apply: val_inj].
exact: functional_extensionality e.
Qed.

Lemma cont_apprP : Cpo.axiom [poType of cont].
Proof.
move=> /= f.
have f_mono1: forall x, monotone (f^~ x).
  by move=> x n1 n2 n1n2; apply: (valP f n1 n2 n1n2).
pose sup_f x := val (supP (Mono (f_mono1 x))).
have sup_fP  :  forall x, sup (f^~ x) (sup_f x).
  move=> x; apply: valP.
have sup_f_mono : monotone sup_f.
  move=> x1 x2 x1x2.
  case: (sup_fP x1) (sup_fP x2)=> /= [ub_x1 least_x1] [ub_x2 least_x2].
  apply: least_x1=> n; apply: transitivity (f n x2) _ _ (ub_x2 n).
  exact: (valP (val (f n))).
have sup_f_cont : continuous sup_f.
  move=> x.
  have fnx_mono : forall n, monotone (f n \o x).
    by move=> n; apply: monotone_comp (valP (val _)) (valP _).
  pose g n := val (supP (Mono (fnx_mono n))).
  have gP  :  forall n, sup (f n \o x) (g n).
    by move=> n; apply: valP.
  have g_mono : monotone g.
    move=> n1 n2 n1n2.
    case: (gP n1) (gP n2)=> /= [ub_n1 least_n1] [ub_n2 least_n2].
    apply: least_n1=> m; apply: transitivity (f n2 (x m)) _ _ (ub_n2 m).
    exact: (valP f).
  have -> : sup_f (val (supP x)) = val (supP (Mono g_mono)).
    rewrite /sup_f; congr (val (supP _)); apply/val_inj=> /=.
    apply: functional_extensionality=> n.
    apply: sup_unique (valP (f n) x) (gP n).
  rewrite (supC _ gP); first exact: valP.
  move=> n /=; exact: sup_fP.
exists (@Cont (Mono sup_f_mono) sup_f_cont); split.
- by move=> n x /=; case: (sup_fP x)=> [ub_f _]; apply: ub_f.
- move=> g ub_g x /=; case: (sup_fP x)=> [_ least_f]; apply: least_f.
  move=> n; exact: ub_g.
Qed.

End Continuous.

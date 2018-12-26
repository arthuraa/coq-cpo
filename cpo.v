From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Obligation Tactic := idtac.

Lemma compA A B C D (f : C -> D) (g : B -> C) (h : A -> B) :
  f \o (g \o h) = f \o g \o h.
Proof. by []. Qed.

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
  (@subType_choiceMixin _ _ _ : Choice.mixin_of T)
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

Section DepFunChoice.

Variables (I : Type) (T_ : I -> choiceType).

Lemma depfun_choiceMixin : Choice.mixin_of (forall i, T_ i).
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

Coercion subPoType_poType : subPoType >-> poType.

Notation "[ 'poMixin' 'of' T 'by' <: ]" :=
  (SubPoMixin _ : Po.mixin_of T)
  (at level 0, format "[ 'poMixin'  'of'  T  'by'  <: ]") : form_scope.

Notation "[ 'subPoType' 'of' T ]" :=
  (@pack_subPoType _ _ T _ _ id _ id erefl)
  (at level 0, format "[ 'subPoType'  'of'  T ]") : form_scope.

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

Lemma mono_compA A B C D (f : mono C D) (g : mono B C) (h : mono A B) :
  mono_comp f (mono_comp g h) = mono_comp (mono_comp f g) h.
Proof. exact/val_inj. Qed.

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
Canonical mono_subPoType (T S : poType) :=
  Eval hnf in [subPoType of mono T S].

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
Notation "[ 'poChoiceType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'poChoiceType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'poChoiceType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'poChoiceType'  'of'  T ]") : form_scope.
End Exports.

End PoChoice.

Export PoChoice.Exports.

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

Lemma subsing_of_appr x y : subsing_of x ⊑ subsing_of y <-> x ⊑ y.
Proof.
split; first by move=> /(_ x erefl) [y' ->].
by move=> xy x' <-; exists y.
Qed.

Definition sing_poMixin := [poMixin of sing T by <:].
Canonical sing_poType := Eval hnf in PoType (sing T) sing_poMixin.
Canonical sing_subPoType := Eval hnf in [subPoType of sing T].

End SubsingPo.

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

Definition shift (x : nat -> T) n m := x (n + m).

Lemma sup_shift (x : nat -> T) n sup_x :
  monotone x ->
  sup x sup_x ->
  sup (shift x n) sup_x.
Proof.
move=> x_mono [ub_x least_x]; split; first by move=> m; apply: ub_x.
move=> y ub_y; apply: least_x=> p.
apply: transitivity (x (n + p)) _ _ (ub_y _).
by apply: x_mono; apply: leq_addl.
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

Variant mixin_of (T : poType) :=
  Mixin of forall (x : mono _ T), exists sup_x, sup (val x) sup_x.

Section ClassDef.

Record class_of T := Class {base: PoChoice.class_of T; _ : mixin_of (Po.Pack base)}.
Local Coercion base : class_of >-> PoChoice.class_of.

Record type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack (bT_po : Po.class_of T) (m : mixin_of (Po.Pack bT_po)) :=
  fun b bT_choice & phant_id (Choice.class b) bT_choice =>
  @Pack T (@Class T (PoChoice.Class bT_po bT_choice) m).

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

Lemma appr_sup : forall (x : mono _ T), exists sup_x, sup (val x) sup_x.
Proof. by case: T=> [? [? []]]. Qed.

Lemma supP (x : chain T) : {sup_x | sup (val x) sup_x}.
Proof.
apply/choiceP.
have [sup_x sup_xP] := appr_sup x.
exists sup_x; split=> // ?.
exact: sup_unique.
Qed.

End Basics.

Section SubCpo.

Variables (T : cpoType) (P : T -> Prop).

Record subCpoType := SubCpoType {
  subCpo_sort :> subPoType P;
  _           :  forall (x : chain subCpo_sort) sup_x,
                 sup (val \o x) sup_x -> P sup_x
}.

Variable sT : subCpoType.

Lemma SubCpoMixin : Cpo.mixin_of sT.
Proof.
case: sT=> sT' clos /=; split=> x.
have val_x_mono : monotone (val \o x).
  by move=> y1 y2 /=; rewrite -appr_val; apply: (valP x).
have [/= sup_x sup_xP] := supP (Mono val_x_mono).
have [ub_x least_x] := sup_xP.
exists (Sub sup_x (clos _ _ sup_xP)); split.
- by move=> n; rewrite appr_val SubK; apply: ub_x.
- move=> y ub_y; rewrite appr_val SubK; apply: least_x.
  move=> n /=; rewrite -appr_val; exact: ub_y.
Qed.

Definition subCpoType_cpoType := Eval hnf in CpoType sT SubCpoMixin.

End SubCpo.

Section Continuous.

Variables T S : cpoType.

Definition continuous (f : T -> S) :=
  forall (x : chain T),
  sup (f \o x) (f (val (supP x))).

Lemma continuous_mono (f : mono T S) :
  continuous f <->
  forall x : chain T,
    val (supP (mono_comp f x)) = f (val (supP x)).
Proof.
split.
- move=> f_cont x; apply: sup_unique (f_cont x); exact: valP.
- move=> f_cont x; rewrite -f_cont; exact: valP.
Qed.

Record cont := Cont {
  cont_val :> mono T S;
  _        :  continuous cont_val
}.

Canonical cont_subType := [subType for cont_val].
(* FIXME: This does not work if the form notation is used. *)
Definition mono_choiceMixin :=
  @subType_choiceMixin (fun_choiceType T S) _ _ : Choice.mixin_of (mono T S).
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

Lemma cont_cpoMixin : Cpo.mixin_of [poType of cont].
Proof.
split=> /= f.
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
  rewrite (@supC _ _ (sup_f \o x) g _ gP); first exact: valP.
  move=> n /=; exact: sup_fP.
exists (@Cont (Mono sup_f_mono) sup_f_cont); split.
- by move=> n x /=; case: (sup_fP x)=> [ub_f _]; apply: ub_f.
- move=> g ub_g x /=; case: (sup_fP x)=> [_ least_f]; apply: least_f.
  move=> n; exact: ub_g.
Qed.

Canonical cont_cpoType := Eval hnf in CpoType cont cont_cpoMixin.

End Continuous.

Section ContinuousComp.

Variables (T S R : cpoType).

Lemma continuous_comp (f : mono S R) (g : mono T S) :
  continuous f -> continuous g -> continuous (f \o g).
Proof.
move=> /continuous_mono f_cont /continuous_mono g_cont.
apply/(continuous_mono (mono_comp f g))=> x.
by rewrite -mono_compA f_cont g_cont.
Qed.

Definition cont_comp (f : cont S R) (g : cont T S) : cont T R :=
  Sub (mono_comp f g) (continuous_comp (valP f) (valP g)).

End ContinuousComp.

Lemma cont_compA A B C D (f : cont C D) (g : cont B C) (h : cont A B) :
  cont_comp f (cont_comp g h) = cont_comp (cont_comp f g) h.
Proof. exact/val_inj/mono_compA. Qed.

Section SubsingCpo.

Variables (T : cpoType).

Lemma subsing_cpoMixin : Cpo.mixin_of (subsing_poType T).
Proof.
split=> X.
pose sup_X x :=
  exists (y : chain T) (n : nat),
  (forall m, X (n + m) = subsing_of (y m)) /\
  sup y x.
have sup_XP : forall x1 x2, sup_X x1 -> sup_X x2 -> x1 = x2.
  move=> x1 x2 [y1 [n1 [y1X x1P]]] [y2 [n2 [y2X x2P]]].
  pose y := shift y1 (n2 - n1).
  have {x1P} x1P : sup y x1 by exact: sup_shift (valP y1) _.
  suffices: sup y x2 by apply: sup_unique x1P.
  have -> : y = shift y2 (n1 - n2).
    apply: functional_extensionality=> n.
    rewrite /y /shift.
    apply: subsing_of_inj.
    by rewrite -y1X -y2X !addnA -!maxnE maxnC.
  by apply: sup_shift (valP y2) _.
exists (Sub sup_X sup_XP); split.
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
  exists (val (supP (Mono y_mono))).
    exists (Mono y_mono), n; split; last exact: valP.
    by move=> m; apply/in_subsing/(valP (choose (H m))).
  suffices -> : x = y 0.
    by case: (supP _)=> [sup_y [/= ub_y _]]; apply: ub_y.
  rewrite /y; case: (choose _)=> z; rewrite /= addn0=> zP.
  by rewrite (valP (X n) _ _ Xnx zP).
- move=> /= ub_X ub_XP x [y [n [eq_y sup_x]]].
  move/(_ (n + 0)): (ub_XP); rewrite eq_y.
  case/(_ _ erefl)=> z zP _; exists z=> //.
  case: sup_x=> _; apply=> m; apply/subsing_of_appr.
  rewrite -eq_y -(in_subsing zP); exact: ub_XP.
Qed.

Canonical subsing_cpoType := Eval hnf in CpoType (subsing T) subsing_cpoMixin.

End SubsingCpo.

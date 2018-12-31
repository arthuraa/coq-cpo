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

Identity Coercion fun_of_dfun : dfun >-> Funclass.
Identity Coercion fun_of_sfun : sfun >-> Funclass.

Lemma compA A B C D (f : C -> D) (g : B -> C) (h : A -> B) :
  f \o (g \o h) = f \o g \o h.
Proof. by []. Qed.

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

Definition monotone (T S : poType) (f : T -> S) :=
  forall x y, x ⊑ y -> f x ⊑ f y.

Lemma monotone_comp (T S R : poType) (f : S -> R) (g : T -> S) :
  monotone f -> monotone g -> monotone (f \o g).
Proof. by move=> mono_f mono_g x y /mono_g/mono_f. Qed.

Record mono (T S : poType) := Mono {
  mono_val :> sfun T S;
  _        :  monotone mono_val
}.

Canonical mono_subType (T S : poType) :=
  [subType for @mono_val T S].

Definition mono_comp T S R (f : mono S R) (g : mono T S) : mono T R :=
  Eval hnf in Sub (f \o g) (monotone_comp (valP f) (valP g)).

Canonical mono_comp.

Lemma mono_compA A B C D (f : mono C D) (g : mono B C) (h : mono A B) :
  mono_comp f (mono_comp g h) = mono_comp (mono_comp f g) h.
Proof. exact/val_inj. Qed.

Lemma monotone_id (T : poType) : monotone (@id T).
Proof. by []. Qed.

Definition mono_id (T : poType) : mono T T :=
  Eval hnf in Sub idfun (@monotone_id T).

Canonical mono_id.

Arguments mono_id {_}.

Lemma monotone_cast T (S : T -> poType) (x y : T) (e : x = y) : monotone (cast S e).
Proof. by case: y / e. Qed.

Definition mono_cast T (S : T -> poType) (x y : T) (e : x = y) : mono _ _ :=
  Eval hnf in Sub (cast S e) (monotone_cast e).

Canonical mono_cast.

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

Definition mono_val' (sT : subPoType) : mono (subPoType_poType sT) T :=
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

Coercion subPoType_poType : subPoType >-> poType.

Notation "[ 'poMixin' 'of' T 'by' <: ]" :=
  (SubPoMixin _ : Po.mixin_of T)
  (at level 0, format "[ 'poMixin'  'of'  T  'by'  <: ]") : form_scope.

Notation "[ 'subPoType' 'of' T ]" :=
  (@pack_subPoType _ _ T _ _ id _ id erefl)
  (at level 0, format "[ 'subPoType'  'of'  T ]") : form_scope.

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

Section MonotoneChoice.

Variables (T : poType) (S : poChoiceType).

Definition mono_choiceMixin :=
  [choiceMixin of mono T S by <:].
Canonical mono_choiceType :=
  Eval hnf in ChoiceType (mono T S) mono_choiceMixin.
Canonical mono_poChoiceType :=
  Eval hnf in PoChoiceType (mono T S).

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

Definition sing_poMixin := [poMixin of sing T by <:].
Canonical sing_poType := Eval hnf in PoType (sing T) sing_poMixin.
Canonical sing_subPoType := Eval hnf in [subPoType of sing T].
Canonical sing_poChoiceType := Eval hnf in PoChoiceType (sing T).

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

Lemma dfun_supP T (S : T -> poType) (f : nat -> dfun_poType S) sup_f :
  (forall x, sup (f^~ x) (sup_f x)) -> sup f sup_f.
Proof.
move=> sup_fP; split.
- by move=> n x; case: (sup_fP x)=> ub_x _; apply: ub_x.
- move=> g ub_g x; case: (sup_fP x)=> _; apply.
  by move=> n; apply: ub_g.
Qed.

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
Notation CpoType T m := (@pack T _ unify _ unify m).
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

Lemma supE (x : chain T) sup_x : sup x sup_x -> val (supP x) = sup_x.
Proof. exact/sup_unique/(valP (supP x)). Qed.

End Basics.

Section SubCpo.

Variables (T : cpoType) (P : T -> Prop).

Definition subCpo_axiom (S : subPoType P) :=
  forall (x : chain S) sup_x,
    sup (val \o x) sup_x -> P sup_x.

Record subCpoType := SubCpoType {
  subCpo_sort :> subPoType P;
  _           :  subCpo_axiom subCpo_sort
}.

Definition clone_subCpoType (U : Type) :=
  [find sT1 : subType P   | sub_sort    sT1 ~ U   | "not a subType"    ]
  [find sT2 : subPoType P | subPo_sort  sT2 ~ sT1 | "not a subPoType"  ]
  [find sT  : subCpoType  | subCpo_sort sT  ~ sT2 | "not a subCpoType" ]
  sT.

Variable sT : subCpoType.

Lemma subCpo_supP (x : chain sT) (sup_x : sT) :
  sup x sup_x <-> sup (val \o x) (val sup_x).
Proof.
case: (sT) x sup_x=> [sS sSP] /= x sup_x; split=> sup_xP.
- have [/= vsup_x vsup_xP] := supP (mono_comp (Mono monotone_val) x).
  have Pvsup_x := sSP _ _ vsup_xP.
  suffices -> : val sup_x = vsup_x by [].
  rewrite -[RHS](SubK sS Pvsup_x); congr val.
  have [ub_x least_x] := vsup_xP.
  apply: sup_unique sup_xP _; split.
    by move=> n; rewrite appr_val SubK; apply: ub_x.
  move=> y ub_y; rewrite appr_val SubK; apply: least_x.
  move=> n /=; rewrite -appr_val; exact: ub_y.
- have [ub_x least_x] := sup_xP; split.
    move=> n; rewrite appr_val; apply: ub_x.
  move=> y ub_y; rewrite appr_val; apply: least_x.
  move=> n /=; rewrite -appr_val; exact: ub_y.
Qed.

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

Canonical subCpoType_poChoiceType := Eval hnf in PoChoiceType sT.
Canonical subCpoType_cpoType := Eval hnf in CpoType sT SubCpoMixin.

End SubCpo.

Notation "[ 'subCpoType' 'of' T ]" :=
  (@clone_subCpoType _ _ T _ unify _ unify _ unify)
  (at level 0, format "[ 'subCpoType'  'of'  T ]") : form_scope.
Notation "[ 'cpoMixin' 'of' T 'by' <: ]" :=
  (@SubCpoMixin _ _ [subCpoType of T])
  (at level 0, format "[ 'cpoMixin'  'of'  T  'by'  <: ]") : form_scope.

Section DFunCpo.

Variables (T : Type) (S : T -> cpoType).

Lemma dfun_supPV (f : chain (dfun_poType S)) :
  {sup_f | forall x, sup (f^~ x) (sup_f x)}.
Proof.
have f_mono: forall x, monotone (f^~ x).
  by move=> x n1 n2 n1n2; apply: (valP f n1 n2 n1n2).
by exists (fun x => val (supP (Mono (f_mono x))))=> x; apply: valP.
Qed.

Lemma dfun_cpoMixin : Cpo.mixin_of (dfun_poType S).
Proof.
split=> /= f; have [sup_f sup_fP] := dfun_supPV f.
exists sup_f; exact: dfun_supP sup_fP.
Qed.

Canonical dfun_cpoType := Eval hnf in CpoType (dfun S) dfun_cpoMixin.

Lemma dfun_sup_pointwise (f : chain dfun_cpoType) sup_f :
  sup f sup_f ->
  forall x, sup (f^~ x) (sup_f x).
Proof.
move=> sup_fP.
have [sup_f' PW] := dfun_supPV f.
have sup_f'P := dfun_supP PW.
by rewrite (sup_unique sup_fP sup_f'P).
Qed.

End DFunCpo.

Canonical sfun_cpoType (T : Type) (S : cpoType) :=
  Eval hnf in CpoType (sfun T S) (dfun_cpoMixin _).

Section MonoCpo.

Variables (T : poType) (S : cpoType).

Lemma mono_sup_clos : subCpo_axiom (mono_subPoType T S).
Proof.
move=> f sup_f; set F := val \o f.
have F_mono : monotone F by apply: monotone_comp monotone_val (valP f).
move=> sup_fP x y xy.
have PW := @dfun_sup_pointwise T (fun _ => S) (Mono F_mono) _ sup_fP.
case: (PW x)=> _; apply=> n /=.
case: (PW y)=> /(_ n) /= ub_y _.
by apply: transitivity ub_y; apply: (valP (f n)) xy.
Qed.

Canonical mono_subCpoType := Eval hnf in SubCpoType mono_sup_clos.
Definition mono_cpoMixin := [cpoMixin of mono T S by <:].
Canonical mono_cpoType := Eval hnf in CpoType (mono T S) mono_cpoMixin.

End MonoCpo.

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
Definition cont_poMixin := [poMixin of cont by <:].
Canonical cont_poType := Eval hnf in PoType cont cont_poMixin.
Canonical cont_subPoType := [subPoType of cont].
Definition cont_choiceMixin := [choiceMixin of cont by <:].
Canonical cont_choiceType := Eval hnf in ChoiceType cont cont_choiceMixin.
Canonical cont_poChoiceType := Eval hnf in PoChoiceType cont.

Lemma eq_cont (f g : cont) : (forall x, f x = g x) -> f = g.
Proof.
move=> e; do 2![apply: val_inj].
exact: functional_extensionality e.
Qed.

Lemma cont_sup_clos : subCpo_axiom cont_subPoType.
Proof.
move=> f sup_f.
rewrite -[val \o _]/(val (mono_comp (Mono monotone_val) _)).
move/subCpo_supP.
rewrite -[val \o _]/(val (mono_comp (Mono monotone_val) _)).
move/dfun_sup_pointwise=> sup_fP x.
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
  apply: sup_unique (sup_fP (val (supP x))) _.
  move: (valP (supP (Mono g_mono)))=> /=.
  rewrite {1}(_ : g = f^~ (sval (supP x))) //.
  apply: functional_extensionality=> n.
  exact: sup_unique (gP n) (valP (f n) x).
rewrite (@supC _ _ (sup_f \o x) g _ gP); first exact: valP.
move=> n /=; exact: sup_fP.
Qed.

Canonical cont_subCpoType := SubCpoType cont_sup_clos.
Definition cont_cpoMixin := [cpoMixin of cont by <:].
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

Lemma continuous_id : continuous (@id T).
Proof. move=> x; exact: (valP (supP x)). Qed.

Definition cont_id : cont T T :=
  Sub mono_id continuous_id.

End ContinuousComp.

Arguments cont_id {_}.

Lemma cont_compA A B C D (f : cont C D) (g : cont B C) (h : cont A B) :
  cont_comp f (cont_comp g h) = cont_comp (cont_comp f g) h.
Proof. exact/val_inj/mono_compA. Qed.

Lemma continuous_cast T (S : T -> cpoType) x y (e : x = y) : continuous (cast S e).
Proof. case: y / e=> /=; exact: continuous_id. Qed.

Definition cont_cast T (S : T -> cpoType) x y (e : x = y) : cont _ _ :=
  Sub (mono_cast S e) (continuous_cast e).

Lemma continuous_valV (T S : cpoType) (P : S -> Prop) (sS : subCpoType P) (f : T -> sS) :
  continuous (val \o f) ->  continuous f.
Proof.
move=> cont_f x; have [ub_x least_x] := cont_f x; split.
  by move=> n; move: (ub_x n); rewrite /= appr_val.
move=> y ub_y; move: (least_x (val y)); rewrite /= -appr_val.
by apply=> n; move: (ub_y n); rewrite /= -appr_val.
Qed.

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

Section InverseLimit.

Variable T : nat -> cpoType.
Variable p : forall n, cont (T n.+1) (T n).

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

Lemma invlim_sup_clos : subCpo_axiom invlim_subPoType.
Proof.
move=> x sup_x.
pose f := mono_comp (Mono monotone_val) x.
move=> /(@dfun_sup_pointwise _ _ f) sup_xP n.
have /continuous_mono /= cont_e := valP (p n).
have fn_mono : forall m, monotone (f^~ m).
  by move=> m n1 n2 n1n2; apply: (valP f).
rewrite -(@supE _ (Mono (fn_mono n.+1)) _ (sup_xP n.+1)) -cont_e.
rewrite -(@supE _ (Mono (fn_mono n)) _ (sup_xP n)).
congr (val (supP _)); apply/val_inj/functional_extensionality=> m /=.
exact: (valP (x m)).
Qed.

Canonical invlim_subCpoType := SubCpoType invlim_sup_clos.
Definition invlim_cpoMixin := [cpoMixin of invlim by <:].
Canonical invlim_cpoType := Eval hnf in CpoType invlim invlim_cpoMixin.

End InverseLimit.

Section Projections.

Definition projection (T S : cpoType) (p : T -> S) (e : S -> T) :=
  cancel e p /\ forall x, e (p x) ⊑ x.

Record proj (T S : cpoType) := Proj {
  proj_val :> cont T S;
  _        :  exists e : mono S T, projection proj_val e
}.

Canonical proj_subType (T S : cpoType) := [subType for @proj_val T S].
Definition proj_choiceMixin T S := [choiceMixin of proj T S by <:].
Canonical proj_choiceType T S := Eval hnf in ChoiceType (proj T S) (proj_choiceMixin T S).

Lemma projectionA (T S : cpoType) (p : mono T S) (e : mono S T) x y :
  projection p e -> e x ⊑ y <-> x ⊑ p y.
Proof.
case=> eK pD; split; first by move=> /(valP p) /=; rewrite eK.
by move=> /(valP e) /= H; apply: transitivity H (pD _).
Qed.

Lemma embedding_iso (T S : cpoType) (p : mono T S) (e : mono S T) x y :
  projection p e -> e x ⊑ e y -> x ⊑ y.
Proof. by case=> eK _ /(valP p); rewrite /= !eK. Qed.

Lemma embedding_cont (T S : cpoType) (p : mono T S) (e : mono S T) :
  projection p e -> continuous e.
Proof.
move=> pe x; case: (supP x)=> [sup_x [/= ub_x least_x]]; split.
  by move=> n /=; apply: (valP e).
move=> y ub_y; apply/(projectionA _ _ pe); apply: least_x.
by move=> n; apply/(projectionA _ _ pe); apply: ub_y.
Qed.

Lemma embedding_unique (T S : cpoType) (p : mono T S) (e1 e2 : mono S T) :
  projection p e1 -> projection p e2 -> e1 = e2.
Proof.
move=> e1P e2P; apply: val_inj; apply: functional_extensionality=> x /=.
apply: appr_anti; rewrite projectionA; eauto.
- rewrite e2P.1; reflexivity.
- rewrite e1P.1; reflexivity.
Qed.

Lemma proj_emb_ex (T S : cpoType) (p : proj T S) : {e : cont S T | projection p e}.
Proof.
pose p_proj : subsing _ := Sub (fun e : mono S T => projection p e) (@embedding_unique _ _ p).
case: (@choose _ p_proj (valP p))=> /= e pe.
have e_cont := embedding_cont pe.
by exists (Cont e_cont).
Qed.

Definition proj_emb (T S : cpoType) (p : proj T S) := val (proj_emb_ex p).

Definition proj_embP (T S : cpoType) (p : proj T S) := valP (proj_emb_ex p).

Notation "p '^e'" := (proj_emb p) (at level 9, format "p ^e").

Variables T S R : cpoType.

Lemma embK (p : proj T S) : cancel p^e p.
Proof. by case: (proj_embP p). Qed.

Lemma projD (p : proj T S) x : p^e (p x) ⊑ x.
Proof. by case: (proj_embP p). Qed.

Lemma projA (p : proj T S) x y : p^e x ⊑ y <-> x ⊑ p y.
Proof. by apply: projectionA; apply: proj_embP. Qed.

Lemma projection_id : projection (@id T) id.
Proof. by split=> x; reflexivity. Qed.

Lemma proj_id_proof : exists e : mono T T, projection id e.
Proof. exists cont_id; exact: projection_id. Qed.

Definition proj_id : proj T T := Sub cont_id proj_id_proof.

Lemma emb_id : proj_id^e = cont_id.
Proof.
move: (proj_embP proj_id)=> H.
apply: val_inj.
apply: embedding_unique H _; apply: projection_id.
Qed.

Lemma projection_comp (p1 : mono S R) (e1 : mono R S)
                      (p2 : mono T S) (e2 : mono S T) :
  projection p1 e1 -> projection p2 e2 -> projection (p1 \o p2) (e2 \o e1).
Proof.
move=> [e1K p1D] [e2K p2D]; split; first by apply: can_comp.
move=> x /=.
have /= H := valP e2 _ _ (p1D (p2 x)).
apply: transitivity H _; apply: p2D.
Qed.

Lemma proj_comp_proof (p1 : proj S R) (p2 : proj T S) :
  exists e : mono R T, projection (mono_comp p1 p2) e.
Proof.
by exists (cont_comp p2^e p1^e); apply: projection_comp; apply: proj_embP.
Qed.

Definition proj_comp (p1 : proj S R) (p2 : proj T S) : proj T R :=
  Sub (cont_comp p1 p2) (proj_comp_proof p1 p2).

Lemma emb_comp (p1 : proj S R) (p2 : proj T S) :
  (proj_comp p1 p2)^e = cont_comp p2^e p1^e.
Proof.
move: (proj_embP (proj_comp p1 p2)) => H.
apply: val_inj.
apply: embedding_unique H _; apply: projection_comp; apply: proj_embP.
Qed.

End Projections.

Notation "p '^e'" := (proj_emb p) (at level 9, format "p ^e") : cpo_scope.

Section BiLimit.

Variables (T : nat -> cpoType) (p : forall n, proj (T n.+1) (T n)).

Fixpoint down n m : proj (T (m + n)) (T n) :=
  match m with
  | 0    => @proj_id _
  | m.+1 => proj_comp (down n m) (p (m + n))
  end.

Lemma downSn n m x : p n (down n.+1 m x) = down n m.+1 (cast T (addnS _ _) x).
Proof.
elim: m x=> [|m IH] /=; first by move=> x; rewrite eq_axiomK.
move=> x; rewrite IH /=; congr (down _ _ (p _ _)).
move: (addnS m n) (addnS m.+1 n) x; rewrite -![m.+1 + _]/((m + _).+1).
move: (m + n.+1) (m + n).+1=> a b q.
by case: b / q=> q x /=; rewrite eq_axiomK.
Qed.

Definition inlim_def n x m : T m :=
  down m n (cast T (addnC _ _) ((down n m)^e x)).

Lemma inlim_proof n (x : T n) m : inlim_def x m = p m (inlim_def x m.+1).
Proof.
rewrite /inlim_def downSn /= castD; congr (down m n _).
move: (addnC m n) (etrans _ _); rewrite -[_.+1 + _]/(_ + _).+1=> q.
by case: (n + m) / q => /= q; rewrite !eq_axiomK /= emb_comp /= embK.
Qed.

Definition inlim n x : invlim p :=
  Sub (@inlim_def n x) (@inlim_proof n x).

Lemma monotone_inlim n : monotone (@inlim n).
Proof.
move=> x y xy m; rewrite /= /inlim_def /=.
apply: (valP (val (val (down m n)))).
move: (valP (val (down n m)^e) _ _ xy) => /=.
move: ((down n m)^e x) ((down n m)^e y)=> {x y xy}.
by case: (n + m) / (addnC _ _).
Qed.

Definition mono_inlim n : mono (T n) (invlim_poType p) :=
  Sub (@inlim n) (@monotone_inlim n).

Lemma continuous_inlim n : continuous (@inlim n).
Proof.
apply: continuous_valV.
have ->: val \o @inlim n = @inlim_def n.
  by apply: functional_extensionality=> x /=.
move=> x; apply: dfun_supP=> m /=.
exact: (valP (cont_comp (down m n) (cont_comp (cont_cast _ (addnC m n)) (down n m)^e))).
Qed.

Definition cont_inlim n : cont (T n) (invlim_cpoType p) :=
  Sub (mono_inlim n) (@continuous_inlim n).

Definition outlim n (x : invlim p) : T n := val x n.

Lemma up_outlim n m x : (down n m)^e (outlim _ x) ⊑ outlim _ x.
Proof.
elim: m=> [|m IH /=]; first by rewrite emb_id; reflexivity.
rewrite emb_comp.
apply: transitivity (valP (val (p (m + n))^e) _ _ IH) _.
rewrite /outlim (valP x) /=; exact: projD.
Qed.

Lemma down_outlim n m x : down n m (outlim _ x) = outlim _ x.
Proof.
elim: m=> [//|m IH /=]; by rewrite -(valP x (m + n)) -IH.
Qed.

Lemma projection_outlim n : projection (outlim n) (@inlim n).
Proof.
split.
  by move=> x; rewrite /inlim /inlim_def /outlim /= eq_axiomK /= embK.
move=> x; rewrite appr_val /=; move=> m; rewrite /inlim_def.
apply: (@transitivity _ _ _ _ (down m n (cast T (addnC m n) (outlim _ x)))).
  apply: (valP (val (val (down m n)))).
  apply: monotone_cast; exact: up_outlim.
rewrite (eq_irrelevance _ _ : addnC m n = esym (addnC n m)).
move: (m + n) (addnC n m)=> k ek.
case: k / ek=> /=.
rewrite down_outlim; reflexivity.
Qed.

Lemma monotone_outlim n : monotone (outlim n).
Proof. by move=> x y; rewrite appr_val => /(_ n). Qed.

Definition mono_outlim n : mono (invlim_poType p) (T n) :=
  Sub (outlim n) (monotone_outlim n).

Lemma continuous_outlim n : continuous (outlim n).
Proof.
move=> x; case: (supP x)=> [/= sup_x sup_xP]; split.
  move=> m; case: sup_xP=> ub_x _; exact: ub_x.
move/subCpo_supP: sup_xP=> /= sup_xP.
have /= := @dfun_sup_pointwise _ _ (mono_comp (mono_val' _) x) _ sup_xP n.
move=> {sup_xP} sup_xP y ub_y.
by case: sup_xP=> [_ least_x]; apply: least_x.
Qed.

Definition cont_outlim n : cont (invlim_cpoType p) (T n) :=
  Sub (mono_outlim n) (continuous_outlim n).

Lemma proj_outlim_proof n : exists e : mono _ _, projection (outlim n) e.
Proof. exists (mono_inlim n); exact: projection_outlim. Qed.

Definition proj_outlim n : proj (invlim_cpoType p) (T n) :=
  Sub (cont_outlim n) (proj_outlim_proof n).

Lemma emb_outlim n : (proj_outlim n)^e = cont_inlim n.
Proof.
apply: val_inj; move: (projection_outlim n)=> /=.
(* FIXME: Why can't this be solved by unification? *)
rewrite -[@inlim n]/(mono_val (mono_inlim n)).
rewrite -[outlim n]/(mono_val (proj_outlim n)).
apply: embedding_unique; exact: proj_embP.
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

Definition void_cpoMixin : Cpo.mixin_of void_poType.
Proof. by split=> x; case: (x 0). Qed.

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
Lemma disc_cpoMixin : Cpo.mixin_of disc_poType.
Proof.
split=> x; exists (x 0); split.
- by move=> n; rewrite (valP x _ _ (leq0n n)).
- by move=> y /(_ 0) ->.
Qed.
Canonical disc_cpoType := Eval hnf in CpoType disc disc_cpoMixin.

End Disc.

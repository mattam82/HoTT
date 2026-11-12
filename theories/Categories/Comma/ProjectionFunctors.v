(** * Functoriality of the comma category construction with projection functors *)
Require Import Category.Core Functor.Core.
Require Import Category.Prod Functor.Prod.Core.
Require Import Category.Dual Functor.Dual.
Require Import Functor.Composition.Core.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors NatCategory.
Require Import FunctorCategory.Core.
Require Import Cat.Core.
Require Import Functor.Paths.
Require Comma.Core.
Import Comma.Core.
Require Import Comma.InducedFunctors Comma.Projection.
Require ProductLaws ExponentialLaws.Law1.Functors ExponentialLaws.Law4.Functors.
Require Import Types.Forall PathGroupoids HoTT.Tactics.

Set Implicit Arguments.
Generalizable All Variables.

Local Open Scope category_scope.

(** ** Functor from [(A → C)ᵒᵖ × (B → C)] to [cat / (A × B)] *)
(** It sends [S : A → C ← B : T] to the category [(S / T)] and its projection functor to [A × B]. *)
Section comma.
  Local Open Scope type_scope.
  Context `{Funext}.
  Universes p p' pt a a' b b' c c'.

  Variable P : PreCategory@{p p'} -> Type@{pt}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Abbreviation Cat := (@sub_pre_cat@{p p' pt p p'} _ P HF).

  Variables (A : PreCategory@{a a'}) (B : PreCategory@{b b'}) (C : PreCategory@{c c'}).

  Hypothesis PAB : P (A * B).
  Hypothesis P_comma : forall (S : Functor A C) (T : Functor B C),
                         P (S / T).

  (** The slice category over [A * B], with the terminal category in [Set]: the notation [Cat / !x] would cast it to fresh universes. The objects of [Cat] are given their type explicitly: [(A * B; PAB)] would take it from [A * B], forcing [p] and [p'] to be the universes of [A * B]. *)
  Local Abbreviation CatAB := (@comma_category@{_ _ _ _ Set Set} Cat terminal_category Cat (cc_identity_functor' Cat) (@from_terminal@{_ _ Set Set} _ terminal_category _ _ _ (@exist PreCategory@{p p'} P (A * B)%category PAB : Cat)))%category.

  Local Open Scope category_scope.
  Local Open Scope morphism_scope.

  Definition comma_category_projection_functor_object_of
             (ST : object ((A -> C)^op * (B -> C)))
  : CatAB.
  Proof.
    exists (@exist PreCategory@{p p'} P (Basics.Overture.fst ST / Basics.Overture.snd ST) (P_comma _ _)) (center _).
    exact (comma_category_projection (Basics.Overture.fst ST) (Basics.Overture.snd ST)).
  Defined.

  Definition comma_category_projection_functor_morphism_of
             s d (m : morphism ((A -> C)^op * (B -> C)) s d)
  : morphism CatAB
             (comma_category_projection_functor_object_of s)
             (comma_category_projection_functor_object_of d).
  Proof.
    hnf.
    refine (CommaCategory.Build_morphism
              (comma_category_projection_functor_object_of s)
              (comma_category_projection_functor_object_of d)
              (comma_category_induced_functor m)
              (center _)
              _).
    simpl.
    destruct_head_hnf Basics.Overture.prod.
    path_functor.
  Defined.

  Local Ltac comma_laws_t :=
    repeat (apply path_forall || intro);
    simpl;
    rewrite !transport_forall_constant;
    transport_path_forall_hammer;
    simpl;
    destruct_head Basics.Overture.prod;
    simpl in *;
    apply CommaCategory.path_morphism;
    simpl;
    repeat match goal with
             | [ |- context[?f _ _ _ _ _ _ _ (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport
                                   _ P _ _ _ p
                                   (fun _ => f _ _ _ _ _ _ _)
                                   z)
             | [ |- context[transport (fun y => ?f (?fa _ _ _ _ _ y) ?x)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f y x) (fa _ _ _ _ _))
             | [ |- context[transport (fun y => ?f ?x (?fa _ _ _ _ _ y))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f x y) (fa _ _ _ _ _))
           end;
    unfold comma_category_induced_functor_object_of_identity;
    unfold comma_category_induced_functor_object_of_compose;
    simpl;
    rewrite ?CommaCategory.ap_a_path_object', ?CommaCategory.ap_b_path_object';
    try reflexivity.
    
  Lemma comma_category_projection_functor_identity_of x
  : comma_category_projection_functor_morphism_of (Category.Core.identity x)
    = 1.
  Proof.
    apply CommaCategory.path_morphism; simpl; [ | reflexivity ].
    path_functor.
    exists (path_forall _ _ (comma_category_induced_functor_object_of_identity _)).
    comma_laws_t.
  Qed.

  Lemma comma_category_projection_functor_composition_of s d d' m m'
  : comma_category_projection_functor_morphism_of
      (@Category.Core.compose _ s d d' m' m)
    = (comma_category_projection_functor_morphism_of m')
        o (comma_category_projection_functor_morphism_of m).
  Proof.
    apply CommaCategory.path_morphism; simpl; [ | reflexivity ].
    path_functor.
    simpl.
    exists (path_forall _ _ (comma_category_induced_functor_object_of_compose m' m)).
    comma_laws_t.
  Qed.

  Definition comma_category_projection_functor
  : Functor ((A -> C)^op * (B -> C)) CatAB
    := Build_Functor ((A -> C)^op * (B -> C)) CatAB
                     comma_category_projection_functor_object_of
                     comma_category_projection_functor_morphism_of
                     comma_category_projection_functor_composition_of
                     comma_category_projection_functor_identity_of.
End comma.

Section slice_category_projection_functor.
  Local Open Scope type_scope.
  Context `{Funext}.
  Universes p p' pt c c' d d'.

  Variable P : PreCategory@{p p'} -> Type@{pt}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Abbreviation Cat := (@sub_pre_cat@{p p' pt p p'} _ P HF).
  (** The terminal category, in [Set] *)
  Local Abbreviation one := (NatCategory.Core.nat_category@{Set} (Overture.S Overture.O)).

  Variables (C : PreCategory@{c c'}) (D : PreCategory@{d d'}).

  (** The universes of [one] in the products and comma categories are given explicitly: they would otherwise be fresh universes above [Set], different from the ones of [comma_category_projection_functor]. *)
  Hypothesis P1C : P (Category.Prod.prod@{Set Set c c'} one C).
  Hypothesis PC1 : P (Category.Prod.prod@{c c' Set Set} C one).
  Hypothesis PC : P C.
  Hypothesis P_comma : forall (S : Functor C D) (T : Functor@{Set Set d d'} one D), P (@comma_category@{c c' d d' Set Set} C one D S T).
  Hypothesis P_comma' : forall (S : Functor@{Set Set d d'} one D) (T : Functor C D), P (@comma_category@{Set Set d d' c c'} one C D S T).

  Local Open Scope functor_scope.
  Local Open Scope category_scope.

  Local Abbreviation inv D := (@ExponentialLaws.Law1.Functors.inverse _ one _ _ _ D).

  (** The slice category over [C], the object being given its type explicitly as in [comma] *)
  Local Abbreviation CatC := (Cat / (@exist PreCategory@{p p'} P C PC : Cat)).

  (** ** Functor [(C → D)ᵒᵖ → D → (cat / C)] *)
  Definition slice_category_projection_functor
  : object (((C -> D)^op) -> (D -> CatC)).
  Proof.
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ o (Functor.Identity.identity (C -> D)^op,
                 inv D)).
    refine (_ o @comma_category_projection_functor _ P HF C one D PC1 P_comma).
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor _).
  Defined.

  Definition coslice_category_projection_functor
  : object ((C -> D)^op -> (D -> CatC)).
  Proof.
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ o (Functor.Identity.identity (C -> D)^op,
                 inv D)).
    refine (_ o @comma_category_projection_functor _ P HF C one D PC1 P_comma).
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor _).
  Defined.

  (** ** Functor [(C → D) → Dᵒᵖ → (cat / C)] *)
  Definition slice_category_projection_functor'
  : object ((C -> D) -> (D^op -> CatC)).
  Proof.
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ o (Functor.Identity.identity (C -> D),
                 (inv D)^op)).
    refine (_ o ProductLaws.Swap.functor _ _).
    refine (_ o @comma_category_projection_functor _ P HF one C D P1C P_comma').
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor' _).
  Defined.

  Definition coslice_category_projection_functor'
  : object ((C -> D) -> (D^op -> CatC)).
  Proof.
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ o (Functor.Identity.identity (C -> D),
                 (inv D)^op)).
    refine (_ o ProductLaws.Swap.functor _ _).
    refine (_ o @comma_category_projection_functor _ P HF one C D P1C P_comma').
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor' _).
  Defined.
End slice_category_projection_functor.

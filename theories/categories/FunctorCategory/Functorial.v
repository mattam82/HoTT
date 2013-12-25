Require Import Category.Core Functor.Core FunctorCategory.Core Functor.Pointwise Functor.Pointwise.Properties Category.Dual Category.Prod Cat.Core ExponentialLaws.Law4.Functors.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

Section functor.
  Context `{fs1 : Funext}.

  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Definition cat := (sub_pre_cat P HF).

  Hypothesis has_functor_categories : forall C D : cat, P (C.1 -> D.1).

  Local Transparent Functor.Composition.Core.compose_composition_of.
  Local Transparent Functor.Composition.Core.compose_identity_of.

  Definition functor_uncurried `{fs2 : Funext}
  : object (@functor_category fs2 (cat^op * cat) cat).
    refine (
    (* := Eval cbv zeta in *)
        let object_of := (fun CD => (((fst CD).1 -> (snd CD).1);
                                     has_functor_categories (fst CD) (snd CD)))
        in Build_Functor
             (cat^op * cat) cat
             object_of
             (fun CD C'D' FG => pointwise (fst FG) (snd FG))
             (fun _ _ _ _ _ => Functor.Pointwise.Properties.composition_of _ _ _ _)
             _).
    intros.
    pose (Functor.Pointwise.Properties.identity_of (H:=fs1) ((fst x).1) (snd x).1).
    admit.
  Defined.

  Definition functor `{fs2 : Funext} : object (cat^op -> (cat -> cat))
    := ExponentialLaws.Law4.Functors.inverse _ _ _ (@functor_uncurried fs2).
End functor.

(* Require Import HoTT.Homotopy. *)

Definition id {A : Type} (a : A) := a.

Definition morphism (A:Type) := A -> A -> Type.
  
Class Identity {A} (M : morphism A) :=
  { identity : forall {x}, M x x }.

Class Composition {A} (M : morphism A) :=
  { composition : forall {x y z:A}, M x y -> M y z -> M x z }.

Class Inverse {A} (M : morphism A) :=
  { inverse : forall {x y:A}, M x y -> M y x }.

Class Category {A} (M : morphism A) := {
  Category_Identity :> Identity M ;
  Category_Composition :> Composition M;
  Identity_Left : forall x y : A, forall m : M x y, composition identity m = m;
  Identity_Right : forall x y : A, forall m : M x y, composition m identity = m;
  Composition_Assoc : forall (x y z w : A) (m : M x y) (m' : M y z) (m'' : M z w),
                        composition (composition m m') m'' =
                        composition m (composition m' m'')
 }.

Infix "∘" := composition (at level 81, left associativity).
Notation "'1' '@' x" := (identity (x:=x)) (at level 0, x at level 200).

Inductive fin : nat -> Set :=
| fin0 {n} : fin (S n)
| finS {n} (f : fin n) : fin (S n).
Section FinElim.

  Definition fin_0 P (p: fin 0): P p :=
    match p with | fin0 _ | finS _ _ => fun devil => False_rect (@ID) devil (* subterm !!! *) end.

  Definition fin_case (P: forall {n}, fin (S n) -> Type)
             (P1: forall n, @P n fin0) (PS : forall {n} (p: fin n), P (finS p))
             {n} (p: fin (S n)): P p :=
    match p with
      |fin0 k => P1 k
      |finS k pp => PS pp
    end.

  Definition fin_elim (P: forall {n}, fin (S n) -> Type)
             (P1: forall n, @P n fin0) (PS : forall {n} (p: fin (S n)), P p -> P (finS p)):
    forall {n} (p: fin (S n)), P p :=
    fix rectS_fix {n} (p: fin (S n)): P p:=
    match p with
      |fin0 k => P1 k
      |finS 0 pp => fin_0 (fun f => P (finS f)) pp
      |finS (S k) pp => PS pp (rectS_fix pp)
    end.
End FinElim.

Class Le (A : Type) := le : A -> A -> Prop.
Infix "≤" := le (at level 90). 

Inductive le_nat : nat -> nat -> Prop :=
| le0 n : le_nat 0 n
| leS n m : le_nat n m -> le_nat (S n) (S m).
Hint Constructors le_nat : arith.
Lemma le_n n : le_nat n n.
Proof. induction n; simpl; auto with arith. Defined.
Hint Resolve le_n : arith.
Require Import Program.Equality.

Lemma le_trans {m n k} : le_nat m n -> le_nat n k -> le_nat m k.
Proof.
  intros lemn; revert k; induction lemn; intros k lenk; auto with arith.
  depelim lenk; auto with arith.
Defined. 

Hint Resolve le_trans : earith.
  
Instance nat_Le : Le nat := le_nat.

Inductive finle : forall {n m}, fin n -> fin m -> Prop :=
| finle0 {m n} (f : fin (S n)) : finle (@fin0 m) f
| finleS {m n} (f : fin m) (g : fin n) : 
    finle (finS f) (finS g) -> finle f g.

(* Inductive finle : forall {n}, fin n -> fin n -> Prop := *)
(* | finle0 {m} (f : fin (S m)) : finle fin0 f *)
(* | finleS {m} (f : fin m) (g : fin m) :  *)
(*     finle (finS f) (finS g) -> finle f g. *)
Instance fin_Le n : Le (fin n) := finle.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.
Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "'Π'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "( x ; y )" := (existT _ x y).

Section Simplex.

  Definition Δ : Set := nat.
  
  Notation mor m n := (fin m -> fin n).
  
  Record mon {m n} (map : mor m n) : Prop :=
    { mon_idx : le_nat m n;
      mon_mor : Π f g : fin m, finle f g → finle (map f) (map g) }.

  Definition hom : nat -> nat -> Set := 
    fun m n => sigT (@mon m n).
  Definition hom_fn {m n} (m : hom m n) := projT1 m.
  Coercion hom_fn : hom >-> Funclass.
  Definition hom_prop {m n} (m : hom m n) : mon m := projT2 m.

  Definition id_hom (n : Δ) : hom n n.
  Proof. 
    refine (fun f => f ; _).
    constructor; auto with arith.
  Defined.

  Global Instance: Identity hom := { identity := id_hom }.

  Definition compose_hom {m n k : Δ} : hom m n -> hom n k -> hom m k.
  Proof. 
    intros f g.
    refine (fun x => g (f x) ; _).
    generalize (hom_prop f) (hom_prop g).
    intros [lemn lef] [lenk leg].
    constructor; eauto with arith earith.  
  Defined.

  Global Instance: Composition hom := { composition := @compose_hom }.

  Axiom funext : forall {A : Type} {B : A -> Type} (f g : forall x : A, B x),
    (forall x, f x = g x) -> f = g.

  Definition eq_hom {m n} (f g : hom m n) : 
    (forall x, f x = g x) -> f = g.
  Proof. 
    intros. apply funext in H. destruct f, g. simpl in H. 
    revert m1. elim H. intros m1; apply f_equal.
    admit.
  Qed.

  Global Instance simplex_cat : Category hom := {}.
  Proof.
    now intros; apply eq_hom. 
    now intros; apply eq_hom. 
    now intros; apply eq_hom. 
  Defined.


End Simplex.

Section nuplets.
  Context {A : Type}.

  Fixpoint uplet (n : nat) : Type := 
    match n with
      | 0 => unit
      | S n => (A * uplet n)%type
    end.

  Notation " n  '-uplet' " := (uplet n) (at level 0) : type_scope.

  Definition elim_fin_0 (f : fin 0) : A.
  Proof. inversion f. Defined.

  Definition projn {n : nat} : forall (f : fin (S n)) (i : (S n)-uplet), A :=
    fin_elim (fun n (f : fin (S n)) => (S n)-uplet -> A) (fun _ i => fst i) 
             (fun n f' r i => r (snd i)).

  Fixpoint uplet_rec {n} : forall (u : n-uplet) (acc : A) (f : A -> A -> A), A :=
    match n with
      | 0 => fun u acc f => acc
      | S n => fun u acc f => f acc (uplet_rec (snd u) (fst u) f)
    end. 

End nuplets.  

Arguments uplet A n.

Require Import Reals.


Definition test : (@uplet R 2) := (0%R, (1%R, tt)).
Eval compute in projn (finS fin0) test.

Instance R_le : Le R := Rle.

Section TopologicalSimplex.

  Definition sum {n} (u : @uplet R n) := uplet_rec u R0 Rplus.
  
  Lemma sum_0 r : sum ((r, tt) : uplet 1) = r.
  Proof. unfold sum. simpl. ring. Qed.

  Lemma sum_S {n} (r : R) (u : @uplet R n) : 
    sum ((r, u) : @uplet R(S n)) = Rplus r (sum u).
  Proof. 
    unfold sum.
    induction n; simpl; ring. 
  Qed.

  Hint Rewrite @sum_0 @sum_S : topsimplex.

  Ltac simp := autorewrite with topsimplex.

  Definition Δtop (n : nat) := 
    { xs : @uplet R (S n) | sum xs = 1%R /\ ∀ i, 0%R ≤ projn i xs }.

  Require Import RealField.

  Definition Δtop0 : Δtop 0.
  Proof.
    refine (exist _ (1%R, tt) _).
    simpl. split; auto. intros. repeat depelim i; simpl; auto. red. admit.
  Defined.

  Definition Δtop1 : Δtop 1.
  Proof.
    refine (exist _ (0%R, (1%R, tt)) _); simp.
    split; auto. field. intros. repeat depelim i; simpl; auto. apply Rle_refl. 
    admit.
  Defined.

  Definition incl : forall {n} (k : fin (S n)) (d : @uplet R n), @uplet R (S n) :=
    @fin_elim (fun n k => @uplet R n → @uplet R (S n)) 
             (fun _ i => (0%R, i))
             (fun n f' inclr i => (fst i, inclr (snd i))).
  
  Lemma incl0 {n} (d : @uplet R n) : incl fin0 d = (0%R, d).
  Proof eq_refl.

  Lemma inclS {n} (k : fin (S n)) (d : @uplet R (S n)) : 
    incl (finS k) d = (fst d, incl k (snd d)).
  Proof eq_refl.
  Hint Rewrite @incl0 @inclS : topsimplex.

  Definition sum_incl {n} (k : fin (S (S n))) (d : @uplet R (S n)) : sum d = sum (incl k d).
  Proof.
    revert d; apply fin_elim with (n:=n) (p:=k); clear; intros; simp.
    - ring.
    - rewrite <- H. destruct d; now simp.
  Qed.
  Hint Rewrite <- @sum_incl : topsimplex.

  Definition bound_incl {n} (k : fin (S n)) (d : @uplet R (S n)) : 
    (∀ i, 0%R ≤ projn i d) ->
    ∀ i, 0%R ≤ projn i (incl k d).
  Proof. 
    intros H i. revert k d H.
    depind i; intros k d H.

    - depelim k. simp. simpl. apply Rle_refl.
      depelim k; apply (H fin0).
    - depelim k. now (simp; simpl).
      destruct n. depelim k. simp.
      simpl. apply IHi; auto.
      intros i0.
      apply (H (finS i0)).
  Qed.

  Definition Δincl {n} (k : fin (S n)) (d : Δtop n) : Δtop (S n).
  Proof.
    refine (exist _ (incl k (proj1_sig d)) _).
    destruct d as [d [dsum dbound]]. simpl proj1_sig. simp.

    intuition auto.
    now apply bound_incl.
  Defined.
  
End TopologicalSimplex.

Eval compute in incl (finS fin0) test.
Eval compute in incl fin0 test.

Eval compute in proj1_sig (Δincl fin0 Δtop0).
Eval compute in proj1_sig (Δincl fin0 Δtop1).


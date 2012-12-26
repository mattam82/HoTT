(* Require Import HoTT.Homotopy. *)

Definition id {A : Type} (a : A) := a.

Definition morphism (A:Type) := A -> A -> Type.
  
Class Identity {A} (M : morphism A) :=
  { identity : forall {x}, M x x }.

Class Composition {A} (M : morphism A) :=
  { composition : forall {x y z:A}, M y z -> M x y -> M x z }.
Infix "∘" := composition (at level 40, left associativity).

Class Inverse {A} (M : morphism A) :=
  { inverse : forall {x y:A}, M x y -> M y x }.

Class Category {A} (M : morphism A) := {
  Category_Identity :> Identity M ;
  Category_Composition :> Composition M;
  Identity_Left : forall x y : A, forall m : M x y, identity ∘ m = m;
  Identity_Right : forall x y : A, forall m : M x y, m ∘ identity = m;
  Composition_Assoc : forall (x y z w : A) (m : M x y) (m' : M y z) (m'' : M z w),
                        m'' ∘ (m' ∘ m) = (m'' ∘ m') ∘ m
 }.

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

  Definition fin_case2 (P: forall {n}, fin (S (S n)) -> Type)
             (P1: forall n, @P n (@fin0 (S n))) (PS : forall {n} (p: fin (S n)), P (finS p))
             {n} (p: fin (S (S n))): P p :=
    match p with
      |fin0 (S n) => P1 n
      |finS (S n) pp => PS pp
      |finS 0 pp => @id
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

Definition fin_embed {n} (f : fin n) : fin (S n) :=
  fin_rect (fun n _ => fin (S n)) (fun n => fin0) (fun n' _ f' => finS f') n f.

Lemma fin_embed_elim (P : forall n : nat, fin n -> fin (S n) -> Prop)
  (P0 : forall n, P (S n) fin0 fin0)
  (PS0 : forall n f f', P n f f' -> P (S n) (finS f) (finS f')) :
  forall n f, P n f (@fin_embed n f).
Proof.
  intros. induction f; simpl; auto.
Qed.

Definition fin_pred {n} (f : fin (S (S n))) : fin (S n) :=
  match f with
    | fin0 0 => I
    | fin0 (S n) => @fin0 n
    | finS 0 f => fin_0 _ f
    | finS (S n) f' => f'
  end.

Require Import Program.Equality.

Lemma fin_pred_elim (P : forall n : nat, fin (S (S n)) -> fin (S n) -> Prop)
  (P0 : forall n, P n fin0 fin0)
  (PS0 : forall n f, P n (finS f) f) :
  forall n f, P n f (@fin_pred n f).
Proof.
  intros. elim f using fin_case2; simpl; auto.
Qed.

Eval compute in fin_pred (finS (@fin0 0)).
Eval compute in fin_pred (finS (finS (@fin0 0))).

Class Le (A : Type) := le : A -> A -> Prop.
Infix "≤" := le (at level 90). 

Inductive le_nat : nat -> nat -> Prop :=
| le0 n : le_nat 0 n
| leS n m : le_nat n m -> le_nat (S n) (S m).
Hint Constructors le_nat : arith.
Lemma le_n n : le_nat n n.
Proof. induction n; simpl; auto with arith. Defined.
Hint Resolve le_n : arith.

Lemma le_trans {m n k} : le_nat m n -> le_nat n k -> le_nat m k.
Proof.
  intros lemn; revert k; induction lemn; intros k lenk; auto with arith.
  depelim lenk; auto with arith.
Defined. 

Hint Resolve le_trans : earith.
  
Instance nat_Le : Le nat := le_nat.

Inductive finle : forall {n m}, fin n -> fin m -> Prop :=
| finle0 {m n} (f : fin n) : finle (@fin0 m) f
| finleS {m n} (f : fin m) (g : fin n) : 
    finle f g -> finle (finS f) (finS g).

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

  Definition compose_hom {m n k : Δ} : hom n k -> hom m n -> hom m k.
  Proof. 
    intros g f.
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

  Definition projn {n : nat} : forall (f : fin n) (i : n-uplet), A :=
    fin_rect (fun n (f : fin n) => n-uplet -> A) (fun _ i => fst i) 
             (fun n f' r i => r (snd i)) n.

  Fixpoint uplet_rec {n} : forall (u : n-uplet) (acc : A) (f : A -> A -> A), A :=
    match n with
      | 0 => fun u acc f => acc
      | S n => fun u acc f => f acc (uplet_rec (snd u) (fst u) f)
    end. 

  (* Lemma uplet_rec_eq {n} (u : n-uplet) (acc : A) f :  *)
  (*   uplet_rec u acc f = f acc (uplet_rec u f ). *)
                                                     

End nuplets.  

Arguments uplet A n.

Require Import Reals.

Definition test0 : (@uplet R 1) := (1%R, tt).

Definition test : (@uplet R 2) := (0%R, (1%R, tt)).
Eval compute in projn (finS fin0) test.

Instance R_le : Le R := Rle.

Section TopologicalSimplex.

  Definition sum {n} (u : @uplet R n) := uplet_rec u R0 Rplus.
  Arguments sum n u : simpl never.
  Lemma sum_0 r : sum ((r, tt) : uplet 1) = r.
  Proof. unfold sum. simpl. ring. Qed.

  Lemma sum_S {n} (r : R) (u : @uplet R n) : 
    sum ((r, u) : @uplet R(S n)) = Rplus r (sum u).
  Proof. 
    unfold sum.
    induction n; simpl; ring. 
  Qed.

  Hint Rewrite @sum_0 @sum_S : topsimplex.

  Ltac simp := repeat (autorewrite with topsimplex; simpl).

  Definition Δtop_prop {n} (xs : @uplet R n) :=
    sum xs = 1%R /\ ∀ i, 0%R ≤ projn i xs.

  Definition Δtop (n : nat) := sig (@Δtop_prop (S n)).

  Definition Δtop_proj {n : nat} : Δtop n -> uplet (S n) := @proj1_sig _ (@Δtop_prop (S n)).

  Lemma eq_Δtop n (x y : Δtop n) : Δtop_proj x = Δtop_proj y -> x = y.
  Proof. intros. destruct x, y. simpl in *. subst x.
         f_equal. admit.        (* pi *)
  Defined.

  Require Import RealField.

  Definition Δtop0 : Δtop 0.
  Proof.
    refine (exist _ (1%R, tt) _).
    simpl. split; auto. unfold sum. simpl. ring. intros. repeat depelim i; simpl; auto. red. admit.
  Defined.

  Definition Δtop1 : Δtop 1.
  Proof.
    refine (exist _ (0%R, (1%R, tt)) _); simp.
    split; auto. unfold sum; simpl. field. intros. repeat depelim i; simpl; auto. apply Rle_refl. 
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

  Definition sum_incl {n} (k : fin (S n)) (d : @uplet R n) : sum d = sum (incl k d).
  Proof.
    revert d; apply fin_elim with (n:=n) (p:=k); clear; intros; simp.
    - ring.
    - rewrite <- H. destruct d; now simp.
  Qed.
  Hint Rewrite <- @sum_incl : topsimplex.

  Definition bound_incl {n} (k : fin (S (S n))) (d : @uplet R (S n)) :
    (∀ i, 0%R ≤ projn i d) ->
    ∀ i, 0%R ≤ projn i (incl k d).
  Proof. 
    revert d. depind k.
    intros. simpl. depelim i. apply Rle_refl.
    simpl. apply H.
    
    intros.
    depelim i. simpl. apply (H fin0).
    
    destruct d. simpl.
    destruct n. repeat depelim i; repeat depelim k. simpl. apply Rle_refl.
    apply IHk; auto. intros i'. apply (H (finS i')).
  Qed.

  Definition Δincl {n} (k : fin (S (S n))) (d : Δtop n) : Δtop (S n).
  Proof.
    refine (exist _ (incl k (proj1_sig d)) _).
    destruct d as [d [dsum dbound]]. unfold Δtop_prop; simpl proj1_sig. simp.

    intuition auto.
    now apply bound_incl.
  Defined.

  Definition surj : forall {n} (k : fin (S n)) (d : @uplet R (S (S n))), @uplet R (S n) :=
    @fin_elim (fun n k => @uplet R (S (S n)) → @uplet R (S n)) 
             (fun _ i => let '(a, (b, i')) := i in (Rplus a b, i'))
             (fun n f' surj i => (fst i, surj (snd i))).

  Lemma surj0 {n} (d : @uplet R (S (S n))) : surj fin0 d = (Rplus (fst d) (fst (snd d)), snd (snd d)).
  Proof.
    simpl. destruct d. destruct u. simpl. reflexivity.
  Qed.

  Lemma surjS {n} (k : fin (S n)) (d : @uplet R (S (S (S n)))) : 
    surj (finS k) d = (fst d, surj k (snd d)).
  Proof eq_refl.
  Hint Rewrite @surj0 @surjS : topsimplex.
  Notation " n '-uplet' " := (@uplet R n) (at level 200) : type_scope.

  Lemma uplet_rec_eq {n} a (d : uplet n) : (uplet_rec d a Rplus)%R = (a + uplet_rec d 0 Rplus)%R.
  Proof.
    revert a.
    induction n; destruct d; simpl; intros a. 
    - ring.
    - rewrite IHn. ring.
  Qed.

  Lemma sum_unfold {n} a (d : uplet n) : sum ((a, d):uplet (S n)) = Rplus a (sum d).
  Proof. unfold sum; simpl; rewrite uplet_rec_eq. ring. Qed.
  
  Definition sum_surj {n} (k : fin (S n)) (d : @uplet R (S (S n))) : sum d = sum (surj k d).
  Proof.
    revert d. apply fin_elim with (n:=n) (p:=k); clear; intros; simp.
    - destruct d as [a [b d]]. now rewrite !sum_unfold, Rplus_assoc.
    - rewrite <- H. destruct d; now simp.
  Qed.
  Hint Rewrite <- @sum_surj : topsimplex.

  Lemma projn_finS {n} (i : fin n) a (d : @uplet R n) : 
    projn (finS i) (a, d) = projn i d.
  Proof eq_refl.
  Hint Rewrite @projn_finS : topsimplex.

  Definition bound_surj {n} (k : fin (S n)) (d : @uplet R (S (S n))) :
    (∀ i, 0%R ≤ projn i d) ->
    ∀ i, 0%R ≤ projn i (surj k d).
  Proof. 
    destruct d as [a [b d]].
    revert a b d. depind k; intros a b d H i.
    depelim i. 
    - simpl.
      generalize (H fin0), (H (finS fin0)).
      unfold le in *.
      simpl. intros. simpl. admit.
    - now apply (H (finS (finS i))).
    - destruct n. depelim k. destruct d as [c d].
      specialize (IHk n k eq_refl JMeq_refl b c d (fun i => H (finS i))). 
      depelim i. apply (H fin0).
      apply IHk.
  Qed.

  Definition Δsurj {n} (k : fin (S n)) (d : Δtop (S n)) : Δtop n.
  Proof.
    refine (exist _ (surj k (proj1_sig d)) _).
    destruct d as [d [dsum dbound]]. simpl proj1_sig.

    split.
    - now rewrite <- sum_surj.
    - now apply bound_surj.
  Defined.

  Lemma fin_embed_0 n (i : fin (S n)) : fin0 = fin_embed i -> i = fin0.
  Proof. elim i using fin_elim; intros; auto. discriminate. Qed.

  Section Laws.
    Context {n : Δ}.

    Notation arrow_mor := (fun a b => a -> b).
    Instance arrow_comp : Composition arrow_mor := { composition A B C := Basics.compose }.

    Notation "n '.+1'" := (S n) (at level 0).
    Notation "n '.+2'" := (S (S n)) (at level 0).
    Notation "n '.+3'" := (S (S (S n))) (at level 0).

    Lemma compose_incl (i : fin (n.+2)) (j : fin n.+3) :
      finS i ≤ j ->
      forall x, (incl j ∘ incl i) x = (incl (fin_embed i) ∘ incl (fin_pred j)) x.
    Proof. 
      intros leij x; simpl. unfold Basics.compose.
      do 2 red in leij; depind leij.

      do 3 (depelim leij; try reflexivity).
      specialize (IHleij _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl).
      destruct x as [a [b x]]. Opaque incl.
      simpl. simp. simpl. simpl in IHleij |- *.
      specialize (IHleij (b, x)).
      autorewrite with topsimplex in IHleij.
      simpl in IHleij.
      injection IHleij.
      intros. simp. simpl.
      rewrite H, H0. reflexivity.
    Qed.

    Lemma compose_Δincl (i : fin (n.+2)) (j : fin (S (S (S n)))) : 
      finS i ≤ j -> Δincl j ∘ Δincl i = Δincl (fin_embed i) ∘ Δincl (fin_pred j).
    Proof.
      intros leij. apply funext. intros [x xprop].
      simpl. unfold Basics.compose. simpl.
      apply eq_Δtop. simpl. now apply compose_incl. 
    Qed.

    Lemma compose_surj (i : fin (S n)) (j : fin (S n)) : 
      i ≤ j ->
      forall x, (surj j ∘ surj (fin_embed i)) x = 
                (surj i ∘ surj (finS j)) x.
    Proof. 
      intros leij x; simpl. unfold Basics.compose.
      do 2 red in leij; depind leij.

      simpl. destruct x as [a [b [c x]]]. simpl. 
      depelim j. simpl. f_equal. ring.
      now depelim j.

      destruct n; [depelim f|].
      specialize (IHleij _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl).
      destruct x as [a x]. Opaque surj.
      simpl. simp. simpl.
      specialize (IHleij x).
      now depelim leij; try reflexivity; rewrite IHleij.
    Qed.

    Lemma compose_Δsurj (i : fin (S n)) (j : fin (S n)) : 
      i ≤ j -> Δsurj j ∘ Δsurj (fin_embed i) = Δsurj i ∘ Δsurj (finS j).
    Proof. 
      intros leij; apply funext; intros x; simpl. unfold Basics.compose.
      destruct x. apply eq_Δtop. simpl. now apply compose_surj.
    Qed.

    Definition finlt {n} (i j : fin n) := 
      finS i ≤ fin_embed j.

    Arguments Basics.compose A B C g f x /.

    Ltac forward H :=
      match type of H with
        | ?X -> _ => let H' := fresh in cut X; [intro H'; specialize (H H'); clear H'|]
      end.


    Definition finS_inj {n} (x y: fin n) (eq: finS x = finS y): x = y :=
      match eq in _ = a return
            match a as a' in fin m return match m with |0 => Prop |S n' => fin n' -> Prop end
            with @fin0 _ =>  fun _ => True |@finS _ y => fun x' => x' = y end x with
          eq_refl => eq_refl
      end.

    Lemma surj_inj (i : fin (n.+2)) (j : fin (n.+2)) :
      finlt i j -> forall x,
                     (surj j ∘ incl (fin_embed i)) x = (incl i ∘ surj (fin_pred j)) x.
    Proof.
      intros ltij x. do 3 red in ltij. depind ltij.
      destruct x0 as [a [b x0]]. simpl. simp. 
      depelim ltij; try reflexivity.
      simpl. 
      depelim j; try discriminate. clear.
      now simp. 

      depelim ltij. simpl. simp. simpl. depelim j. discriminate. 
      depelim j; [discriminate|].
      repeat (simpl; simp). 
      simpl in x. 
      now depelim j; simp.
      
      simp. depelim j; [discriminate|].
      simpl in x.
      destruct n; [depelim f0|].
      specialize (IHltij _ _ j eq_refl eq_refl JMeq_refl).
      apply finS_inj in x. rewrite x in IHltij. 
      specialize (IHltij JMeq_refl).
      generalize (IHltij (b, x0)). simp.
      depelim j; try discriminate.
      depelim j; try discriminate.
      simpl in x. do 2 apply finS_inj in x. subst g. simp.
      intros. now rewrite H. 
    Qed.

    Lemma surj_incl_eq (i : fin (n.+1)) (j : fin (n.+1)) : 
      (i = j \/ fin_embed i = finS j) ->
      forall x,
        (surj j ∘ incl (fin_embed i)) x = x.
    Proof.
      revert i; depind j. intros.
      destruct x as [a x].
      destruct H; subst; simp. f_equal; ring.
      rewrite H. simp. f_equal; ring.

      intros.
      destruct x as [a x].
      destruct n; [depelim j|].
      specialize (IHj _ _ eq_refl JMeq_refl).
      destruct H; subst; simp.
      specialize (IHj j (or_introl eq_refl)).
      now setoid_rewrite IHj.

      depelim i. discriminate.
      simpl in H. apply finS_inj in H. 
      specialize (IHj i (or_intror H)).
      setoid_rewrite IHj. now simp.
    Qed.

    (* Lemma surj_incl_gt (i : fin (n.+2)) (j : fin (n.+2)) :  *)
    (*   finlt (finS j) (fin_embed i) -> *)
    (*   forall x : uplet (n.+2), *)
    (*     surj j (incl (fin_embed i) x) = (incl (fin_pred (fin_embed i)) (surj (fin_pred j) x)). *)
    (* Proof. *)
    (*   intros Hlt. do 3 red in Hlt. depind Hlt; simp. *)

    Lemma surj_incl_gt (i : fin (n.+2)) (j : fin (n.+1)) : 
      finlt (finS j) i ->
      forall x : uplet (n.+2),
        surj (fin_embed j) (incl (fin_embed i) x) = (incl (fin_pred (fin_embed i)) ∘ surj j) x.
    Proof.
      intros Hlt. do 3 red in Hlt. depind Hlt; simp.

      depelim i; try discriminate.
      simpl in x; apply finS_inj in x. subst.
      intros [a [b x]].
      simp. depelim Hlt. rewrite <- x. simp.
      depelim Hlt; simp. easy.
      depelim Hlt; simp. easy.
      specialize (IHHlt _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl).
      destruct x0 as [c x0].
      generalize (IHHlt (b, (c, x0))).
      rewrite <- x.
      simp.  intros.
      congruence.
    Qed.
      
    Definition fin_comparison {m} (f g : fin m) : comparison.
    Proof. admit. Qed.
    
    Check (fun  (i : fin (n.+2)) (j : fin (n.+2)) =>
             Δsurj j ∘ Δincl (fin_embed i)).

    Check (fun  (i : fin (n.+2)) (j : fin (n.+2)) =>
             (Δincl i ∘ Δsurj (fin_pred j))).
    
    Check (fun  (i : fin (n.+2)) (j : fin (n.+2)) => fun (x : Δtop (n.+1)) =>
             (Δincl (fin_embed (fin_pred i)) (Δsurj (fin_pred j) x))).

    (* Lemma Δsurj_Δincl (i : fin (n.+2)) (j : fin (n.+2)) : *)
    (*   Δsurj j ∘ Δincl (fin_embed i)  *)
    (*   = match fin_comparison i j return Δtop (n.+1) → Δtop (n.+1) with *)
    (*       | Lt => Δincl i ∘ Δsurj (fin_pred j) *)
    (*       | Eq => Datatypes.id *)
    (*       | Gt => Δincl (fin_pred (fin_embed i)) ∘ Δsurj j *)
    (*     end. *)
  End Laws.
End TopologicalSimplex.

Eval compute in incl (finS fin0) test0.
Eval compute in incl fin0 test0.

Eval compute in incl (finS fin0) test.
Eval compute in incl fin0 test.

Eval compute in proj1_sig (Δincl fin0 Δtop0).
Eval compute in proj1_sig (Δincl (finS fin0) Δtop0).
Check (Δincl (finS fin0) Δtop0).
Check (Δincl fin0 Δtop0).

Eval compute in proj1_sig (Δincl fin0 Δtop1).

Eval compute in proj1_sig (Δsurj fin0 Δtop1).


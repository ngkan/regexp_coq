Require Import ssreflect ssrbool List.
Set Implicit Arguments.

(* Words and languages *)

(*** Alphabet ***)

Parameter (A : Type).
Parameter Aeq : A -> A -> bool.
Axiom Aeq_dec : forall (x y : A), Aeq x y <-> x = y.

(*** Word ***)

Notation word := (list A).

(*** Language ***)

Notation language := (word -> Prop).

Implicit Types (L G H : language) (x y : A) (w : word).

(*** Basic languages ***)

Definition langVoid : language :=
  fun w => False.

Definition langNil : language :=
  fun w => w = nil.

Definition langW w0 : language := 
  fun w => w = w0.

Definition langWs (ws : list word) : language := 
  fun w => In w ws.

Definition langAtom x : language := 
  fun w => w = x::nil.

Definition langUnion L G : language := 
  fun w => (L w) \/ (G w).

Definition langIntersect L G : language := 
  fun w => (L w) /\ (G w).

Definition langConcat L G : language := 
  fun w => exists (w1:word) (w2:word), (w1 ++ w2 = w) /\ (L w1) /\ (G w2).

Inductive  langKleen L : language := 
  | LK_Empty: langKleen L nil
  | LK_Atom w: L w -> langKleen L w
  | LK_Concat w1 w2: langKleen L w1 -> langKleen L w2 -> langKleen L (w1 ++ w2)
.

Definition langMirror L : language := 
  fun w => L (rev w).


(*** Equivalance between two languages ***)

Definition eqL L G := forall w, L w <-> G w.

Infix "=L" := eqL (at level 90).

Lemma eqL_commutative L G: L =L G <-> G =L L.
Proof.
  split.
  + move => H. 
    intros w.
    symmetry.
    apply H.
  + move => H. 
    intros w.
    symmetry.
    apply H.
Qed.

Lemma eqL_transitive L G H: L =L G -> L =L H -> G =L H.
Proof.
  move => IH1 => IH2.
  split.
  + move => IH3.
    apply IH1 in IH3.
    apply IH2 in IH3.
    apply IH3.
  + move => IH3.
    apply IH2 in IH3.
    apply IH1 in IH3.
    apply IH3.
Qed.

(*** A few lemmas relating to languages. ***)

Lemma concat0L L : langConcat langVoid L =L langVoid.
Proof.
  split.
  + elim => [w1 [w2 [H1 [H2 H3]]]]. 
    contradiction.
  + move => H. 
    contradiction. 
Qed.

Lemma concatL0 L : langConcat L langVoid =L langVoid.
Proof. 
  split.
  + elim => [w1 [w2 [H1 [H2 H3]]]]. 
    contradiction.
  + move => H.
    contradiction.
Qed.

Lemma concat1L L : langConcat langNil L =L L.
Proof.
  split.
  + elim => [w1 [w2 [H1 [H2 H3]]]]. 
    subst. 
    inversion H2. 
    rewrite app_nil_l. 
    apply H3.
  + move => H. 
    exists nil. 
    exists w. 
    split. 
    ++ apply app_nil_l.
    ++ split. 
       reflexivity.
       apply H.
Qed.

Lemma concatL1 L : langConcat L langNil =L L.
Proof. 
  split.
  + elim => [w1 [w2 [H1 [H2 H3]]]]. 
    subst. 
    inversion H3. 
    rewrite app_nil_r. 
    apply H2.
  + move => H. 
    exists w. 
    exists nil. 
    split.
    ++ apply app_nil_r.
    ++ split.
       apply H.
       reflexivity.
Qed.

Lemma concatA L G H : langConcat (langConcat L G) H =L langConcat L (langConcat G H).
Proof. 
  split.
  + elim => [w1 [w2 [H1 [[w3 [w4 [H2 [H3 H4]]]] H5]]]].
    exists w3. 
    exists (w4++w2). 
    split.
    ++ rewrite (app_assoc w3 w4 w2). 
       rewrite H2.
       apply H1.
    ++ split.
       apply H3.
       exists w4. 
       exists w2. 
       split. reflexivity. 
       split. apply H4. 
       apply H5. 
  + elim => [w1 [w2 [H1 [H2 [w3 [w4 [H3 [H4 H5]]]]]]]].
    exists (w1++w3). 
    exists w4. 
    split.
    ++ rewrite <- (app_assoc w1 w3 w4).
       rewrite H3. 
       apply H1.
    ++ split.
       +++ exists w1. exists w3. 
           split. reflexivity.
           split. apply H2.
           apply H4. 
       +++ apply H5.
Qed.

Lemma unionC L G : langUnion L G =L langUnion G L.
Proof.
  split.
  + move => H. 
    destruct H.
    ++ right. 
       apply H.
    ++ left. 
       apply H.
  + move => H.
    destruct H.
    ++ right. 
       apply H.
    ++ left. 
       apply H.
Qed.

Lemma interC L G : langIntersect L G =L langIntersect G L.
Proof.
  split. 
  + move => H. 
    destruct H. 
    split. 
    apply H0. 
    apply H. 
  + move => H. 
    destruct H.
    split. 
    ++ apply H0. 
    ++ apply H. 
Qed.

Lemma langKleenKleen L : langKleen (langKleen L) =L langKleen L.
Proof.
  split.
  + move => H;induction H.
    ++ apply LK_Empty.
    ++ apply H.
    ++ apply LK_Concat.
       +++ apply IHlangKleen1.
       +++ apply IHlangKleen2.
  + move => H. inversion H.
    ++ apply LK_Empty.
    ++ apply LK_Atom.
       apply H.
    ++ apply LK_Concat.
       +++ apply LK_Atom.
           apply H0.
       +++ apply LK_Atom.
           apply H1.
Qed.

(* Regular languages *)

(*** Definition ***)

Inductive regular : language -> Prop :=
  | RL_Eq (L:language) (G:language): regular L -> L =L G -> regular G
  | RL_Void : regular langVoid
  | RL_Empty : regular langNil
  | RL_Atom (a:A): regular (langAtom a)
  | RL_Union L G: regular L -> regular G -> regular (langUnion L G)
  | RL_Concat L G: regular L -> regular G -> regular (langConcat L G)
  | RL_Kleen L: regular L -> regular (langKleen L)
. 

(*** Lemma related to regular languages **)
Lemma regularWaux a w: a::w = (a::nil) ++ w.
Proof.
  reflexivity.
Qed.

Lemma regularWaux2 w0 w1: langW (w0 ++ w1) =L langConcat (langW w0) (langW w1).
Proof.
  split.
  + move => H.
    inversion H.
    exists w0.
    exists w1.
    done.
  + move => H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    inversion H0.
    inversion H1.
    rewrite <- H.
    rewrite H2.
    rewrite H3.
    done.
Qed.

Lemma regularW w : regular (langW w).
Proof.
  induction w.
  + apply RL_Empty.
  + rewrite regularWaux.
    pose proof (regularWaux2 (a::nil) w).
    apply RL_Eq with (langConcat (langW (a :: nil)) (langW w)).
    ++ apply RL_Concat.
      +++ apply RL_Eq with (langAtom a).
        ++++ apply RL_Atom.
        ++++ done.
      +++ apply IHw.
    ++ apply eqL_commutative.  
       apply H.
Qed.

Lemma regularMaux1 w : rev (rev w) = rev (rev nil) -> w = nil.
Proof.
  move => h.
  rewrite rev_involutive in h.
  rewrite rev_involutive in h.
  assumption.
Qed.

Lemma regularMaux2 w : rev w = rev nil -> w = nil.
Proof.
  move => h.
  apply regularMaux1.
  apply f_equal.
  assumption.
Qed.

Lemma regularMaux3 w a: w = (a::nil) -> rev w = (a::nil).
Proof.
  move => h.
  rewrite h.
  done.
Qed.

Lemma regularMaux4 L w1 w2: langMirror (langKleen L) (w1 ++ w2) = (langKleen L) (rev w2 ++ rev w1).
Proof.
  rewrite <- rev_app_distr.
  done.
Qed.

Lemma regularMaux5 w: rev w = nil -> w = nil.
Proof.
  have: nil = rev nil. done.
  move => H HH.
  rewrite H in HH.
  apply regularMaux2.
  apply HH.
Qed.

Lemma regularMaux6 L w: langKleen L w -> langKleen (langMirror L) (rev w).
Proof.
  move => H.
  induction H.
  + apply LK_Empty.
  + apply LK_Atom. 
    rewrite <- rev_involutive in H. 
    apply H.
  + rewrite rev_app_distr.
    apply LK_Concat; done.
Qed.

Lemma regularMirror L : regular L -> regular (langMirror L).   
Proof.
  move => H.
  induction H.
  + apply RL_Eq with (langMirror L).
   ++ apply IHregular.
   ++ intros w. 
      split.
    +++ move => H1.
        apply H0 in H1.
        apply H1.
    +++ move => H1.
        apply H0 in H1.
        apply H1.
  + apply RL_Void.
  + apply RL_Eq with langNil.
    ++ apply RL_Empty.
    ++ split.
      +++ move => H.
          inversion H.
          done.
      +++ move => H.
          inversion H.
          have H2: (rev nil = nil). done.
          pose proof (H2 A).
          rewrite <- H0 in H1.
          apply regularMaux2 in H1.
          done.
  + apply RL_Eq with (langAtom a).
    ++ apply RL_Atom.
    ++ split.
      +++ move => h.
          inversion h.
          done.
      +++ move => h.
          inversion h.
          apply regularMaux3 in H0.
          rewrite rev_involutive in H0.
          apply H0.
  + apply RL_Eq with (langUnion (langMirror L) (langMirror G)).
    ++ apply RL_Union; done.
    ++ split; move => H2.
      +++ case H2; move => H3. 
        ++++ left. 
             apply H3.
        ++++ right. 
             apply H3.
      +++ case H2; move => H3; done.
  + apply RL_Eq with (langConcat (langMirror G) (langMirror L)).
    ++ apply RL_Concat; done.
    ++ split; move => H1.
      +++ destruct H1.
          destruct H1.
          destruct H1.
          destruct H1.
          destruct H2. 
          exists (rev x0).
          exists (rev x).
          split. symmetry. apply rev_app_distr.
          split; done.
      +++ destruct H1.
          destruct H1.
          destruct H1.
          destruct H2.
          exists (rev x0).
          exists (rev x).
          split. rewrite <- rev_app_distr. rewrite H1. apply rev_involutive.
          split. rewrite <- rev_involutive in H3. done.
          rewrite <- rev_involutive in H2. done.
  + apply RL_Eq with (langKleen (langMirror L)). 
    ++ apply RL_Kleen. done.
    ++ split; move => H1.
       +++ induction H1.
          ++++ apply LK_Empty.
          ++++ apply LK_Atom.
               apply H0.
          ++++ rewrite regularMaux4. apply LK_Concat; done. 
       +++ rewrite <- rev_involutive.
           apply regularMaux6. 
           apply H1.
Qed.

(* regular expression *)

Inductive regexp : Type :=
  | RE_Empty : regexp
  | RE_Void  : regexp
  | RE_Atom  : A -> regexp
  | RE_Concat: regexp -> regexp -> regexp
  | RE_Union : regexp -> regexp -> regexp
  | RE_Kleen : regexp -> regexp
.
Implicit Types (r : regexp).

Fixpoint interpret (r : regexp) {struct r} : language :=
  match r with
    | RE_Void => langVoid
    | RE_Empty => langNil
    | RE_Atom x => langAtom x
    | RE_Concat r1 r2 => langConcat (interpret r1) (interpret r2)
    | RE_Union r1 r2 => langUnion (interpret r1) (interpret r2)
    | RE_Kleen r1 => langKleen (interpret r1)
  end
.

Lemma regular_regexp r : regular (interpret r).
Proof. 
  induction r; simpl.
  + apply RL_Empty.
  + apply RL_Void.
  + apply RL_Atom.
  + apply RL_Concat; assumption.
  + apply RL_Union; assumption.
  + apply RL_Kleen; assumption.
Qed.

Lemma regexp_regular L : regular L -> exists r, L =L interpret r.
Proof.
  move => H.
  induction H.
  + inversion IHregular.
    exists x. 
    pose proof (eqL_transitive H0 H1).
    apply H2.
  + exists RE_Void. done.
  + exists RE_Empty. done.
  + exists (RE_Atom a). done.
  + inversion IHregular1.
    inversion IHregular2.
    exists (RE_Union x x0).
    split; move => H3.
    ++ inversion H3.
      +++ apply H1 in H4. left. done.
      +++ apply H2 in H4. right. done.
    ++ inversion H3.
      +++ apply H1 in H4. left. done.
      +++ apply H2 in H4. right. done.
  + inversion IHregular1.
    inversion IHregular2.
    exists (RE_Concat x x0).
    split; move => H3.
    ++ destruct H3.
       destruct H3. 
       destruct H3. 
       destruct H4.
       exists x1.
       exists x2.
       split. done.
       split. apply H1. done.
       apply H2. done.
    ++ destruct H3.
       destruct H3.    
       destruct H3.
       destruct H4. 
       exists x1.
       exists x2.
       split. assumption.
       split. apply H1. done.
       apply H2. done.
  + destruct IHregular.
    exists (RE_Kleen x).
    split; move => H1. 
    ++ induction H1.
      +++ apply LK_Empty.
      +++ apply LK_Atom. apply H0. apply H1. 
      +++ apply LK_Concat; done. 
    ++ induction H1.
      +++ apply LK_Empty.
      +++ apply LK_Atom. apply H0. apply H1.
      +++ apply LK_Concat; done. 
Qed.

Definition eqR (r1 r2 : regexp) : Prop := 
  (interpret r1) =L (interpret r2).

Infix "~" := eqR (at level 90).

Lemma eqR_commutative r1 r2: r1 ~ r2 <-> r2 ~ r1.
Proof.
  split.
  + move => H. 
    intros w.
    symmetry.
    apply H.
  + move => H. 
    intros w.
    symmetry.
    apply H.
Qed.

Lemma eqR_transitive r1 r2 r3: r1 ~ r2 -> r1 ~ r3 -> r2 ~ r3.
Proof.
  move => IH1 => IH2.
  split.
  + move => IH3.
    apply IH1 in IH3.
    apply IH2 in IH3.
    apply IH3.
  + move => IH3.
    apply IH2 in IH3.
    apply IH1 in IH3.
    apply IH3.
Qed.

Lemma Q11aux L1 L2 w: (langKleen L1 w) -> langKleen (langUnion L1 L2) w. 
Proof.
  move => H.
  induction H.
  + apply LK_Empty.
  + apply LK_Atom.
    left.
    apply H.
  + apply LK_Concat; done.
Qed.

Lemma Q11aux2 L1 L2 w: langKleen L2 w -> langKleen (langUnion L1 L2) w.
Proof.
  move => H.
  induction H.
  + apply LK_Empty.
  + apply LK_Atom.
    right.
    apply H.
  + apply LK_Concat; done.
Qed. 

Lemma Q11_RL: forall a b,  
    langKleen (langUnion (langAtom a) (langAtom b)) 
    =L langKleen (langConcat (langKleen (langAtom a)) (langKleen (langAtom b))).
Proof.
  split; move => H. 
  + induction H.
    ++ apply LK_Empty.
    ++ apply LK_Atom.
       inversion H.
       +++ exists w.
           exists nil.
           split. apply app_nil_r.
           split. apply LK_Atom. apply H0.
           apply LK_Empty.
       +++ exists nil.
           exists w. 
           split. apply app_nil_l.
           split. apply LK_Empty. 
           apply LK_Atom. apply H0.
    ++ apply LK_Concat; done.
  + induction H.
    ++ apply LK_Empty. 
    ++ destruct H.
       destruct H.
       destruct H.
       destruct H0.
       rewrite <- H.
       apply LK_Concat. 
       +++ apply Q11aux.
           apply H0.
       +++ apply Q11aux2.
           apply H1.
    ++ apply LK_Concat.
       apply IHlangKleen1.
       apply IHlangKleen2.
Qed.

Lemma Q11: 
forall a b, 
  RE_Kleen (RE_Union (RE_Atom a) (RE_Atom b)) ~ 
  RE_Kleen (RE_Concat (RE_Kleen (RE_Atom a)) (RE_Kleen (RE_Atom b))).
Proof.
  simpl.
  move => a b w.
  simpl.
  move: (Q11_RL a b w).
  done.
Qed.

(* regexp matching *)

Fixpoint contains0 (r : regexp) : bool :=   
  match r with
    | RE_Void => false
    | RE_Empty => true
    | RE_Atom x => false
    | RE_Concat r1 r2 => (contains0 r1) && (contains0 r2)
    | RE_Union r1 r2 => (contains0 r1) || (contains0 r2)
    | RE_Kleen r1 => true
  end
.

Lemma contains0_ok r : contains0 r <-> interpret r nil.
Proof.
  split; move => H.
  + induction r.
    ++ done.
    ++ done.
    ++ done.
    ++ inversion H.
       exists nil. 
       exists nil.
       split. done. 
       split. apply IHr1. move/andP: H1 => H1. apply H1.
       apply IHr2. move/andP: H1 => H1. apply H1.
    ++ inversion H. move/orP: H1 => H1.
       case H1; move => H2.
       +++ left. apply IHr1. apply H2.
       +++ right. apply IHr2. apply H2.
    ++ apply LK_Empty.
  + induction r.
    ++ done.
    ++ done.
    ++ done.
    ++ destruct H.
       destruct H.
       destruct H.
       destruct H0.
       simpl.
       apply/andP.
       apply app_eq_nil  in H.
       destruct H.
       split. apply IHr1. rewrite H in H0. apply H0.
       apply IHr2. rewrite H2 in H1. apply H1.
    ++ apply/orP.
       destruct H.
       +++ left. apply IHr1. apply H.
       +++ right. apply IHr2. apply H.
    ++ trivial.
Qed.

Fixpoint E (r : regexp) : regexp :=   
  match r with
    | RE_Empty => RE_Empty
    | RE_Void => RE_Void
    | RE_Atom x => RE_Void
    | RE_Concat r1 r2 => RE_Concat (E r1) (E r2)
    | RE_Union r1 r2 => RE_Union (E r1) (E r2)
    | RE_Kleen r1 => RE_Empty
  end
.

Lemma concatRE_Void r: RE_Concat r RE_Void ~ RE_Void.
Proof.
  intro w.
  split; simpl; move => H.
  + destruct H.
    destruct H.
    destruct H.
    destruct H0.
    contradiction.
  + contradiction. 
Qed.

Lemma concatRE_Void2 r: RE_Concat RE_Void r ~ RE_Void.
Proof.
  intro w.
  split; simpl; move => H.
  + destruct H.
    destruct H.
    destruct H.
    destruct H0.
    contradiction.
  + contradiction. 
Qed.

Lemma concatRE_Empty: RE_Concat RE_Empty RE_Empty ~ RE_Empty.
Proof.
  intro w.
  split; simpl; move => H.
  + destruct H.
    destruct H.
    destruct H.
    destruct H0.
    inversion H0.
    inversion H1.
    rewrite H0 in H.
    rewrite H1 in H.
    inversion H.
    done.
  + inversion H. 
    exists nil.
    exists nil.
    split. done.
    split; done. 
Qed.

Lemma unionRE_Void: RE_Union RE_Void RE_Void ~ RE_Void.
Proof.
  intro w.
  split; simpl; move => H.
  + destruct H.
    ++ apply H.
    ++ apply H.
  + destruct H.
Qed.

Lemma unionRE_Empty: RE_Union RE_Empty RE_Void  ~ RE_Empty.
Proof.
  intro w.
  split; simpl; move => H.
  + destruct H; done.
  + inversion H. left. done.  
Qed.

Lemma unionRE_Empty2: RE_Union RE_Void RE_Empty ~ RE_Empty.
Proof.
  intro w.
  split; simpl; move => H.
  + destruct H; done.
  + inversion H. right. done.  
Qed.

Lemma unionRE_Empty3: RE_Union RE_Empty RE_Empty ~ RE_Empty.
Proof.
  intro w.
  split; simpl; move => H.
  + destruct H; done.
  + inversion H. right. done.  
Qed.

Lemma concatREaux1: forall a b c, a~b -> RE_Concat a c ~ RE_Concat b c.
Proof.
  move => a b c H w.
  split.
  + move => H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    apply H in H1.  
    exists x.
    exists x0.
    split. apply H0.
    split. apply H1.
    apply H2.
  + move => H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    apply H in H1.  
    exists x.
    exists x0.
    split. apply H0.
    split. apply H1.
    apply H2.
Qed.

Lemma concatREaux2: forall a b c, a~b -> RE_Concat c a ~ RE_Concat c b.
Proof.
  move => a b c H w.
  split.
  + move => H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    apply H in H2.  
    exists x.
    exists x0.
    split. apply H0.
    split. apply H1.
    apply H2.
  + move => H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    apply H in H2.  
    exists x.
    exists x0.
    split. apply H0.
    split. apply H1.
    apply H2.
Qed.

Lemma unionREaux1: forall a b c, a~b -> RE_Union a c ~ RE_Union b c.
Proof.
  move => a b c H w.
  split.
  + move => H0.
    destruct H0.
    ++ apply H in H0.
       left.
       apply H0.
    ++ right.
       apply H0.
  + move => H0.
    destruct H0.
    ++ apply H in H0.
       left.
       apply H0.
    ++ right.
       apply H0.
Qed.
 
Lemma unionREaux2: forall a b c, a~b -> RE_Union c a ~ RE_Union c b.
Proof.
  move => a b c H w.
  split.
  + move => H0.
    destruct H0.
    ++ left.
       apply H0.
    ++ right.
       apply H.
       apply H0.
  + move => H0.
    destruct H0.
    ++ left.
       apply H0.
    ++ right.
       apply H in H0.
       apply H0.
Qed.
  
Lemma E_two_values: forall r, ((E r) ~ RE_Void) \/ ((E r) ~ RE_Empty).
Proof.
  move => r.
  induction r; simpl.
  + right. done.
  + left. done.
  + left. done.
  + case IHr1; case IHr2; simpl; move => H1; move => H2.
    ++ left.
       move: (concatREaux1 (E r2) H2). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H. 
       apply eqR_transitive.
       move: (concatREaux2 RE_Void H1). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H.
       apply eqR_transitive.
       apply  concatRE_Void.
    ++ left.
       move: (concatREaux1 (E r2) H2). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H.
       apply eqR_transitive.
       move: (concatREaux2 RE_Void H1). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H.
       apply eqR_transitive.
       apply concatRE_Void2.
    ++ left. 
       move: (concatREaux1 (E r2) H2). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H.
       apply eqR_transitive.
       move: (concatREaux2 RE_Empty H1). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H.
       apply eqR_transitive.
       apply concatRE_Void.
    ++ right.
       move: (concatREaux1 (E r2) H2). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H.
       apply eqR_transitive.
       move: (concatREaux2 RE_Empty H1). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H.
       apply eqR_transitive.
       apply concatRE_Empty.
  + case IHr1; case IHr2; simpl; move => H1; move => H2.
    ++ left. 
       move: (unionREaux1 (E r2) H2). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H. 
       apply eqR_transitive.
       move: (unionREaux2 RE_Void H1). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H.
       apply eqR_transitive.
       apply unionRE_Void. 
    ++ right. 
       move: (unionREaux1 (E r2) H2). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H. 
       apply eqR_transitive.
       move: (unionREaux2 RE_Void H1). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H.
       apply eqR_transitive.
       apply unionRE_Empty2.
    ++ right. 
       move: (unionREaux1 (E r2) H2). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H. 
       apply eqR_transitive.
       move: (unionREaux2 RE_Empty H1). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H.
       apply eqR_transitive.
       apply unionRE_Empty.
    ++ right. 
       move: (unionREaux1 (E r2) H2). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H. 
       apply eqR_transitive.
       move: (unionREaux2 RE_Empty H1). move => H. apply eqR_commutative in H. rewrite eqR_commutative.
       move: H.
       apply eqR_transitive. 
       apply unionRE_Empty3.
  + right; done.
Qed.

Lemma Eauxaux: RE_Void ~ RE_Empty -> False.
Proof.
  intros H.
  unfold eqR in H.
  simpl in H.
  unfold eqL in H.
  move: (H nil).
  unfold langVoid.
  unfold langNil.
  intros H0.
  destruct H0.
  apply H1.
  done.
Qed.

Lemma EauxauxConcat r1 r2: RE_Concat (E r1) (E r2) ~ RE_Empty -> ((E r1) ~ RE_Empty) /\ ((E r2) ~ RE_Empty).
Proof.
  move => H.
  case: (E_two_values r1); case (E_two_values r2); move => H0 H1.
  + move: concatRE_Empty. move => H2. 
    apply eqR_commutative in H.
    apply eqR_commutative in H2.
    pose proof (eqR_transitive H H2).
    move: (concatREaux1 (E r2) H1). move => H4. 
    pose proof (eqR_transitive H3 H4).
    move: (concatREaux2 RE_Void H0). move => H6. apply eqR_commutative in H5.
    pose proof (eqR_transitive H5 H6).
    move: concatRE_Empty. move => H8.
    pose proof (eqR_transitive H7 H8).
    move: (concatRE_Void RE_Void). move => H10.
    pose proof (eqR_transitive H9 H10).
    apply eqR_commutative in H11.
    pose proof (Eauxaux).
    contradiction.
  + move: concatRE_Empty. move => H2. 
    apply eqR_commutative in H.
    apply eqR_commutative in H2.
    pose proof (eqR_transitive H H2).
    move: (concatREaux1 (E r2) H1). move => H4. 
    pose proof (eqR_transitive H3 H4).
    move: (concatREaux2 RE_Void H0). move => H6. apply eqR_commutative in H5.
    pose proof (eqR_transitive H5 H6).
    move: concatRE_Empty. move => H8.
    pose proof (eqR_transitive H7 H8).
    move: (concatRE_Void2 RE_Empty). move => H10.
    pose proof (eqR_transitive H9 H10).
    apply eqR_commutative in H11.
    pose proof (Eauxaux).
    contradiction.
  + move: concatRE_Empty. move => H2. 
    apply eqR_commutative in H.
    apply eqR_commutative in H2.
    pose proof (eqR_transitive H H2).
    move: (concatREaux1 (E r2) H1). move => H4. 
    pose proof (eqR_transitive H3 H4).
    move: (concatREaux2 RE_Empty H0). move => H6. apply eqR_commutative in H5.
    pose proof (eqR_transitive H5 H6).
    move: concatRE_Empty. move => H8.
    pose proof (eqR_transitive H7 H8).
    move: (concatRE_Void RE_Empty). move => H10.
    pose proof (eqR_transitive H9 H10).
    apply eqR_commutative in H11.
    pose proof (Eauxaux).
    contradiction.
  + done.
Qed.

Lemma EauxauxUnion r1 r2: RE_Union (E r1) (E r2) ~ RE_Empty -> ((E r1) ~ RE_Empty) \/ ((E r2) ~ RE_Empty).
Proof.
  move => H.
  case: (E_two_values r1); case (E_two_values r2); move => H0 H1.
  + move: unionRE_Empty. move => H2. 
    apply eqR_commutative in H.
    apply eqR_commutative in H2. 
    pose proof (eqR_transitive H H2).
    move: (unionREaux1 (E r2) H1). move => H4. 
    pose proof (eqR_transitive H3 H4).
    move: (unionREaux2 RE_Void H0). move => H6. apply eqR_commutative in H5.
    pose proof (eqR_transitive H5 H6).
    move: unionRE_Empty. move => H8.
    pose proof (eqR_transitive H7 H8).
    move: (unionRE_Void). move => H10.
    pose proof (eqR_transitive H9 H10).
    apply eqR_commutative in H11.
    pose proof (Eauxaux).
    contradiction.
  + right.
    apply H0.
  + left.
    apply H1.
  + left.
    apply H1.
Qed.

Lemma Eaux r: (E r) ~ RE_Empty -> interpret r nil.
Proof.
  induction r; simpl; move => H.
  + done.
  + apply Eauxaux in H.
    contradiction.
  + apply Eauxaux in H.
    contradiction.
  + apply EauxauxConcat in H.
    destruct H.
    exists nil.
    exists nil.
    split. done.
    split. apply IHr1. apply H.
    apply IHr2. apply H0.
  + apply  EauxauxUnion in H.
    destruct H.
    ++ left.
       apply IHr1.
       apply H.
    ++ right.
       apply IHr2.
       apply H.
  + apply LK_Empty.
Qed.

Fixpoint Brzozowski (x : A) (r : regexp) : regexp :=
  match r with
    | RE_Empty => RE_Void
    | RE_Void => RE_Void
    | RE_Atom y => match Aeq x y with 
                   | true => RE_Empty
                   | false => RE_Void
                   end
    | RE_Concat r1 r2 => RE_Union (RE_Concat (Brzozowski x r1) r2) (RE_Concat (E r1) (Brzozowski x r2))
    | RE_Union r1 r2 => RE_Union (Brzozowski x r1)  (Brzozowski x r2) 
    | RE_Kleen r1 => RE_Concat (Brzozowski x r1) (RE_Kleen r1)
  end.

Fixpoint rmatch (r : regexp) (w : word) : bool := 
  match w with
    | nil => contains0 r
    | a::w => rmatch (Brzozowski a r) w
  end
.

Lemma Brzozowski_correct (x : A) (r : regexp) :
  forall w, interpret (Brzozowski x r) w -> interpret r (x :: w).
Proof.
  induction r; simpl.
  + contradiction.
  + contradiction.
  + case eq: (Aeq x a).
    ++ apply Aeq_dec in eq.
       destruct eq.
       move => w.
       move => H.
       inversion H.
       done.
    ++ contradiction.
  + move => w.                                                                       
    move => H.
    case H. 
    ++ move => H0.
       destruct H0.
       destruct H0.
       destruct H0.
       destruct H1.
       exists (x::x0).
       exists x1. 
       split. rewrite <- app_comm_cons. rewrite H0. reflexivity.
       split. apply IHr1 in H1. apply H1.
       apply H2. 
    ++ move => H0.
       destruct H0.
       destruct H0.
       destruct H0.
       destruct H1.
       move: (E_two_values r1). 
       move => lem.
       inversion lem.
       +++ apply H3 in H1.
           contradiction.
       +++ apply H3 in H1.
           inversion H1.
           rewrite H4 in H0.
           have: nil ++ x1 = x1. done. move => H5.
           rewrite H5 in H0. 
           destruct H0.
           rewrite <- H4 in H5.
           exists (x0).
           exists (x::x1).  
           split. rewrite H4. done.
           split. rewrite H4. apply (Eaux r1). apply H3.
           apply IHr2. apply H2.
  + move => w. 
    move => H.
    case H.
    ++ move => H1.
       left.
       apply IHr1.
       apply H1.
    ++ move => H1.
       right.
       apply IHr2.
       apply H1.
  + move => w.
    move => H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    apply IHr in H0.
    apply LK_Atom in H0.
    rewrite <- H.
    apply (LK_Concat H0 H1). 
Qed.

Lemma rmatch_correct (w : word) :
  forall r, rmatch r w -> interpret r w.
Proof.
  induction w.
  + move => r. 
  move => H. 
  inversion H. 
  apply contains0_ok. 
  apply H1.
  + move => r. 
    move => H.
    inversion H.
    apply IHw in H1.
    apply Brzozowski_correct.
    apply H1.
Qed.

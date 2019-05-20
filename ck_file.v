Module CK.

  Import Maps Assets AssetMapping 
  Name FormulaTheory Form Decidability FeatureModel.
  Require Import Coq.Lists.ListSet.

  Inductive Transformation : Type.

  Definition Item : Type := Formula * Transformation.
  Definition CK : Type := list Item.

  Variable ts: list Transformation.
  Variable t: Transformation.
  Variable am am1 am2 amt1 amt2: AM.
  Variable fm: FM.
  Variable exp: Formula.
  Variable ck ck2 its: CK.
  Variable item it it2: Item.
  Variable items its1 its2: list Item.
  Variable c: Configuration.
  Variable assets S S1 S2: set Asset.
  Variable s: set Configuration.
  Variable an: AssetName.


 Variable l l1 l2    : Maps.S.
 Variable r r1 r2    : Maps.T.
 Variable ls ls1 ls2 : set Maps.S.

  (* Get all Formulas*)
  Fixpoint exps (ck: CK) : set Formula :=
    match ck with
    | nil => nil
    | x :: xs => set_union form_dec (set_add form_dec (fst x) nil) (exps xs)
    end. 

  (*Definition items (ck : CK) : set Item := list2set ck.*) 

  (* get Formula*)
  Definition getExp (it : Item) : Formula := fst it.
  
  (* get Transformation*)
  Definition getRS (it: Item) : Transformation := snd it.
  
  Parameter Inline(40) transform : Transformation -> AM-> AM -> AM.
  
  Axiom preserv :
   forall am1 am2 amt1 amt2 t, 
      (unique am1) /\ (unique am2) /\ (unique amt1) /\ (unique amt2) ->
      aMR am1 am2 /\ aMR amt1 amt2 ->
        aMR (transform t am1 am2) (transform t am2 amt2). 
  
  (* get each asset if it satisfies a configuration*)
  Fixpoint semanticsCK (ck : CK) (am amt: AM) (c: Configuration) : set Asset :=
    match ck with
     | nil => img amt
     | x :: xs => if is_true (satisfies (getExp x) c) then 
                    semanticsCK xs am (transform (getRS x) am amt) c  
                  else semanticsCK xs am amt c
    end.
  
  (* get AM if it satisfies a configuration*)
  Fixpoint semanticCK (ck : CK) (am amt: AM) (c: Configuration) : AM :=
    match ck with
    |nil => amt
    | x :: xs => if is_true (satisfies (getExp x) c) 
                    then semanticCK xs am (transform (getRS x) am amt) c 
                 else semanticCK xs am amt c
    end. 
  
  Definition semantics (ck: CK) (am: AM) (c: Configuration): set Asset :=
    semanticsCK ck am (nil) c. 
  
  (* return the same result*)
  Lemma similarFunctions: 
    forall ck am amt c, (unique am) -> semanticsCK ck am amt c 
      = img (semanticCK ck am amt c).
  Proof.
    induction ck0.
      - induction amt.
        + induction am0. 
          * intros. simpl. reflexivity.
          * intros. simpl. reflexivity.
        + induction amt.
          * intros. simpl. reflexivity.
          * intros. simpl. reflexivity.
      - induction amt.
        + induction am0. 
          * intros. simpl. intuition.
          * intros. simpl. intuition.
        + induction amt.
          * intros. simpl. intuition.
          * intros. simpl. intuition.
Qed.

Theorem compAmRefEmptyset:
    forall am1 am2,
      (unique am1) /\ (unique am2) ->
        aMR am1 am2 ->
          forall ck c,
            wfProduct (semantics ck am1 c) ->
               wfProduct (semantics ck am2 c).
  Proof.
    induction am1.
      - induction am2.
        + induction ck.
          { intros. destruct H. unfold unique in H. unfold unique in H2.
            specialize (H l r1 r2). specialize (H2 l r1 r2).
            intuition. }
          { intros. destruct H. intuition. }
        + induction ck.
          { intros. destruct H. intuition. }
          { intuition. }
      - induction am2.
        + induction ck.
          { intuition. }
          { intuition. }
        + induction ck.
          { intuition. }
          { intuition. }
  Qed.
  
  
  Theorem compAmRef:
    forall am1 am2,
      (unique am1) /\ (unique am2) ->
        aMR am1 am2 ->
          (forall ck c amt1 amt2,
            aMR amt1 amt2 /\ wfProduct (semanticsCK ck am1 amt1 c) ->
              wfProduct (semanticsCK ck am2 amt2 c)).
  Proof.
   induction am1.
      - induction am2.
        + induction ck.
          { intuition. }
          { intuition. }
        + induction ck.
          { intuition. }
          { intuition. }
      - induction am2.
        + induction ck.
          { intuition. }
          { intuition. }
        + induction ck.
          { intuition. }
          { intuition. }
  Qed.
  
  
End CK.
  

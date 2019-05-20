
Module Maps.

  Set Implicit Arguments.

  (*Imports*)
  Require Export Coq.Lists.List.
  Require Import Coq.Arith.Arith.
  Require Import Coq.Init.Specif.
  Require Import Coq.Bool.Bool.

  (*library of finite set*)
  Require Export Coq.Lists.ListSet.

  Section Types.

  (*Key and value*)
  Inductive S: Type.
  Inductive T: Type.

  (*pair and map definition*)
  Definition pair_     :Type := prod S T.
  Definition map_     :Type := list pair_.

  Definition empty_map : set T := nil.

  Notation "[-]"        := empty_map.
  Notation "( x , y )" := (pair_ x y).

  End Types.

  Section Spec.

  (*Local Vars*)
  Variable l l1 l2    : S.
  Variable r r1 r2    : T.
  Variable ls ls1 ls2 : set S.
  Variable s m1 m2    : map_.
   
  (** Working with lists requires types to be decidable*) 
  (* decidability to S,T, pair and map *)
  Axiom (Seq_dec : forall x y: S, {x = y} + {x <> y}).
  Axiom (Teq_dec : forall x y: T, {x = y} + {x <> y}).
  Axiom (Peq_dec : forall x y: pair_, {x = y} + {x <> y}).
  Axiom (Mapeq_dec : forall x y: map_, {x = y} + {x <> y}).

  (* get key and value*)
  Definition getKey (p: pair_)   : S := fst p.
  Definition getValue (p: pair_) : T :=  snd p.

  (* Prop to bool *)
  Definition is_true (b:Prop) : bool :=
   match b with
     | True => true
   end.

  (** check if there is a mapping between the key and a given value *)
  Fixpoint isMappable (s: map_) (l: S) (r: T): Prop :=
        match s with
          | nil     => False
          | p :: ps => if is_true (fst p = l) then 
                          if is_true (snd p = r) then True 
                          else (isMappable ps l r)
                       else (isMappable ps l r)
        end.

  (** sets of unique pairs: If there is a mapping of a key to two values,these
       values must be the same to ensure single mapping *)
  Definition unique s : Prop :=
    forall (l: S) (r1 r2: T), 
      (isMappable s l r1 /\ isMappable s l r2) -> r1 = r2.

  (** reduction of list*)
   Lemma unique_red:
    forall (s: map_) (p: pair_),
      unique (p :: s) -> unique (s).
    Proof.
      intros s0 p HunqList. 
      unfold unique in HunqList. specialize (HunqList l r1 r2).
      unfold unique. intros l0 r0 r3 Hmap.
      destruct Hmap as [Hmap1 Hmap2]. destruct r0, r3. reflexivity.
    Qed.

  (** an auxiliary lemma *)
  Lemma isMappable_elim :
     forall (s: map_) (a: pair_) (l :S) (r: T),
        isMappable (a :: s) l r -> (l = fst a /\ r = snd a)
          \/ isMappable s l r.
  Proof. 
    induction a.
    induction s0.
    - intros l0 r0 HMapList. simpl. simpl in HMapList.
      rewrite l0, a, r0, b. left.
      split. 
      + reflexivity. 
      + reflexivity.
    - intros l0 r0 HMapList. specialize (IHs0 l r).
      left. split.
      + simpl. rewrite l0, a. reflexivity.
      + simpl. rewrite r0, b. reflexivity.
  Qed.

  (* an auxiliary lemma *)
  Lemma isMappable_intro :
     forall (s: map_) (a: pair_) (l :S) (r: T),
        (l = fst a /\ r = snd a)
          \/ isMappable s l r ->  isMappable (a :: s) l r.
  Proof.
  induction a.
    induction s0.
    - intros l0 r0 HMapListElim. inversion HMapListElim.
      + clear HMapListElim. destruct H. simpl in H0. simpl in H.
      rewrite H0. rewrite H. simpl. trivial.
      + simpl in H. contradiction.
    - specialize (IHs0 l r). intros l0 r0 HMapListElim. intuition. rewrite H0.
      rewrite H1. simpl. simpl in H0, H1. rewrite l0, a in H0.
      generalize H0. tauto.
  Qed. 
  
  (** ============================EMPTY_MAP============================= **)
  
  Definition Empty (s: map_) := 
    forall (l : S)(r: T) , ~ isMappable s l r.

  Definition is_map_empty (s : map_ ) : Prop :=
     if is_true (Empty s) then True else False.  
  
  Lemma empty_not_is_mappable:
    forall (s: map_) (l : S)(r: T),
      Empty s -> ~ isMappable s l r. 
  Proof.
   intros s0 l0 r0.  unfold Empty. 
   intros HnotMpb. specialize (HnotMpb l r). rewrite l0, r0.
   rewrite l, r in HnotMpb. assumption.
  Qed.

  Lemma empty_elim:
    forall (s: map_) (p: pair_),
      Empty (p :: s) -> Empty ( p :: nil) /\ Empty s.
  Proof. 
    induction p.
    induction s0.
    - intros HEmptyNil1. split.
        + apply HEmptyNil1.
        + unfold Empty. intros l0 r0. 
          unfold Empty in HEmptyNil1. specialize (HEmptyNil1 l r).
          simpl in HEmptyNil1. unfold not in HEmptyNil1. contradiction.
    - auto.
  Qed. 

  Lemma empty_intro:
    forall (s: map_) (p: pair_),
       Empty s /\ Empty ( p :: nil)  -> Empty (p :: s).
  Proof.
    induction p.
    induction s0.
    - intros HEptConj. destruct HEptConj as [HEmpt1 HEmpt2]. 
      apply HEmpt2.
    - intros HEptConj. destruct HEptConj. intuition.
  Qed.
  
  Lemma is_map_empty_elim: 
    forall (p: pair_) (s: map_),
      is_map_empty (p :: s) = True-> (is_map_empty (p :: nil)) = True 
        /\ (is_map_empty s) = True.
  Proof.
     induction p.
     induction s0.
        - intros HMapEmp. split.
          + assumption.
          + unfold is_map_empty.  simpl. reflexivity.
    - tauto.
  Qed. 

  Lemma is_map_empty2:forall s, Empty s -> is_map_empty s = True.
  Proof.
   intros s0. induction s0. 
    - simpl. intros HEmptNil. reflexivity. 
    - intros HEmpt. apply empty_elim in HEmpt. auto.
  Qed.
 

(*==========================add_map==========================================*)

 Fixpoint add_map (s: map_) (p: pair_): map_ :=
 match s with
  | nil     => set_add Peq_dec p s
  | x :: xs => if is_true(isMappable s (getKey p) (getValue p)) then 
                    set_add Peq_dec p s 
                else s
  end.

  Lemma unique_add:
    forall (s: map_) (p: pair_),
      unique s -> unique (add_map s p).
  Proof.
  induction p.
  induction s0.
  - simpl. unfold unique.
    intros HMpConj1 l0 r3 r4 HMpConj2. 
    rewrite r3, r4. reflexivity.
  - intros HUnqList. apply unique_red in HUnqList.
    apply IHs0 in HUnqList. apply unique_red_add.
    split. 
      + left. destruct a0. rewrite s1, t, a, b. reflexivity.    
      + apply HUnqList.
  Qed.

(*=============================remove map========================*) 

  Fixpoint remove_map (s: map_) (p: pair_) : map_ :=
  match s with
  | nil     => s
  | x :: xs => if is_true(x =p) then
                set_remove Peq_dec p s
                else remove_map xs p
    end.


  Lemma unique_rmv:
    forall (s: map_) (p: pair_),
      unique s -> unique (remove_map s p).
  Proof.
  induction p.
  induction s0.
  - simpl. unfold unique. intros H1 l0 r0 r3 H2.
   specialize (H1 l r1 r2). 
    rewrite r0, r3. reflexivity.
  - intro HUnq. apply unique_red in HUnq. 
    apply IHs0 in HUnq. apply unique_red_rmv.
    split. destruct a0. 
      + left. rewrite s1, t, a, b. reflexivity.    
      + apply HUnq.
  Qed.

(*=======================dom img==========================*)

(* get domain of pairs *)
  Fixpoint dom (m: map_) : set S := 
    match m with 
      | nil     => nil
      | p :: ps => set_add Seq_dec (fst p) (dom ps)
    end.

  (* get image of pairs *)
  Fixpoint img (m: map_) : set T := 
    match m with 
      | nil     => nil
      | p :: ps => set_add Teq_dec (snd p) (img ps)
    end.

(*=============================union map========================*) 
   Definition union_map (s1 s2: map_) : map_:=
          set_union Peq_dec s1 (set_diff Peq_dec s1 s2).

  Lemma union_intro:
    forall (p: pair_) (s1 s2: map_),
      unique (union_map s1 s2)
        -> unique (union_map (p :: s1) s2).
  Proof.
    intros p s1 s2.
    destruct p.
    induction s1.
      - induction s2. 
          + simpl. unfold unique. intros. rewrite r0, r3. reflexivity.
          + simpl. intuition. simpl in H0. 
     - induction s2. 
          + intuition.
          + intuition.
  Qed.

  Lemma unique_union: 
    forall (s1 s2: map_),
      unique(s1) /\ unique(s2) ->
         unique (union_map s1 s2).
  Proof.
  intros. 
  induction s1.
  induction s2. 
  - simpl. destruct H. apply H0.
  - intuition.
  - intuition. apply unique_red in H0. apply union_intro.
    apply H.
      + apply H0.
      + apply H1.
  Qed.
  
   Lemma uniqueUnion:
    forall m1 m2, (unique m1) /\ (unique m2) ->
      (forall l,
        set_In l (dom m1) -> ~(set_In l (dom m2)))
          -> unique(app m1 m2).
  Proof.
    intros. 
    destruct H.
    induction m0.
      - induction m3.
        + specialize (H0 l). simpl in H0. simpl.  intuition.
        + specialize (H0 l). intuition.
      - specialize (H0 l). intuition.
  Qed.

(*=================================union l e r===================================*)
 
Fixpoint union_s (ls1 ls2: set S) : set S:=
    match ls1 with
    | nil => ls2
    | x :: xs => match ls2 with
                  | nil => ls1
                  | y :: ys => if is_true(set_In y ls1) then
                                set_add Seq_dec x ( union_s xs ys)
                                else set_add Seq_dec x (set_add Seq_dec y ( union_s xs ys))
                    end
    end.  
  
  Definition union_t (rs1 rs2: set T) : set T := 
  match rs1 with
    | nil => rs2
    | x :: xs => match rs2 with
                  | nil => rs1
                  | y :: ys => set_union Teq_dec rs1 rs2
                  end
  end. 


(*==========================================================================*)

  (* Indicates whether there is a key *)
  Fixpoint existsT (s: map_) (l: S): Prop :=
      match s with
      | nil     => False
      | x :: xs => (fst x = l) \/ existsT xs l
      end.

   (* can pick up more than one value for a key, if there is *)
  Fixpoint getTs (s: map_) (l: S) : set T :=
   match s with
    | nil     => nil
    | x :: xs => if is_true(fst x = l) 
                  then set_add Teq_dec (snd x) (getTs xs l) 
                 else getTs xs l
    end.

  Definition option_elim (defaulT: T) (o : option T) : T :=
    match o with
      | Some n'=> n'
      | None   =>  defaulT
    end.

  (* get value *) 
  Fixpoint getT (s: map_) (l: S) : option T :=
   match s with
    | nil     => None
    | x :: xs => if is_true (fst x = l) then Some (snd x) else getT xs l
    end.

  (*asset mapping function*)
  Fixpoint maps (defaulT: T) (s: map_) (ls: set S) : set T :=
    match s with
      | nil     => nil
      | c :: cs => match ls with
                    | nil     => nil
                    | x :: xs => if is_true (existsT s x) 
                                    then set_add Teq_dec (option_elim defaulT (getT s x)) 
                                      (maps defaulT s xs)
                                 else (maps defaulT s xs)
                   end
    end.

  (* an auxiliary lemma for UnionMap *)
  Lemma nilMap:
      forall ls defaulT, 
        maps defaulT nil ls = nil.
    Proof.
    induction ls0.
    - simpl. tauto.
    - intro defaulT. specialize (IHls0 defaulT). 
      simpl. reflexivity.
    Qed.

  Lemma nilKeys:
      forall s defaulT, 
        maps defaulT s nil = nil.
    Proof.
    induction s0.
    - simpl. tauto.
    - intros defaulT. specialize (IHs0 defaulT). 
      simpl. reflexivity.
    Qed.

(*Map over union is equivalent to union of maps*) 
  Lemma unionMap:
    forall (s: map_) (ls1 ls2: set S) (defaulT: T), unique s ->
      maps defaulT s (union_s ls1 ls2) 
        = union_t (maps defaulT s ls1) (maps defaulT s ls2).
  Proof.
    induction s0.
      - intros ls0 ls3 defaulT. repeat rewrite nilMap.
        simpl. tauto.
      - intros ls0 ls3 defaulT. 
        specialize (IHs0 ls1 ls2 defaulT).
        intros Hunq. apply unique_red in Hunq.
        apply IHs0 in Hunq. 
Qed.

(*Map over union is equivalent to union of maps*) 
  Lemma unionMap_t2:
    forall (s: map_) (ls1 ls2: set S) (defaulT: T), unique s ->
      maps defaulT s (union_s ls1 ls2) 
        = union_t (maps defaulT s ls1) (maps defaulT s ls2).
  Proof.
  induction ls3.
  - induction ls0.
    + induction s0.
      { intuition. }
      { intuition. }
    + induction s0.
      { intros defaulT. repeat rewrite nilMap. tauto. } 
      { intros defaulT. repeat rewrite nilKeys. simpl. admit. }
 - induction ls3.
    + induction s0.
      { intuition. admit. }
      { intros defaulT. specialize (IHls3 defaulT).
        intros. simpl in IHls3.
        intuition. admit. }
    + induction s0.
      { admit. }
      { intuition. admit. }
Admitted.

End Maps.

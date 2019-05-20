Module Assets.

Import Maps.
Require Import Coq.Lists.ListSet. 

(*Assets*)
Definition Asset : Type := Maps.T.
Definition AssetName : Type := Maps.S.

Variable a a1 a2 a3 : Asset.
Variable aSet S1 S2 : set Asset.

Axiom ANdec_eq : 
  forall x y: Asset, {x = y} + {x <> y}.
Axiom Asset_dec : 
  forall x y: Asset, {x = y} + {x <> y}.

(*Assumption <Assets refinement>*)
(*Inductive assetRef (S1 S2: set Asset) : Prop.*)
Parameter inline assetRef : 
  set Asset -> set Asset -> Prop.

Inductive wfProduct (aSet : set Asset) : Prop.
Definition Product (aSet : set Asset) : Type := wfProduct aSet.

(*Axiom <Asset refinement is pre-order>*)
Axiom assetRefinement:
  forall x y z: set Asset, assetRef x x /\ 
    assetRef x y -> assetRef y z ->  assetRef x z.


(*Axiom 5 <Asset refinement compositionality>*)
Axiom asRefCompositional :
  forall (S1 : set Asset) (S2 : set Asset) (aSet : set Asset),
    (assetRef S1 S2) /\ wfProduct (Maps.union_t  S1 aSet) 
      -> (wfProduct (Maps.union_t  S2 aSet)) 
        /\ assetRef (Maps.union_t  S1 aSet) 
           (Maps.union_t S2 aSet).

End Assets.

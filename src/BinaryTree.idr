module BinaryTree

import Decidable.Order.Strict
import Control.Relation

data Tree a
    = Branch (Tree a) a (Tree a)
    | Leaf 

Functor Tree where
   map f (Branch l x r) = Branch (map f l) (f x) (map f r) 
   map f Leaf = Leaf 

interface Functor f => VerifiedFunctor f where
    preservesIdentity : (x: f a) -> map Prelude.id x = Prelude.id x
    preservesComposition : {0 g : b -> c} -> {0 h : a -> b} ->   
                           (x: f a) -> map (g . h) x = (map g . map h) x

treePreservesIdentity : (x: Tree a) -> map Prelude.id x = Prelude.id x
treePreservesIdentity (Branch l x r) = 
    let ih1 = treePreservesIdentity l
        ih2 = treePreservesIdentity r in
    rewrite ih1 in  
    rewrite ih2 in  
    Refl
treePreservesIdentity Leaf = Refl 

treePreservesComposition : {0 g : b -> c} -> {0 h : a -> b} ->   
                        (x: Tree a) -> map (g . h) x = (map g . map h) x
treePreservesComposition {g} {h} (Branch l x r) =
    let ih1 = treePreservesComposition {g} {h} l   
        ih2 = treePreservesComposition {g} {h} r in
    rewrite ih1 in
    rewrite ih2 in
    Refl 
treePreservesComposition Leaf = Refl 

VerifiedFunctor Tree where
    preservesIdentity = treePreservesIdentity
    preservesComposition = treePreservesComposition


data All : (a -> Type) -> Tree a -> Type where
    AllBranch :
        All p l -> 
        p x -> 
        All p r -> 
        All p (Branch l x r) 
    AllLeaf : All p Leaf 

data OrderedTree : (a -> a -> Type) -> Tree a -> Type where
    OrderedBranch : 
        OrderedTree rel l -> 
        OrderedTree rel r -> 
        All (Not . rel x) l -> 
        All (rel x) r ->
        OrderedTree rel (Branch l x r)   
    OrderedLeaf : 
        OrderedTree rel Leaf

record ValidTree (a: Type) (rel : a -> a -> Type) where
    constructor MkValidTree 
    tree: Tree a
    0 ordered : OrderedTree rel tree

data Insert : a -> Tree a -> Tree a -> Type where
    InsertLeaf : Insert x Leaf (Branch Leaf x Leaf)    
    InsertLeft : Insert x l l' -> Insert x (Branch l y r) (Branch l' y r)   
    InsertRight : Insert x r r' -> Insert x (Branch l y r) (Branch l y r')   

record ValidInsertion 
    {0 a: Type}
    {0 rel: a -> a -> Type}
    (x: a) 
    (before: ValidTree a rel) 
    where
    constructor MkValidInsertion
    after : ValidTree a rel 
    0 insert : Insert x before.tree after.tree  

insertLemma : All p t -> p x -> Insert x t t' -> All p t'    
insertLemma (AllBranch l p r) pred (InsertLeft il) = 
    AllBranch (insertLemma l pred il) p r 
insertLemma (AllBranch l p r) pred (InsertRight ir) = 
    AllBranch l p (insertLemma r pred ir) 
insertLemma AllLeaf pred InsertLeaf = 
    AllBranch AllLeaf pred AllLeaf


insert : (o: StrictOrdered a rel) =>
         (asym: Asymmetric a rel) =>
         (irr: Irreflexive a rel) =>
         (x : a) -> 
         (tree: ValidTree a rel) ->
         (ValidInsertion x tree) 
insert x (MkValidTree (Branch l y r) ot@(OrderedBranch orderedL orderedR lLtY yLtR)) = 
    case order @{o} x y of
        DecLT lt => 
            let (MkValidInsertion (MkValidTree l' orderedL') insertL')
                = insert x (MkValidTree l orderedL) in
            let 0 lLtY' = insertLemma lLtY (asymmetric @{asym} lt) insertL' in
            let 0 ord = OrderedBranch orderedL' orderedR lLtY' yLtR in     
            MkValidInsertion (MkValidTree (Branch l' y r) ord) (InsertLeft insertL')
        DecGT gt => 
            let (MkValidInsertion (MkValidTree r' orderedR') insertR')
                = insert x (MkValidTree r orderedR) in
            let 0 yLtR' = insertLemma yLtR gt insertR' in
            let 0 ord = OrderedBranch orderedL orderedR' lLtY yLtR' in     
            MkValidInsertion (MkValidTree (Branch l y r') ord) (InsertRight insertR')
        DecEQ eq => 
            let (MkValidInsertion (MkValidTree l' orderedL') insertL')
                = insert x (MkValidTree l orderedL) in
            let 0 lLtY' = insertLemma lLtY (rewrite eq in irreflexive @{irr}) insertL' in
            let 0 ord = OrderedBranch orderedL' orderedR lLtY' yLtR in     
            MkValidInsertion (MkValidTree (Branch l' y r) ord) (InsertLeft insertL')
insert x (MkValidTree Leaf ordered) = 
    let ord = OrderedBranch OrderedLeaf OrderedLeaf AllLeaf AllLeaf in  
    MkValidInsertion (MkValidTree (Branch Leaf x Leaf) ord) InsertLeaf

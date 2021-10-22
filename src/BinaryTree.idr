module BinaryTree

import Control.Order 

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

data Insert : a -> Tree a -> Tree a -> Type where
    InsertLeaf : Insert x Leaf (Branch Leaf x Leaf)    
    InsertLeft : Insert x l l' -> Insert x (Branch l y r) (Branch l' y r)   
    InsertRight : Insert x r r' -> Insert x (Branch l y r) (Branch l y r')   

data Lte : (a -> a -> Type) -> a -> Tree a -> Type where
    LteBranch : {0 x, y: a} -> Lte rel x l -> rel x y -> Lte rel x r -> Lte rel x (Branch l y r)
    LteLeaf : Lte con x Leaf 

data OrderedTree : (a -> a -> Type) -> Tree a -> Type where
    OrderedBranch : 
        OrderedTree rel l -> 
        OrderedTree rel r -> 
        Lte (flip rel) x l -> 
        Lte rel x r ->
        OrderedTree rel (Branch l x r)   
    OrderedLeaf : 
        OrderedTree rel Leaf

record ValidTree (a: Type) (tree: Tree a) (rel : a -> a -> Type) where
    constructor MkValidTree 
    ordered : OrderedTree rel tree

insertLemma : {0 rel : a -> a -> Type} -> rel y x -> Lte rel y t -> Insert x t t' -> Lte rel y t' 
insertLemma lte _ InsertLeaf = 
    LteBranch LteLeaf lte LteLeaf 
insertLemma lte (LteBranch l p r) (InsertLeft il) = 
    LteBranch (insertLemma lte l il) p r 
insertLemma lte (LteBranch l p r) (InsertRight ir) = 
    LteBranch l p (insertLemma lte r ir) 

insert : (o : StronglyConnex a rel) => 
         (x: a) -> 
         (tree: Tree a) -> 
         ValidTree a tree rel -> 
         (tree': Tree a ** (ValidTree a tree' rel, Insert x tree tree'))
insert x Leaf (MkValidTree ordered) = 
    let ordered' = OrderedBranch OrderedLeaf OrderedLeaf LteLeaf LteLeaf in
    (Branch Leaf x Leaf ** (MkValidTree ordered', InsertLeaf))
insert x (Branch l y r) (MkValidTree (OrderedBranch orderedL orderedR lLteY yLteR)) = 
    case order @{o} x y of
        Left xLteY => 
            let (l' ** (MkValidTree orderedL', insertL')) = insert x l (MkValidTree orderedL) in
            let lLteY' = insertLemma xLteY lLteY insertL' in   
            let ordered' = OrderedBranch orderedL' orderedR lLteY' yLteR in
            (Branch l' y r ** (MkValidTree ordered', InsertLeft insertL'))
        Right yLteX =>             
            let (r' ** (MkValidTree orderedR', insertR')) = insert x r (MkValidTree orderedR) in
            let yLteR' = insertLemma yLteX yLteR insertR' in   
            let ordered' = OrderedBranch orderedL orderedR' lLteY yLteR' in
            (Branch l y r' ** (MkValidTree ordered', InsertRight insertR'))
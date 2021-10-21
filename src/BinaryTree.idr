module BinaryTree

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

treePreserversIdentity : (x: Tree a) -> map Prelude.id x = Prelude.id x
treePreserversIdentity (Branch l x r) = 
    let ih1 = treePreserversIdentity l
        ih2 = treePreserversIdentity r in
    rewrite ih1 in  
    rewrite ih2 in  
    Refl
treePreserversIdentity Leaf = Refl 

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
    preservesIdentity = treePreserversIdentity
    preservesComposition = treePreservesComposition

data Path : a -> Tree a -> Type where
    End : Path x (Branch l x r)    
    Left : Path x l -> Path x (Branch l _ r)   
    Right : Path x r -> Path x (Branch l _ r)   


insert : Ord a => (x: a) -> Tree a -> (t: Tree a ** Path x t)   
insert x Leaf = (Branch Leaf x Leaf ** End)  
insert x (Branch l y r) with (x <= y)
    _ | True = 
        let (l' ** leftPath) = insert x l in
        (Branch l' y r ** Left leftPath) 
    _ | _ =  
        let (r' ** rightPath) = insert x r in
        (Branch l y r' ** Right rightPath) 
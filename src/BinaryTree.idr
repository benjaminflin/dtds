module BinaryTree

import Decidable.Order.Strict
import Control.Relation
import Data.Fin
import Data.Nat
import Decidable.Equality

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

absdiff : Nat -> Nat -> Nat   
absdiff x y = maximum (minus x y) (minus y x)  

height : Tree a -> Nat
height (Branch l _ r) = 1 + maximum (height l) (height r)
height Leaf = 0

BalanceFactor : Tree a -> Tree a -> Nat -> Type
BalanceFactor l r n = (diff: Fin n ** finToNat diff = absdiff (height l) (height r))  

data BalancedTree : Nat -> Tree a -> Type where
    BalancedBranch :
        BalancedTree n l -> 
        BalancedTree n r -> 
        BalanceFactor l r n ->
        BalancedTree n (Branch l x r) 
    BalancedLeaf : BalancedTree n Leaf

data Insert : a -> Tree a -> Tree a -> Type where
    InsertLeaf : Insert x Leaf (Branch Leaf x Leaf)    
    InsertLeft : Insert x l l' -> Insert x (Branch l y r) (Branch l' y r)   
    InsertRight : Insert x r r' -> Insert x (Branch l y r) (Branch l y r')   

data Rotation : Tree a -> Tree a -> Type where 
    SingleLeft : Rotation 
                    (Branch l1 x (Branch l2 y (Branch l3 z r))) 
                    (Branch (Branch l1 x l2) y (Branch l3 z r))
    SingleRight : Rotation 
                    (Branch (Branch (Branch l x r1) y r2) z r3) 
                    (Branch (Branch l x r1) y (Branch r2 z r3))
    DoubleLeft : Rotation
                    (Branch l1 x (Branch (Branch l2 y r1) z r2))
                    (Branch (Branch l1 x l2) y (Branch r1 z r2))  
    DoubleRight : Rotation
                    (Branch (Branch l1 x (Branch l2 y r1)) z r2) 
                    (Branch (Branch l1 x l2) y (Branch r1 z r2))  

data Balance : Tree a -> Tree a -> Type where
    NoRotate : Balance t t  
    Rotate : Rotation t t' -> Balance t t'
    BalanceLeft : Balance l l' -> Balance (Branch l x r) (Branch l' x r)
    BalanceRight : Balance r r' -> Balance (Branch l x r) (Branch l x r')

data Path : a -> Tree a -> Type where
    Stop : Path x (Branch l x r)   
    GoLeft : Path x l -> Path x (Branch l _ r) 
    GoRight : Path x r -> Path x (Branch l _ r) 

pathInsert : Insert x t t' -> Path x t'
pathInsert InsertLeaf = Stop 
pathInsert (InsertLeft il) = GoLeft $ pathInsert il
pathInsert (InsertRight ir) = GoRight $ pathInsert ir 

pathInsertRotation : Insert x t1 t2 -> Rotation t2 t3 -> Path x t3   
pathInsertRotation InsertLeaf SingleLeft impossible
pathInsertRotation InsertLeaf SingleRight impossible
pathInsertRotation InsertLeaf DoubleLeft impossible
pathInsertRotation InsertLeaf DoubleRight impossible
pathInsertRotation (InsertLeft il) SingleLeft = GoLeft $ GoLeft $ pathInsert il 
pathInsertRotation (InsertLeft il) SingleRight = 
    case il of
        InsertLeft il' => GoLeft $ pathInsert il' 
        InsertRight ir' => GoRight $ GoLeft $ pathInsert ir' 
pathInsertRotation (InsertLeft il) DoubleLeft = GoLeft $ GoLeft $ pathInsert il 
pathInsertRotation (InsertLeft il) DoubleRight = 
    case il of
        InsertLeft il' => GoLeft $ GoLeft $ pathInsert il' 
        InsertRight ir' => 
            case ir' of
                InsertLeaf => Stop 
                InsertLeft il'' => GoLeft $ GoRight $ pathInsert il'' 
                InsertRight ir'' => GoRight $ GoLeft $ pathInsert ir'' 
pathInsertRotation (InsertRight ir) SingleRight = GoRight $ GoRight $ pathInsert ir
pathInsertRotation (InsertRight ir) SingleLeft = 
    case ir of
        InsertRight ir' => GoRight $ pathInsert ir' 
        InsertLeft il' => GoLeft $ GoRight $ pathInsert il' 
pathInsertRotation (InsertRight ir) DoubleLeft = 
    case ir of
        InsertRight ir' => GoRight $ GoRight $ pathInsert ir' 
        InsertLeft il' =>
            case il' of
                InsertLeaf => Stop 
                InsertRight ir'' => GoRight $ GoLeft $ pathInsert ir'' 
                InsertLeft il'' => GoLeft $ GoRight $ pathInsert il'' 
pathInsertRotation (InsertRight ir) DoubleRight = GoRight $ GoRight $ pathInsert ir

weakenEq : (n: Fin k) -> finToNat n = finToNat (weaken n) 
weakenEq FZ = Refl 
weakenEq (FS x) = rewrite weakenEq x in Refl

weakenBalancedTree : BalancedTree n t -> BalancedTree (S n) t 
weakenBalancedTree (BalancedBranch l r (diff ** pfBal)) = 
    let pfEq = weakenEq diff in   
    BalancedBranch (weakenBalancedTree l) 
                   (weakenBalancedTree r) 
                   (weaken diff ** rewrite sym pfEq in pfBal)
weakenBalancedTree BalancedLeaf = BalancedLeaf 

maxEither : (a,b : Nat) -> Either (maximum a b = a) (maximum a b = b)
maxEither 0 b = Right Refl 
maxEither a 0 = Left (rewrite maximumZeroNLeft a in Refl)
maxEither (S j) (S k) = 
    case maxEither j k of
        Left p => rewrite p in Left Refl 
        Right p => rewrite p in Right Refl

-- maxSuccEqLeft : (a, b: Nat) -> maximum a b = a -> maximum (S a) b = S a
-- maxSuccEqLeft 0 b maxLeft = rewrite maxLeft in Refl 
-- maxSuccEqLeft a 0 maxLeft = Refl
-- maxSuccEqLeft (S j) (S k) maxLeft =
--     let ih = maxSuccEqLeft j k (succInjective (maximum j k) j maxLeft)
--     in rewrite ih in Refl 

maxSuccLemmaLeft : 
    (a, b: Nat) -> 
    Either (maximum (S a) b = maximum a b) (maximum (S a) b = S (maximum a b))
maxSuccLemmaLeft a 0 = Right $ rewrite maximumZeroNLeft a in Refl 
maxSuccLemmaLeft 0 (S k) = Left Refl 
maxSuccLemmaLeft (S j) (S k) = 
    case maxSuccLemmaLeft j k of
        Left maxEq => rewrite maxEq in Left Refl 
        Right maxSucc => rewrite maxSucc in Right Refl

total
minusLemma : (a, b: Nat) -> S k = minus a b -> minus b a = 0
minusLemma 0 b eq impossible 
minusLemma (S j) 0 eq = Refl 
minusLemma (S j) (S i) eq = minusLemma j i eq

total
minusSuccLeft : (a, b: Nat) -> Either (minus (S a) b = 0) (minus (S a) b = S (minus a b))
minusSuccLeft 0 0 = Right Refl 
minusSuccLeft 0 (S k) = Left Refl 
minusSuccLeft (S k) 0 = Right Refl 
minusSuccLeft (S j) (S k) = minusSuccLeft j k

total
absDiffLemma : (a, b: Nat) -> Either (S (absdiff (S a) b) = absdiff a b) (absdiff (S a) b = S (absdiff a b))
absDiffLemma 0 0 = Right Refl 
absDiffLemma 0 (S k) = rewrite minusZeroRight k in Left Refl 
absDiffLemma (S k) 0 = Right Refl 
absDiffLemma (S j) (S k) = absDiffLemma j k 


total
heightLemma : {t,t': Tree a} -> Insert x t t' -> Either (height t' = height t) (height t' = S (height t))
heightLemma InsertLeaf = Right Refl 
heightLemma {t=Branch l _ r} (InsertLeft il) = 
    case heightLemma il of
        Left sameHeight => 
            rewrite sameHeight in Left Refl 
        Right succHeight => 
            rewrite succHeight in 
            case maxSuccLemmaLeft (height l) (height r) of
                Left maxEq => rewrite maxEq in Left Refl
                Right maxSucc => rewrite maxSucc in Right Refl 
heightLemma {t=Branch l _ r} (InsertRight ir) = 
    case heightLemma ir of
        Left sameHeight => 
            rewrite sameHeight in Left Refl 
        Right succHeight => 
            rewrite succHeight in
            rewrite maximumCommutative (height l) (S (height r)) in 
            case maxSuccLemmaLeft (height r) (height l) of
                Left maxEq => 
                    rewrite maxEq in 
                        Left $ rewrite maximumCommutative (height l) (height r) in Refl 
                Right maxSucc => 
                    rewrite maxSucc in 
                        Right $ rewrite maximumCommutative (height l) (height r) in Refl 

balanceLemma : 
    {t,t',t'': Tree a} ->
    Insert x t t' -> 
    BalancedTree 2 t -> 
    (t'': Tree a ** (Balance t' t'', BalancedTree 2 t''))
balanceLemma InsertLeaf bal = 
    (Branch Leaf x Leaf ** (NoRotate, BalancedBranch BalancedLeaf BalancedLeaf (0 ** Refl)))
balanceLemma {t=Branch l _ r} {t'=Branch l' y r} (InsertLeft il) (BalancedBranch bl br bf) = 
    case balanceLemma il bl of
        (_ ** (NoRotate, bl')) => 
            case heightLemma il of  
                Left sameHeight => 
                    (Branch l' y r ** (NoRotate, BalancedBranch bl' br (rewrite sameHeight in bf)))
                Right succHeight => 
                    let (diff ** pfDiff) = bf in
                    case diff of
                        0 => 
                            let bf' = 
                                rewrite succHeight in 
                                    case absDiffLemma (height l) (height r) of 
                                        Left pred => 
                                            let contra = trans pfDiff $ sym pred in 
                                            void $ SIsNotZ $ sym contra
                                        Right suc => 
                                            rewrite suc in (1 ** rewrite sym pfDiff in Refl)
                            in
                            (Branch l' y r ** (NoRotate, BalancedBranch bl' br bf'))
                        1 => ?bal_1 -- will require balancing
        (l'' ** (bal', bl')) => ?bal_2
balanceLemma (InsertRight ir) bal = ?bal_ir

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

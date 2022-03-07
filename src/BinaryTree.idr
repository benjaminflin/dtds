module BinaryTree

import Decidable.Order.Strict
-- import Control.Relation
import Data.Fin
import Data.Nat
import Decidable.Equality

data Bounded1 : Nat -> Nat -> Nat -> Type where   
    Plus : Bounded1 n (S n) (S n)
    Equal : Bounded1 n n n
    Minus : Bounded1 (S n) n (S n)

data Extrema : Type -> Type where
    L : Extrema a
    R : Extrema a
    B : a -> Extrema a     

data LTE : (a : Type) -> (rel : a -> a -> Type) -> (x : Extrema a) -> (y : Extrema a) -> Type where
    XLTER : LTE a rel x R   
    LLTEX : LTE a rel L y
    XLTEY : {x, y : a} -> rel x y -> LTE a rel (B x) (B y)

data Tree : 
    (0 k : Type) 
    -> (0 rel : k -> k -> Type) 
    -> (0 l : Extrema k) 
    -> (0 r : Extrema k) 
    -> Nat 
    -> (v : Type -> Type) 
    -> Type where
    Branch : 
        (bounds : Bounded1 hl hr h) ->
        (key : k) ->
        Tree k rel l (B key) hl v -> v k -> Tree k rel (B key) r hr v -> Tree k rel l r (S h) v
    Leaf : (0 ord : LTE k rel l r) -> Tree k rel l r 0 v 

NDTree : (k : Type) -> (k -> k -> Type) -> (l, r : Extrema k) -> Nat -> Type -> Type 
NDTree k rel l r n v = Tree k rel l r n (const v)

mapTree : {0 v, w : Type -> Type} -> (v k -> w k) -> Tree k rel h l r v -> Tree k rel h l r w
mapTree f (Branch b k l v r) = Branch b k (mapTree f l) (f v) (mapTree f r) 
mapTree f (Leaf o) = Leaf o

Functor (NDTree k rel l r h) where 
    map = mapTree 

data MaybeOneMore : Nat -> Nat -> Type where
    NotOneMore : MaybeOneMore (S n) (S n)
    OneMore : MaybeOneMore n (S n)

record TreeResult (0 k : Type) (0 rel : k -> k -> Type) (0 l : Extrema k) (0 r : Extrema k) (h : Nat) (v : Type -> Type) where 
    constructor MkTreeResult 
    {0 h' : Nat}
    mOneMore : MaybeOneMore h h' 
    tree : Tree k rel l r h' v 


balanceLeft : 
    Bounded1 hl hr h 
    -> (key: k)
    -> Tree k rel l (B key) hl v 
    -> v k
    -> Tree k rel (B key) r hr v
    -> TreeResult k rel l (B key) hl v
    -> TreeResult k rel l r (S h) v
balanceLeft bounds key left val right 
    (MkTreeResult NotOneMore left') = MkTreeResult NotOneMore (Branch bounds key left' val right) 
-- Double rotations
balanceLeft bounds key left val d 
    (MkTreeResult OneMore (Branch Plus key' a val' (Branch Plus key'' b val'' c))) = 
        case bounds of
            Plus => 
                MkTreeResult NotOneMore 
                    (Branch Equal key (Branch Plus key' a val' (Branch Plus key'' b val'' c)) val d)
            Equal => 
                MkTreeResult OneMore
                      (Branch Plus key'' (Branch Minus key' a val' b) val'' (Branch Plus key c val d))  
            Minus => 
                MkTreeResult NotOneMore
                    (Branch Equal key'' (Branch Minus key' a val' b) val'' (Branch Equal key c val d)) 
balanceLeft bounds key left val d 
    (MkTreeResult OneMore (Branch Plus key' a val' (Branch Equal key'' b val'' c))) = 
        case bounds of
            Plus => 
                MkTreeResult NotOneMore 
                    (Branch Equal key (Branch Plus key' a val' (Branch Equal key'' b val'' c)) val d) 
            Equal => 
                MkTreeResult OneMore 
                    (Branch Plus key'' (Branch Equal key' a val' b) val'' (Branch Plus key c val d))  
            Minus => 
                MkTreeResult NotOneMore 
                    (Branch Equal key'' (Branch Equal key' a val' b) val'' (Branch Equal key c val d))  
balanceLeft bounds key left val d 
    (MkTreeResult OneMore (Branch Plus key' a val' (Branch Minus key'' b val'' c))) =
        case bounds of
            Plus => 
                MkTreeResult NotOneMore 
                    (Branch Equal key (Branch Plus key' a val' (Branch Minus key'' b val'' c)) val d)  
            Equal => 
                MkTreeResult OneMore 
                    (Branch Minus key (Branch Plus key' a val' (Branch Minus key'' b val'' c)) val d) 
            Minus =>
                MkTreeResult NotOneMore 
                    (Branch Equal key'' (Branch Equal key' a val' b) val'' (Branch Plus key c val d))   
-- Single rotations
balanceLeft bounds key left val c 
    (MkTreeResult OneMore (Branch Equal key' a val' b)) = 
        case bounds of
            Plus => MkTreeResult NotOneMore (Branch Equal key (Branch Equal key' a val' b) val c)  
            Equal => MkTreeResult OneMore (Branch Minus key (Branch Equal key' a val' b) val c) 
            Minus => MkTreeResult OneMore (Branch Plus key' a val' (Branch Minus key b val c))
balanceLeft bounds key left val c 
    (MkTreeResult OneMore (Branch Minus key' a val' b)) =
        case bounds of
            Plus => MkTreeResult NotOneMore (Branch Equal key (Branch Minus key' a val' b) val c) 
            Equal => MkTreeResult OneMore (Branch Plus key' a val' (Branch Plus key b val c)) 
            Minus => MkTreeResult NotOneMore (Branch Equal key' a val' (Branch Equal key b val c))

balanceRight : 
    Bounded1 hl hr h 
    -> (key: k)
    -> Tree k rel l (B key) hl v 
    -> v k
    -> Tree k rel (B key) r hr v
    -> TreeResult k rel (B key) r hr v
    -> TreeResult k rel l r (S h) v
balanceRight bounds key left val right res = ?balRight


insertWithBounds : 
    StrictOrdered k rel =>
    {l, r : Extrema k}
    -> (key: k)
    -> v k 
    -> (pfBoundsL : LTE k rel l (B key))
    -> (pfBoundsR : LTE k rel (B key) r)
    -> Tree k rel l r h v 
    -> TreeResult k rel l r h v 
insertWithBounds @{o} k1 v1 bL bR (Branch {h} bounds k2 l v2 r) = 
    case order @{o} k1 k2 of 
        (DecLT lt) => balanceLeft bounds k2 l v2 r (insertWithBounds @{o} k1 v1 bL (XLTEY lt) l) 
        (DecEQ Refl) => MkTreeResult NotOneMore (Branch bounds k1 l v2 r)
        (DecGT gt) => balanceRight bounds k2 l v2 r (insertWithBounds @{o} k1 v1 (XLTEY gt) bR r)
insertWithBounds k v bL bR (Leaf ord) = MkTreeResult OneMore (Branch Equal k (Leaf bL) v (Leaf bR))

-- insert : StrictOrdered k rel => k -> v k -> Tree k rel L R h v -> Either (Tree k rel L R h v) (Tree k rel L R (S h) v) 
-- insert k v tree = insertWithBounds k v LLTEX XLTER tree


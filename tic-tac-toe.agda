module tic-tac-toe where

open import Data.Maybe hiding (map)
open import Data.Nat
open import Data.Nat.Properties
open import Data.List 
open import Data.Empty using (⊥-elim)
open import Data.Sum hiding (map) 
open import Data.Product hiding (map)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Bool

data Player : Set where 
    x o : Player 

-- A Mark on a tic-tac-toe grid may be empty if the grid is not filled 
Mark : Set
Mark = Maybe Player 

-- A n × n tic-tac-toe grid
record Grid : Set where 
    constructor grid
    field
        top-left top-middle top-right : Mark 
        middle-left middle-middle middle-right : Mark 
        bottom-left bottom-middle bottom-right : Mark 

record Fillable (a : Set) : Set where    
    field fill : a → ℕ   

open Fillable {{...}} public

instance 
    filled-mark : Fillable Mark 
    fill {{filled-mark}} (just _) = 1  
    fill {{filled-mark}} nothing = 0  

instance
    filled-grid : Fillable Grid
    fill {{filled-grid}} 
        (grid top-left    top-middle    top-right 
              middle-left middle-middle middle-right 
              bottom-left bottom-middle bottom-right) 
        = sum (map fill grid-list)
            where
                grid-list : List Mark
                grid-list
                    = top-left ∷ top-middle ∷ top-right 
                    ∷ middle-left ∷ middle-middle ∷ middle-right 
                    ∷ bottom-left ∷ bottom-middle ∷ bottom-right 
                    ∷ []



fill≤1 : (m : Mark) → fill m ≤ 1    
fill≤1 (just x₁) = s≤s z≤n
fill≤1 nothing = z≤n

Filled : Grid → Set  
Filled g = fill g ≡ 9

fill-list-bound : ∀ l → sum (map fill l) ≤ length l 
fill-list-bound [] = z≤n
fill-list-bound (m ∷ ms) = +-mono-≤ (fill≤1 m) (fill-list-bound ms)
    
fill-lemma : ∀ g → Filled g ⊎ fill g ≤ 8 
fill-lemma (grid (just _) (just _) (just _) (just _) (just _) (just _) (just _) (just _) (just _)) = inj₁ refl
fill-lemma (grid nothing b c d e f g h i) = inj₂ (fill-list-bound (b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ [])) 
fill-lemma (grid a nothing c d e f g h i) = inj₂ (fill-list-bound (a ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ [])) 
fill-lemma (grid a b nothing d e f g h i) = inj₂ (fill-list-bound (a ∷ b ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []))
fill-lemma (grid a b c nothing e f g h i) = inj₂ (fill-list-bound (a ∷ b ∷ c ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []))
fill-lemma (grid a b c d nothing f g h i) = inj₂ (fill-list-bound (a ∷ b ∷ c ∷ d ∷ f ∷ g ∷ h ∷ i ∷ []))
fill-lemma (grid a b c d e nothing g h i) = inj₂ (fill-list-bound (a ∷ b ∷ c ∷ d ∷ e ∷ g ∷ h ∷ i ∷ []))
fill-lemma (grid a b c d e f nothing h i) = inj₂ (fill-list-bound (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ h ∷ i ∷ []))
fill-lemma (grid a b c d e f g nothing i) = inj₂ (fill-list-bound (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ i ∷ []))
fill-lemma (grid a b c d e f g h nothing) = inj₂ (fill-list-bound (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []))

Unfilled : Grid → Set  
Unfilled g = ¬ (Filled g)

filledDec : ∀ g → Dec (Filled g)
filledDec g with fill-lemma g 
... | inj₁ ≡9 = record { does = true; proof = ofʸ ≡9 }
... | inj₂ ≤8 = record { does = false; proof = ofⁿ (helper ≤8) }
    where
        helper : ∀ {k} {n} → n ≤ k → n ≢ suc k
        helper {n = zero} p = λ ()
        helper {n = suc n} (s≤s p) = λ r → helper {n = n} p (suc-injective r) 

empty-grid : Grid  
empty-grid = grid nothing nothing nothing nothing nothing nothing nothing nothing nothing 

empty-grid-unfilled : Unfilled empty-grid  
empty-grid-unfilled = λ ()

won : Grid → Maybe Player       
won (grid (just x) (just x) (just x) middle-left middle-middle middle-right bottom-left bottom-middle bottom-right) = just x  
won (grid (just o) (just o) (just o) middle-left middle-middle middle-right bottom-left bottom-middle bottom-right) = just o  
won (grid top-left top-middle top-right (just x) (just x) (just x) bottom-left bottom-middle bottom-right) = just x
won (grid top-left top-middle top-right (just o) (just o) (just o) bottom-left bottom-middle bottom-right) = just o
won (grid top-left top-middle top-right middle-left middle-middle middle-right (just x) (just x) (just x)) = just x 
won (grid top-left top-middle top-right middle-left middle-middle middle-right (just o) (just o) (just o)) = just o 
won (grid (just x) top-middle top-right (just x) middle-middle middle-right (just x) bottom-middle bottom-right) = just x 
won (grid (just o) top-middle top-right (just o) middle-middle middle-right (just o) bottom-middle bottom-right) = just o
won (grid top-left (just x) top-right middle-left (just x) middle-right bottom-left (just x) bottom-right) = just x
won (grid top-left (just o) top-right middle-left (just o) middle-right bottom-left (just o) bottom-right) = just o
won (grid top-left top-middle (just x) middle-left middle-middle (just x) bottom-left bottom-middle (just x)) = just x
won (grid top-left top-middle (just o) middle-left middle-middle (just o) bottom-left bottom-middle (just o)) = just o
won (grid (just x) top-middle top-right middle-left (just x) middle-right bottom-left bottom-middle (just x)) = just x
won (grid (just o) top-middle top-right middle-left (just o) middle-right bottom-left bottom-middle (just o)) = just o
won (grid top-left top-middle (just x) middle-left (just x) middle-right (just x) bottom-middle bottom-right) = just x
won (grid top-left top-middle (just o) middle-left (just o) middle-right (just o) bottom-middle bottom-right) = just o
won _ = nothing

private 
    variable
        a b c d e f g h i : Mark 

data Move (p : Player) : Grid → Grid → Set where
    move-top-left : Move p (grid nothing b c d e f g h i) (grid (just p) b c d e f g h i)
    move-top-middle : Move p (grid a nothing c d e f g h i) (grid a (just p) c d e f g h i)
    move-top-right : Move p (grid a b nothing d e f g h i) (grid a b (just p) d e f g h i)
    move-middle-left : Move p (grid a b c nothing e f g h i) (grid a b c (just p) e f g h i)
    move-middle-middle : Move p (grid a b c d nothing f g h i) (grid a b c d (just p) f g h i)
    move-middle-right : Move p (grid a b c d e nothing g h i) (grid a b c d e (just p) g h i)
    move-bottom-left : Move p (grid a b c d e f nothing h i) (grid a b c d e f (just p) h i)
    move-bottom-middle : Move p (grid a b c d e f g nothing i) (grid a b c d e f g (just p) i)
    move-bottom-right : Move p (grid a b c d e f g h nothing) (grid a b c d e f g h (just p))

-- If this were longer, I'd might consider generalizing the rewrite rule
move-lemma : ∀ {p g g'} → Move p g g' → fill g' ≡ suc (fill g)
move-lemma move-top-left = refl
move-lemma (move-top-middle {a} {c} {d} {e} {f} {g} {h} {i}) 
    rewrite +-suc (fill a) (sum (map fill (c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []))) = refl
move-lemma (move-top-right {a} {b} {d} {e} {f} {g} {h} {i})
    rewrite +-suc (fill b) (sum (map fill (d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill a) (sum (map fill (b ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []))) = refl
move-lemma (move-middle-left {a} {b} {c} {e} {f} {g} {h} {i}) 
    rewrite +-suc (fill c) (sum (map fill (e ∷ f ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill b) (sum (map fill (c ∷ e ∷ f ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill a) (sum (map fill (b ∷ c ∷ e ∷ f ∷ g ∷ h ∷ i ∷ [])))
    = refl
move-lemma (move-middle-middle {a} {b} {c} {d} {f} {g} {h} {i})
    rewrite +-suc (fill d) (sum (map fill (f ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill c) (sum (map fill (d ∷ f ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill b) (sum (map fill (c ∷ d ∷ f ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill a) (sum (map fill (b ∷ c ∷ d ∷ f ∷ g ∷ h ∷ i ∷ [])))
    = refl
move-lemma (move-middle-right {a} {b} {c} {d} {e} {g} {h} {i}) 
    rewrite +-suc (fill e) (sum (map fill (g ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill d) (sum (map fill (e ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill c) (sum (map fill (d ∷ e ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill b) (sum (map fill (c ∷ d ∷ e ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill a) (sum (map fill (b ∷ c ∷ d ∷ e ∷ g ∷ h ∷ i ∷ [])))
    = refl
move-lemma (move-bottom-left {a} {b} {c} {d} {e} {f} {h} {i})
    rewrite +-suc (fill f) (sum (map fill (h ∷ i ∷ [])))
    rewrite +-suc (fill e) (sum (map fill (f ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill d) (sum (map fill (e ∷ f ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill c) (sum (map fill (d ∷ e ∷ f ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill b) (sum (map fill (c ∷ d ∷ e ∷ f ∷ h ∷ i ∷ [])))
    rewrite +-suc (fill a) (sum (map fill (b ∷ c ∷ d ∷ e ∷ f ∷ h ∷ i ∷ [])))
    = refl
move-lemma (move-bottom-middle {a} {b} {c} {d} {e} {f} {g} {i}) 
    rewrite +-suc (fill g) (sum (map fill (i ∷ [])))
    rewrite +-suc (fill f) (sum (map fill (g ∷ i ∷ [])))
    rewrite +-suc (fill e) (sum (map fill (f ∷ g ∷ i ∷ [])))
    rewrite +-suc (fill d) (sum (map fill (e ∷ f ∷ g ∷ i ∷ [])))
    rewrite +-suc (fill c) (sum (map fill (d ∷ e ∷ f ∷ g ∷ i ∷ [])))
    rewrite +-suc (fill b) (sum (map fill (c ∷ d ∷ e ∷ f ∷ g ∷ i ∷ [])))
    rewrite +-suc (fill a) (sum (map fill (b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ i ∷ [])))
    = refl
move-lemma (move-bottom-right {a} {b} {c} {d} {e} {f} {g} {h}) 
    rewrite +-suc (fill h) 0
    rewrite +-suc (fill g) (sum (map fill (h ∷ [])))
    rewrite +-suc (fill f) (sum (map fill (g ∷ h ∷ [])))
    rewrite +-suc (fill e) (sum (map fill (f ∷ g ∷ h ∷ [])))
    rewrite +-suc (fill d) (sum (map fill (e ∷ f ∷ g ∷ h ∷ [])))
    rewrite +-suc (fill c) (sum (map fill (d ∷ e ∷ f ∷ g ∷ h ∷ [])))
    rewrite +-suc (fill b) (sum (map fill (c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])))
    rewrite +-suc (fill a) (sum (map fill (b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])))
    = refl

CatsGame : Grid → Set  
CatsGame g = Filled g × won g ≡ nothing  

suc-∣a-b∣ : ∀ {a b} → a ≥ b → suc ∣ a - b ∣ ≡ ∣ suc a - b ∣
suc-∣a-b∣ {zero} {zero} p = refl
suc-∣a-b∣ {suc a} {zero} p = refl
suc-∣a-b∣ {suc a} {suc b} (s≤s p) = suc-∣a-b∣ p

match : (∀ g → Unfilled g → ∃[ g' ] Move x g g') → (∀ g → Unfilled g → ∃[ g' ] Move o g g') → Maybe Player 
match fˣ fᵒ = go 9 x empty-grid empty-grid-unfilled refl ≤-refl
    where
    -- n and it's related proofs are needed to appease the termination checker 
    -- so that go decreases it's argument n
    -- we basically prove that every game must end by the 9th move 
    go : ∀ n → Player → (g : Grid) → Unfilled g → fill g ≡ ∣ 9 - n ∣ → 9 ≥ n → Maybe Player  
    go zero _ g u p _ = ⊥-elim (u p)  
    go (suc n) x g u p (s≤s 8≥n) 
        with (filledDec (proj₁ (fˣ g u)))
    ... | yes filled = won (proj₁ (fˣ g u)) 
    ... | no unfilled = 
        let p' = trans (trans (move-lemma (proj₂ (fˣ g u))) (cong suc p)) (suc-∣a-b∣ (s≤s 8≥n)) in
        go n o (proj₁ (fˣ g u)) unfilled p' (≤-step 8≥n)
    go (suc n) o g u p (s≤s 8≥n) 
        with (filledDec (proj₁ (fᵒ g u))) 
    ... | yes filled = won (proj₁ (fᵒ g u)) 
    ... | no unfilled = 
        let p' = trans (trans (move-lemma (proj₂ (fᵒ g u))) (cong suc p)) (suc-∣a-b∣ (s≤s 8≥n)) in
        go n x (proj₁ (fᵒ g u)) unfilled p' ((≤-step 8≥n))
    

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

Mark : Set
Mark = Maybe Player 

record Grid : Set where 
    constructor grid
    field
        top-left top-middle top-right : Mark 
        middle-left middle-middle middle-right : Mark 
        bottom-left bottom-middle bottom-right : Mark 
    
filled' : Mark → ℕ   
filled' (just _) = 1 
filled' nothing = 0 

filled : Grid → ℕ 
filled (grid top-left top-middle top-right middle-left middle-middle middle-right bottom-left bottom-middle bottom-right) 
    = sum (map filled' grid-list)
    where
        grid-list : List Mark
        grid-list
            = top-left 
            ∷ top-middle 
            ∷ top-right 
            ∷ middle-left 
            ∷ middle-middle 
            ∷ middle-right 
            ∷ bottom-left 
            ∷ bottom-middle 
            ∷ bottom-right 
            ∷ []


filled'≤1 : ∀ m → filled' m ≤ 1    
filled'≤1 (just x₁) = s≤s z≤n
filled'≤1 nothing = z≤n


Filled : Grid → Set  
Filled g = filled g ≡ 9

filled'-list : ∀ l → sum (map filled' l) ≤ length l 
filled'-list [] = z≤n
filled'-list (x' ∷ xs) = +-mono-≤ (filled'≤1 x') (filled'-list xs)
    
filled-lemma : ∀ g → Filled g ⊎ filled g ≤ 8 
filled-lemma (grid (just _) (just _) (just _) (just _) (just _) (just _) (just _) (just _) (just _)) = inj₁ refl
filled-lemma (grid nothing b c d e f g h i) = inj₂ (filled'-list (b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ [])) 
filled-lemma (grid a nothing c d e f g h i) = inj₂ (filled'-list (a ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ [])) 
filled-lemma (grid a b nothing d e f g h i) = inj₂ (filled'-list (a ∷ b ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []))
filled-lemma (grid a b c nothing e f g h i) = inj₂ (filled'-list (a ∷ b ∷ c ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []))
filled-lemma (grid a b c d nothing f g h i) = inj₂ (filled'-list (a ∷ b ∷ c ∷ d ∷ f ∷ g ∷ h ∷ i ∷ []))
filled-lemma (grid a b c d e nothing g h i) = inj₂ (filled'-list (a ∷ b ∷ c ∷ d ∷ e ∷ g ∷ h ∷ i ∷ []))
filled-lemma (grid a b c d e f nothing h i) = inj₂ (filled'-list (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ h ∷ i ∷ []))
filled-lemma (grid a b c d e f g nothing i) = inj₂ (filled'-list (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ i ∷ []))
filled-lemma (grid a b c d e f g h nothing) = inj₂ (filled'-list (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []))

Unfilled : Grid → Set  
Unfilled g = ¬ (Filled g)

filledDec : ∀ {g} → Dec (Filled g)
filledDec {g} with filled-lemma g 
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

test-grid : Grid
test-grid = grid (just x) (just o) (just x) (just o) (just x) (just o) (just x) (just x) (just o)

test-grid-filled : Filled test-grid 
test-grid-filled = refl  

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

move-lemma : ∀ {p g g'} → Move p g g' → filled g' ≡ suc (filled g)
move-lemma move-top-left = refl
move-lemma (move-top-middle {a} {c} {d} {e} {f} {g} {h} {i}) 
    rewrite +-suc (filled' a) (sum (map filled' (c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []))) = refl
move-lemma (move-top-right {a} {b} {d} {e} {f} {g} {h} {i})
    rewrite +-suc (filled' b) (sum (map filled' (d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' a) (sum (map filled' (b ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []))) = refl
move-lemma (move-middle-left {a} {b} {c} {e} {f} {g} {h} {i}) 
    rewrite +-suc (filled' c) (sum (map filled' (e ∷ f ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' b) (sum (map filled' (c ∷ e ∷ f ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' a) (sum (map filled' (b ∷ c ∷ e ∷ f ∷ g ∷ h ∷ i ∷ [])))
    = refl
move-lemma (move-middle-middle {a} {b} {c} {d} {f} {g} {h} {i})
    rewrite +-suc (filled' d) (sum (map filled' (f ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' c) (sum (map filled' (d ∷ f ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' b) (sum (map filled' (c ∷ d ∷ f ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' a) (sum (map filled' (b ∷ c ∷ d ∷ f ∷ g ∷ h ∷ i ∷ [])))
    = refl
move-lemma (move-middle-right {a} {b} {c} {d} {e} {g} {h} {i}) 
    rewrite +-suc (filled' e) (sum (map filled' (g ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' d) (sum (map filled' (e ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' c) (sum (map filled' (d ∷ e ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' b) (sum (map filled' (c ∷ d ∷ e ∷ g ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' a) (sum (map filled' (b ∷ c ∷ d ∷ e ∷ g ∷ h ∷ i ∷ [])))
    = refl
move-lemma (move-bottom-left {a} {b} {c} {d} {e} {f} {h} {i})
    rewrite +-suc (filled' f) (sum (map filled' (h ∷ i ∷ [])))
    rewrite +-suc (filled' e) (sum (map filled' (f ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' d) (sum (map filled' (e ∷ f ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' c) (sum (map filled' (d ∷ e ∷ f ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' b) (sum (map filled' (c ∷ d ∷ e ∷ f ∷ h ∷ i ∷ [])))
    rewrite +-suc (filled' a) (sum (map filled' (b ∷ c ∷ d ∷ e ∷ f ∷ h ∷ i ∷ [])))
    = refl
move-lemma (move-bottom-middle {a} {b} {c} {d} {e} {f} {g} {i}) 
    rewrite +-suc (filled' g) (sum (map filled' (i ∷ [])))
    rewrite +-suc (filled' f) (sum (map filled' (g ∷ i ∷ [])))
    rewrite +-suc (filled' e) (sum (map filled' (f ∷ g ∷ i ∷ [])))
    rewrite +-suc (filled' d) (sum (map filled' (e ∷ f ∷ g ∷ i ∷ [])))
    rewrite +-suc (filled' c) (sum (map filled' (d ∷ e ∷ f ∷ g ∷ i ∷ [])))
    rewrite +-suc (filled' b) (sum (map filled' (c ∷ d ∷ e ∷ f ∷ g ∷ i ∷ [])))
    rewrite +-suc (filled' a) (sum (map filled' (b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ i ∷ [])))
    = refl
move-lemma (move-bottom-right {a} {b} {c} {d} {e} {f} {g} {h}) 
    rewrite +-suc (filled' h) (sum (map filled' []))
    rewrite +-suc (filled' g) (sum (map filled' (h ∷ [])))
    rewrite +-suc (filled' f) (sum (map filled' (g ∷ h ∷ [])))
    rewrite +-suc (filled' e) (sum (map filled' (f ∷ g ∷ h ∷ [])))
    rewrite +-suc (filled' d) (sum (map filled' (e ∷ f ∷ g ∷ h ∷ [])))
    rewrite +-suc (filled' c) (sum (map filled' (d ∷ e ∷ f ∷ g ∷ h ∷ [])))
    rewrite +-suc (filled' b) (sum (map filled' (c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])))
    rewrite +-suc (filled' a) (sum (map filled' (b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])))
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
    go : ∀ n → Player → (g : Grid) → Unfilled g → filled g ≡ ∣ 9 - n ∣ → 9 ≥ n → Maybe Player  
    go zero _ g u p _ = ⊥-elim (u p)  
    go (suc n) x g u p (s≤s 8≥n) 
        with (filledDec {proj₁ (fˣ g u)}) 
    ... | yes filled = won (proj₁ (fˣ g u)) 
    ... | no unfilled = 
        let p' = trans (trans (move-lemma (proj₂ (fˣ g u))) (cong suc p)) (suc-∣a-b∣ (s≤s 8≥n)) in
        go n o (proj₁ (fˣ g u)) unfilled p' (≤-step 8≥n)
    go (suc n) o g u p (s≤s 8≥n) 
        with (filledDec {proj₁ (fᵒ g u)}) 
    ... | yes filled = won (proj₁ (fᵒ g u)) 
    ... | no unfilled = 
        let p' = trans (trans (move-lemma (proj₂ (fᵒ g u))) (cong suc p)) (suc-∣a-b∣ (s≤s 8≥n)) in
        go n x (proj₁ (fᵒ g u)) unfilled p' ((≤-step 8≥n))
    
module negation where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _≡⟨⟩_; _∎)

open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import isomorphism using (_≃_)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive (s≤s n<n) = <-irreflexive n<n

data Trichotomy (m n : ℕ) : Set where
  eq : ¬ (m < n) × (m ≡ n) × ¬ (n < m) → Trichotomy m n
  lt : (m < n) × ¬ (m ≡ n) × ¬ (n < m) → Trichotomy m n
  gt : ¬ (m < n) × ¬ (m ≡ n) × (n < m) → Trichotomy m n

postulate
  s≡s : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = eq ( (λ()) , refl , (λ()))
<-trichotomy zero (suc n) = lt ( s≤s z≤n  , (λ()) , λ() )
<-trichotomy (suc m) zero = gt ( (λ()) , (λ()) , s≤s z≤n)
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...  | eq (¬m<n , m≡n , ¬n<m) = eq ((λ {( s≤s m<n ) → ¬m<n (m<n)}) ,
                                   cong suc m≡n ,
                                   (λ {( s≤s n<m ) → ¬n<m (n<m)}))
...  | lt (m<n , ¬m≡n , ¬n<m) = lt (s≤s m<n ,
                                   (λ {m≡n → ¬m≡n (s≡s m≡n)}) ,
                                   ((λ {( s≤s n<m ) → ¬n<m (n<m)})))
...  | gt (¬m<n , ¬m≡n , n<m) = gt ((λ {( s≤s m<n ) → ¬m<n (m<n)}) ,
                                   (λ {m≡n → ¬m≡n (s≡s m≡n)}) ,
                                   s≤s n<m)


-- module op₁ where
--   -- IMP should the parameters be the same for the laws in the implications?
--   postulate
--     em : ∀ {A : Set} → A ⊎ ¬ A
--     ¬¬-elim : ∀ {A B : Set} → ¬ ¬ A → A
--     peirce : ∀ {A B : Set} → ((A → B) → A) → A
--     →as⊎ : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
--     morgan : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B

--   em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
--   em-irrefutable k =  k (inj₂ λ x → k (inj₁ x))

--   em-implies-¬¬-elim : ∀ {A : Set} → em → ¬¬-elim A
--   em-implies-¬¬-elim = ?

--   ¬¬-elim-implies-peirce : ∀ {A B : Set} → ¬¬-elim A → peirce A B
--   ¬¬-elim-implies-peirce = ?

--   peirce-implies-→as⊎ : ∀ {A B : Set} → peirce A B → →as⊎ A B
--   peirce-implies-→as⊎ = ?

--   →as⊎-implies-morgan : ∀ {A B : Set} → →as⊎ A B → morgan A B
--   →as⊎-implies-morgan = ?

--   morgan-implies-em : ∀ {A B : Set} → morgan A B → em A
--   morgan-implies-em = ?

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {P Q : Set} → (P → Q) → (¬ Q → ¬ P)
contraposition f ¬Q P = ¬Q (f P)

postulate
  ×-dual-→ : ∀ {A B : Set} → (A × ¬ B) → (A → B)
  ⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) → ¬ A × ¬ B
  conv-⊎-?ˡ : ∀ {A B : Set} → ¬ A ⊎ B → A ⊎ ¬ B
  conv-⊎-?ʳ : ∀ {A B : Set} → A ⊎ ¬ B → ¬ A ⊎ B
  -- pierce' : ∀ {A B : Set} → (¬ A → ¬ (A → B)) → A

module op₂ where
  em-implies-¬¬-elim :
    (∀ {P : Set} → (P ⊎ ¬ P))
    -------------------------
    → ∀ {P' : Set} → (¬ ¬ P' → P')
  em-implies-¬¬-elim em {P'} with em {P'}
  ... | inj₁ P =  λ ¬¬P → P
  ... | inj₂ ¬P = λ ¬¬P → ⊥-elim (¬¬P ¬P)

  ¬¬-elim-implies-pierce :
    (∀ {A : Set} → (¬ ¬ A → A))
    -------------------------------------
    → ∀ {P Q : Set} → ((P → Q) → P) → P
  ¬¬-elim-implies-pierce ¬¬-elim f = ¬¬-elim λ ¬P → ¬P (f λ P → ¬¬-elim (λ ¬Q → ¬P P))

  pierce-implies-→⊎ :
    (∀ {A B : Set} → ((A → B) → A) → A)
    -----------------------------------
    → ∀ {P Q : Set} → (P → Q) → ¬ P ⊎ Q
  pierce-implies-→⊎ pierce f = pierce λ x → (inj₁ λ P → x (inj₂ (f P)))
  -- pierce-implies-→⊎ pierce' f = inj₂ (f (pierce'
  --                               λ ¬P → ×-dual-→ (⊎-dual-× λ {(inj₁ P) → ¬P P
  --                                                           ; (inj₂ ⊥) → ⊥})))-- $yep

  →⊎-de-morgan :
    (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
    -----------------------------------
    → ∀ {A′ B : Set} → ¬ (¬ A′ × ¬ B) → A′ ⊎ B
  →⊎-de-morgan = {!!}

  →⊎-implies-em :
    (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
    -----------------------------------
    → ∀ {A′ : Set} → (A′ ⊎ ¬ A′)
  →⊎-implies-em = {!!}

  ¬¬-elim-implies-de-morgan :
    (∀ {A : Set} → (¬ ¬ A → A))
  ----------------------------------------
    → ∀ {A′ B : Set} → ¬ (¬ A′ × ¬ B) → A′ ⊎ B
  ¬¬-elim-implies-de-morgan = {!!}

  de-morgan-implies-em :
    (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
    ---------------------------------------
    → ∀ {A′ : Set} → (A′ ⊎ ¬ A′)
  de-morgan-implies-em = {!!}


Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable = {!!}

×-stable : ∀ {A B : Set} → Stable (A × B)
×-stable = {!!}

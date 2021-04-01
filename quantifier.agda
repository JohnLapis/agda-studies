module quantifier where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _≡⟨⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; +-identityˡ;
                                      ≤-refl; ≤-trans; +-mono-≤)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import isomorphism using (_≃_; extensionality)


∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record {
            to = λ f → ( λ A → proj₁ (f A)) , λ A → proj₂ (f A);
            from = λ f A → proj₁ f A , proj₂ f A;
            from∘to = λ f → refl;
            to∘from = λ f → refl
  }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f) a = inj₁ (f a)
⊎∀-implies-∀⊎ (inj₂ f) a = inj₂ (f a)

-- The converse isn't true since B or C being true for all x still holds even if
-- x only satisfies one of them, which means the x doesn't always satisfy at
-- least on of the predicates.

postulate
  extensionality' : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → (∀ x → f x ≡ g x)
      -----------------------
    → f ≡ g

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

∀-× : {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× = record {
      to = λ f → f aa , f bb , f cc ;
      from = λ{ f aa → proj₁ f ; f bb → proj₁ (proj₂ f); f cc → proj₂ (proj₂ f) };
      from∘to = λ f → extensionality' λ{ aa → refl ; bb → refl ; cc → refl };
      to∘from = λ f → refl
    }


∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f (x , y) = f x y

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = record {
              to = λ{ (a , inj₁ x) → inj₁ (a , x) ;
                      (a , inj₂ y) → inj₂ (a , y)};
              from = λ{ (inj₁ x) → proj₁ x , inj₁ (proj₂ x);
                        (inj₂ y) → proj₁ y , inj₂ (proj₂ y)};
              from∘to = λ{ (a , inj₁ x) → refl ;
                           (a , inj₂ y) → refl };
              to∘from = λ{ (inj₁ x) → refl ;
                           (inj₂ y) → refl}
            }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ (f , g) = (f , proj₁ g) , (f , proj₂ g)

-- The converse doesn't hold. If there exists x that satisfies B and a y that
-- satisfies C, that doesn't imply x always equal y, i.e. it doesn't imply there
-- exists an x that satisfies both B and C

∃-⊎ : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ = record {
      to = λ{ (aa , g) → inj₁ g ;
              (bb , g) → inj₂ (inj₁ g) ;
              (cc , g) → inj₂ (inj₂ g)};
      from = λ{ (inj₁ x) → aa , x ;
                (inj₂ (inj₁ x)) → bb , x;
                (inj₂ (inj₂ y)) → cc , y };
      from∘to = λ{ (aa , g) → refl ; (bb , g) → refl ; (cc , g) → refl };
      to∘from = λ{ (inj₁ x) → refl ;
                   (inj₂ (inj₁ x)) → refl;
                   (inj₂ (inj₂ y)) → refl}
    }

data even : ℕ → Set
data odd : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

∃-even : ∀ {n : ℕ} → ∃[ m ] (2 * m ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) → odd n

∃-even (zero , refl) = even-zero
∃-even (suc m , refl) = even-suc (∃-odd (m , helper m))
  where
    helper : ∀ (m : ℕ) → m + (m + zero) + 1 ≡ m + suc (m + zero)
    helper m = begin
               m + (m + zero) + 1   ≡⟨ +-assoc m (m + zero) 1 ⟩
               m + ((m + zero) + 1) ≡⟨ cong (m +_) (+-comm (m + zero) 1) ⟩
               m + suc (m + zero)
               ∎

∃-odd (zero , refl) = odd-suc even-zero
∃-odd (suc m , refl) = odd-suc (∃-even (suc m , helper m))
  where
    helper : ∀ (m : ℕ) → suc (m + suc (m + zero)) ≡ m + suc (m + zero) + 1
    helper m = begin
               suc (m + suc (m + zero)) ≡⟨⟩
               1 + (m + suc (m + zero)) ≡⟨ +-comm 1 (m + suc (m + zero)) ⟩
               m + suc (m + zero) + 1
               ∎


∃-|-≤ : ∀ {y z : ℕ} → ∃[ x ] (x + y ≡ z) → y ≤ z
∃-|-≤ (zero , refl) = ≤-refl
∃-|-≤ {zero} (suc x , refl) = z≤n
∃-|-≤ {suc y} (suc x , refl) = s≤s (∃-|-≤ (suc x , sym (+-suc x y)))

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ (f , g) = λ x → g (x f)

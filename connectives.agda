module connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import isomorphism using (_≃_)

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥)

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record {
    to = λ{ (inj₂ x) → x };
    from = λ{ x → (inj₂ x) };
    from∘to = λ{ (inj₂ x) → refl };
    to∘from = λ{ x → refl }
  }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ =
  record {
    to = λ{ (inj₁ x) → x };
    from = λ{ x → (inj₁ x) };
    from∘to = λ{ (inj₁ x) → refl };
    to∘from = λ{ x → refl }
  }



⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ (inj₁ a) , _ ⟩ = inj₁ a
⊎-weak-× ⟨ (inj₂ a) , c ⟩ = inj₂ ⟨ a , c ⟩

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ proj₃ , proj₄ ⟩) = ⟨ inj₁ proj₃ , inj₁ proj₄ ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

-- ×⊎-implies-⊎× : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
-- ×⊎-implies-⊎× ()

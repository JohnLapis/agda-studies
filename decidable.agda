module decidable where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (¬?; contradiction)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Product using (_×-dec_)


infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no (λ ())
zero <? (suc n) = yes z<s
suc m <? zero = no (λ ())
suc m <? suc n with m <? n
...            | yes m<n = yes (s<s m<n)
...            | no ¬m<n = no λ{(s<s m<n) → ¬m<n m<n}

postulate
  s≡s : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? (suc n) = no (λ ())
suc m ≡ℕ? zero = no (λ ())
suc m ≡ℕ? suc n with m ≡ℕ? n
...             | yes m≡n = yes (cong suc m≡n)
...             | no ¬m≡n = no λ{ x → ¬m≡n (s≡s x)}

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes a) (yes b) = refl
∧-× (yes a) (no ¬b) = refl
∧-× (no ¬a) (yes b) = refl
∧-× (no ¬a) (no ¬b) = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes a) (yes b) = refl
∨-⊎ (yes a) (no ¬b) = refl
∨-⊎ (no ¬a) (yes b) = refl
∨-⊎ (no ¬a) (no ¬b) = refl

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes a) = refl
not-¬ (no ¬a) = refl


record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

_iff_ : Bool → Bool → Bool
false iff false = true
true iff true = true
false iff true = false
true iff false = false

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes a ⇔-dec yes b = yes (record { to = λ _ → b ; from = λ _ → a })
no ¬a ⇔-dec no ¬b = yes (record { to = λ a → ⊥-elim (¬a a) ;
                                  from = λ b → ⊥-elim (¬b b)})
yes a ⇔-dec no ¬b = no λ a⇔b → ¬b (_⇔_.to a⇔b a)
no ¬a ⇔-dec yes b = no λ a⇔b → ¬a (_⇔_.from a⇔b b)

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes a) (yes b) = refl
iff-⇔ (yes a) (no ¬b) = refl
iff-⇔ (no ¬a) (yes b) = refl
iff-⇔ (no ¬a) (no ¬b) = refl

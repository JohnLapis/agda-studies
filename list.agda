module list where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (*-comm; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Unary using (Decidable)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import isomorphism using (_≃_; _⇔_; extensionality)
open import Data.List using (List; _++_; length; map; foldr)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.All using (All; []; _∷_)
open import Data.List.Any using (Any; here; there)
open import Data.Empty using (⊥; ⊥-elim)


pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) rewrite ++-identityʳ xs = refl

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib xs [] =
  begin
    reverse (xs ++ [])          ≡⟨ cong reverse (++-identityʳ xs) ⟩
    reverse xs                  ≡⟨⟩
    [] ++ reverse xs            ≡⟨⟩
    reverse [] ++ reverse xs
  ∎
reverse-++-distrib [] ys =
  begin
    reverse ([] ++ ys)          ≡⟨⟩
    reverse ys                  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    reverse ys ++ []            ≡⟨⟩
    reverse ys ++ reverse []
  ∎
reverse-++-distrib (x ∷ xs) (y ∷ ys) =
  begin
    reverse ((x ∷ xs) ++ (y ∷ ys))         ≡⟨⟩
    reverse (x ∷ (xs ++ (y ∷ ys)))         ≡⟨⟩
    reverse (xs ++ (y ∷ ys)) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs (y ∷ ys)) ⟩
    (reverse (y ∷ ys) ++ reverse (xs)) ++ [ x ]
  ≡⟨ ++-assoc (reverse (y ∷ ys)) (reverse xs) ([ x ])  ⟩
    reverse (y ∷ ys) ++ reverse (x ∷ xs)
  ∎


reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs)) ≡⟨⟩
    reverse ((reverse xs) ++ [ x ]) ≡⟨ reverse-++-distrib (reverse xs) ([ x ]) ⟩
    [ x ] ++ reverse (reverse xs)   ≡⟨ cong ([ x ] ++_) (reverse-involutive xs) ⟩
    x ∷ xs
  ∎

map-distrib-∘ : ∀ {A B C : Set} {f : A → B} {g : B → C}
  → map (g ∘ f) ≡ map g ∘ map f
map-distrib-∘ {A} {B} {C} {f} {g} = extensionality (lemma f g)
  where
    lemma : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A)
      → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    lemma f g [] = refl
    lemma f g (x ∷ xs) = cong ((g ∘ f) x ∷_) (lemma f g xs)

map-distrib-++ : ∀ {A B : Set} (f : A → B) (xs ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-distrib-++ _ [] ys = refl
map-distrib-++ f (x ∷ xs) ys =
  begin
    map f (x ∷ xs ++ ys)        ≡⟨ cong (f x ∷_) (map-distrib-++ f xs ys) ⟩
    map f (x ∷ xs) ++ map f ys
  ∎


data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f _ (leaf x) = leaf (f x)
map-Tree f g (node T₁ x T₂) = node  (map-Tree f g T₁) (g x) (map-Tree f g T₂)


foldr-product : List ℕ → ℕ
foldr-product = foldr _*_ 1

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A)
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys rewrite foldr-++ _⊗_ e xs ys = refl

foldr-∷ : ∀ {A : Set} (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) rewrite foldr-∷ xs = refl

++-is-foldr-∷ : ∀ {A : Set} (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
++-is-foldr-∷ [] ys = refl
++-is-foldr-∷ (x ∷ xs) ys rewrite ++-is-foldr-∷ xs ys = refl

foldr-map : ∀ {A B : Set} (f : A → B) → map f ≡ foldr (λ x xs → f x ∷ xs) []
foldr-map f = extensionality (lemma f)
  where
    lemma : ∀ {A B : Set} (f : A → B) (x : List A)
      → map f x ≡ foldr (λ x₁ → _∷_ (f x₁)) [] x
    lemma _ [] = refl
    lemma f (x ∷ xs) rewrite lemma f xs = refl

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node T₁ x T₂) = g (fold-Tree f g T₁) x (fold-Tree f g T₂)

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A)
  → Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys = record { to = to xs ys ; from = from xs ys } where
  to : ∀ {A : Set} {P : A → Set} (xs ys : List A)
    → Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
  to [] ys Pys = inj₂ Pys
  to (x ∷ xs) ys (here Px) = inj₁ (here Px)
  to (x ∷ xs) ys (there Pxs++ys) with to xs ys Pxs++ys
  ...     | inj₁ Pxs = inj₁ (there Pxs)
  ...     | inj₂ Pys = inj₂ Pys

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A)
    → (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
  from _        _  (inj₁ (here Px))   = here Px
  from (x ∷ xs) ys (inj₁ (there Pxs)) = there (from xs ys (inj₁ Pxs))
  from []       _  (inj₂ Pys)         = Pys
  from (x ∷ xs) ys (inj₂ Pys)         = there (from xs ys (inj₂ Pys))

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A)
  → All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys = record {
         to      = to xs ys;
         from    = from xs ys;
         from∘to = from∘to xs ys;
         to∘from = to∘from xs ys
  }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      All P (xs ++ ys) → (All P xs × All P ys)
    to [] _ Pys = [] , Pys
    to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
    ...                           | Pxs , Pys = Px ∷ Pxs , Pys

    from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
      All P xs × All P ys → All P (xs ++ ys)
    from [] ys (Pxs , Pys) = Pys
    from (x ∷ xs) ys (Px ∷ Pxs , Pys) = Px ∷ from xs ys (Pxs , Pys)

    from∘to : ∀ {A : Set} {P : A → Set} (xs ys : List A) (z : All P (xs ++ ys))
      → from xs ys (to xs ys z) ≡ z
    from∘to [] ys Pxs++ys = refl
    from∘to (x ∷ xs) ys (Px ∷ Pxs++ys) rewrite from∘to xs ys Pxs++ys = refl

    to∘from : ∀ {A : Set} {P : A → Set} (xs ys : List A) (z : All P xs × All P ys)
      → to xs ys (from xs ys z) ≡ z
    to∘from [] ys ([] , Pys) = refl
    to∘from (x ∷ xs) ys ((Px ∷ Pxs) , Pys) rewrite to∘from xs ys (Pxs , Pys) = refl

¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs = record {to = to xs; from = from xs} where
  to : ∀ { A : Set} {P : A → Set} (xs : List A)
    → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
  to [] ¬Pxs = []
  to (x ∷ xs) ¬Pxs = (λ Px →  ¬Pxs (here Px)) ∷ to xs λ Pxs → ¬Pxs (there Pxs)

  from : ∀ { A : Set} {P : A → Set} (xs : List A)
    → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
  from [] _ ()
  from (x ∷ xs) (¬Px ∷ ¬Pxs) (here Px) =  ¬Px Px
  from (x ∷ xs) (¬Px ∷ ¬Pxs) (there Px) = from xs ¬Pxs Px

¬Any≃All¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → (¬_ ∘ Any P) xs ≃ All (¬_ ∘ P) xs
¬Any≃All¬ xs = record {
          to = to xs;
          from = from xs;
          from∘to = from∘to xs ;
          to∘from = to∘from xs
  }
  where
    to : ∀ {A : Set} {P : A → Set} (xs : List A)
      → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
    to xs = _⇔_.to (¬Any⇔All¬ xs)

    from : ∀ {A : Set} {P : A → Set} (xs : List A)
      → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
    from xs = _⇔_.from (¬Any⇔All¬ xs)

    from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) (z : (¬_ ∘ Any P) xs)
      → from xs (to xs z) ≡ z
    from∘to [] _ = extensionality (λ ())
    from∘to (x ∷ xs) ¬Pxs = extensionality
                            λ{(here Px) → refl ;
                              (there Pxs) → ⊥-elim (¬Pxs (there Pxs))}


    to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) (z : All (¬_ ∘ P) xs)
      → to xs (from xs z) ≡ z
    to∘from [] [] = refl
    to∘from (x ∷ xs) (¬Px ∷ ¬Pxs) = cong (¬Px ∷_) (to∘from xs ¬Pxs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → (∀ x → f x ≡ g x)
      -----------------------
    → f ≡ g

All-∀ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → All P xs ≃ (∀ x' → x' ∈ xs → P x')
All-∀  xs = record {
       to = to xs;
       from = from  xs ;
       from∘to = from∘to xs ;
       to∘from = to∘from xs
  } where

  to : ∀ {A : Set} {P : A → Set} (xs : List A)
    → All P xs → (∀ x' → x' ∈ xs → P x')
  to xs (Px ∷ Pxs) x' (here x'≡x) rewrite x'≡x = Px
  to (x ∷ xs) (Px ∷ Pxs) x' (there x'∈xs) = to xs Pxs x' x'∈xs

  from : ∀ {A : Set} {P : A → Set} (xs : List A)
    → (∀ x' → x' ∈ xs → P x') → All P xs
  from [] ∀x'Px' = []
  from (x ∷ xs) ∀x'Px' = ∀x'Px' x (here refl)
                         ∷ from xs λ v v∈xs → ∀x'Px' v (there v∈xs)

  from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) (z : All P xs)
    → from xs (to xs z) ≡ z
  from∘to [] [] = refl
  from∘to (x ∷ xs) (Px ∷ Pxs) = cong (Px ∷_) (from∘to xs Pxs)

  to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) (z : ∀ x' → x' ∈ xs → P x')
    → to xs (from xs z) ≡ z
  to∘from xs ∀x'Px' = ∀-extensionality λ x' → extensionality (lemma xs ∀x'Px')
    where
      lemma : ∀ {A : Set} {P : A → Set} {x'} (xs : List A) (z : ∀ x' → x' ∈ xs → P x')
        → (x : x' ∈ xs) → to xs (from xs z) x' x ≡ z x' x
      lemma [] ∀x'Px' ()
      lemma xs ∀x'Px' (here x'≡x) rewrite x'≡x = refl
      lemma (x ∷ xs) ∀x'Px' (there x'∈xs) = lemma xs
                                                  (λ v v∈xs → ∀x'Px' v (there v∈xs))
                                                  x'∈xs

Any-∃ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → Any P xs ≃ (∃[ x ] (x ∈ xs × P x))
Any-∃ xs      = record {
      to      = to xs;
      from    = from xs;
      from∘to = from∘to xs;
      to∘from = to∘from xs
  } where

  to : ∀ {A : Set} {P : A → Set} (xs : List A)
    → Any P xs → (∃[ x ] (x ∈ xs × P x))
  to [] ()
  to (x ∷ xs) (here Px) = x , here refl , Px
  to (x ∷ xs) (there Pxs) = let (x' , x'∈xs , Px') = to xs Pxs
                            in x' , there x'∈xs , Px'

  from : ∀ {A : Set} {P : A → Set} (xs : List A)
    → (∃[ x ] (x ∈ xs × P x)) → Any P xs
  from [] ()
  from _ (x' , here x'≡x , Px') rewrite x'≡x = here Px'
  from (x ∷ xs) (x' , there x'∈xs , Px') = there (from xs (x' , x'∈xs , Px'))

  from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) (z : Any P xs)
    → from xs (to xs z) ≡ z
  from∘to _ (here Px) = refl
  from∘to (x ∷ xs) (there Pxs) = cong there (from∘to xs Pxs)

  to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) (z : ∃[ x ] (x ∈ xs × P x))
    → to xs (from xs z) ≡ z
  to∘from _ (x' , here x'≡x , Px') rewrite x'≡x = refl
  to∘from (x ∷ xs) (x' , there x'∈xs , Px') =
    cong (λ{ (v , v∈xs , Pv) → v , there v∈xs , Pv})
             (to∘from xs (x' , x'∈xs , Px'))

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no λ()
Any? P? (x ∷ xs) with P? x | Any? P? xs
...               | yes Px | _       = yes (here Px)
...               | _      | yes Pxs = yes (there Pxs)
...               | no ¬Px | no ¬Pxs = no λ{ (here Px) → ¬Px Px ;
                                             (there Pxs) → ¬Pxs Pxs}

any : ∀ {A : Set} → (A → Bool) → List A → Bool
any P = foldr _∨_ false ∘ map P


data merge {A : Set} : (xs ys zs : List A) → Set where
  []      :                                   merge []       []      []
  left-∷  : ∀ {x xs ys zs} → merge xs ys zs → merge (x ∷ xs) ys      (x ∷ zs)
  right-∷ : ∀ {y xs ys zs} → merge xs ys zs → merge  xs     (y ∷ ys) (y ∷ zs)


_ : merge (1 ∷ 4 ∷ []) (2 ∷ 3 ∷ []) (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
_ = left-∷ (right-∷ (right-∷ (left-∷ [])))

split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
  -- → ∃[ xs ] ∃[ ys ] (merge xs ys zs × All P xs × All (¬_ ∘ P) ys)
          → ∃[ xs ] ∃[ ys ] (All P xs × All (¬_ ∘ P) ys × merge xs ys zs)
split P? [] = [] , [] , [] , [] , []
-- split P? (z ∷ zs) = {!!} , ({!!} , ({!!} , {!!} , {!!}))
split P? (z ∷ zs) with
      P? z    | split P? zs
-- ... | yes Pz  | [] , [] , [] , [] , []        = [] , [] , [] , [] , {!()!}
-- ... | yes Pz  | (x ∷ xs) , ys , Pxs , Pys , left-∷ c  =
--                 (x ∷ xs) , ys , Pxs , Pys , left-∷ {!c!}
-- ... | yes Pz  | xs , ys , Pxs , Pys , right-∷ c = xs , ys , Pxs , Pys , {!!}
-- ... | yes Pz  | xs , ys , Pxs , Pys , c     = xs ,   ys ,   Pxs ,  Pys ,  {!!}
...| yes Pz | (x ∷ xs) , ys , (Px ∷ Pxs) , ¬Pys , left-∷ c =
              -- (x ∷ xs) , ys , (Px ∷ Pxs) , ¬Pys , {!left-∷ c!}
               xs , ys , Pxs , ¬Pys , {!left-∷ c!}
...| no ¬Pz | xs , (y ∷ ys) , Pxs , Pys , right-∷ c =
              xs , (y ∷ ys) , Pxs , Pys , {!right-∷ c!}

-- ... | yes Pz  | xs , ys , Pxs , Pys , c     = xs ,   ys ,   Pxs ,  Pys ,  {!!}

split' : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
  -- → ∃[ xs ] ∃[ ys ] (merge xs ys zs × All P xs × All (¬_ ∘ P) ys)
          → ∃[ xs ] ∃[ ys ] (All P xs × All (¬_ ∘ P) ys × merge xs ys zs)
split' P? [] = [] , [] , [] , [] , []
split' P? (z ∷ zs) with
   P? z   | split' P? zs
... | yes Pz | (.z ∷ xs) , ys , (.Pz ∷ Pxs) , Pys , left-∷ c =
               (.z ∷ xs) , ys , (.Pz ∷ Pxs) , Pys , {!left-∷ !}

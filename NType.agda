--
--  NType.agda - Truncated types
--

open import Prelude
open import Groupoid

module NType where

  infix 40 _≤_

  data ℕ₋₂ : Type where
    ⟨-2⟩ : ℕ₋₂
    S : ℕ₋₂ → ℕ₋₂

  data _≤_ : ℕ₋₂ → ℕ₋₂ → Type where
    -2≤n : ∀ {n : ℕ₋₂} → ⟨-2⟩ ≤ n
    s≤s : ∀ {m n : ℕ₋₂} → m ≤ n → S m ≤ S n
  
  is-contr : ∀ {ℓ} → Type ℓ → Type ℓ
  is-contr X = Σ[ x ∈ X ] ((y : X) → x ≡ y) 

  is-of-type : ∀ {ℓ} → ℕ₋₂ → Type ℓ → Type ℓ
  is-of-type ⟨-2⟩ X = is-contr X
  is-of-type (S n) X = (x y : X) → is-of-type n (x ≡ y)

  is-contr⇒is-of-type : ∀ {ℓ A} → is-contr {ℓ} A → (n : ℕ₋₂) → is-of-type n A
  is-contr⇒is-of-type contr ⟨-2⟩ = contr
  is-contr⇒is-of-type {A = A} contr (S n) = λ x y → is-contr⇒is-of-type (contr' x y) n
    where
    contr' : (x y : A) → is-contr (x ≡ y)
    fst (contr' x y) = snd contr x ⁻¹ ∙ snd contr y
    snd (contr' x y) = J (λ x y p → snd contr x ⁻¹ ∙ snd contr y ≡ p) (λ x → invˡ (snd contr x)) x y

  lift-is-of-type : ∀ {ℓ m n A} → is-of-type {ℓ} m A → m ≤ n → is-of-type n A
  lift-is-of-type prf -2≤n = is-contr⇒is-of-type prf _
  lift-is-of-type prf (s≤s m≤n) = λ x y → lift-is-of-type (prf x y) m≤n

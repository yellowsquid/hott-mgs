--
--  Groupoid.agda - Groupoid laws
--

open import Prelude

module Groupoid where

  module _ {ℓ} {X : Type ℓ} where

    J : ∀ {ℓ′}
      (P : (x y : X) (p : x ≡ y) → Type ℓ′) →
      (d : (x : X) → P x x refl) →
      (x y : X) (p : x ≡ y) →
      P x y p
    J P d x .x refl = d x

    infix 60 _⁻¹
    infixl 50 _∙_

    _∙_ : ∀ {x y z : X} → x ≡ y → y ≡ z → x ≡ z
    _∙_ {z = z} = J (λ x y p' → y ≡ z → x ≡ z) (λ _ q → q) _ _

    unitˡ : ∀ {x y : X} (p : x ≡ y) → refl ∙ p ≡ p
    unitˡ p = refl

    unitʳ : ∀ {x y : X} (p : x ≡ y) → p ∙ refl ≡ p
    unitʳ = J (λ _ _ p → p ∙ refl ≡ p) (λ _ → refl) _ _

    assoc : ∀ {x y z w : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
      → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
    assoc {z = z} {w} = J (λ _ y p → (q : y ≡ z) (r : z ≡ w) → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)) (λ _ _ _ → refl) _ _

    _⁻¹ : ∀ {x y : X} → x ≡ y → y ≡ x
    _⁻¹ = J (λ x y _ → y ≡ x) (λ _ → refl) _ _

    invˡ : ∀ {x y : X} (p : x ≡ y) → p ⁻¹ ∙ p ≡ refl
    invˡ = J (λ _ _ p → p ⁻¹ ∙ p ≡ refl) (λ _ → refl) _ _

    invʳ : ∀ {x y : X} (p : x ≡ y) → p ∙ p ⁻¹ ≡ refl
    invʳ = J (λ _ _ p → p ∙ p ⁻¹ ≡ refl) (λ _ → refl) _ _

  module _ {ℓ₀ ℓ₁} {X : Type ℓ₀} {Y : Type ℓ₁} where

    ap : (f : X → Y) {x y : X} (p : x ≡ y) → f x ≡ f y
    ap f = J (λ x y _ → f x ≡ f y) (λ _ → refl) _ _

    ap∙ : (f : X → Y) {x y z : X} (p : x ≡ y) (q : y ≡ z) → ap f (p ∙ q) ≡ ap f p ∙ ap f q
    ap∙ f {z = z} = J (λ _ y p → (q : y ≡ z) → ap f (p ∙ q) ≡ ap f p ∙ ap f q) (λ _ q → refl) _ _

    ap⁻¹ : (f : X → Y) {x y : X} (p : x ≡ y) → ap f (p ⁻¹) ≡ ap f p ⁻¹
    ap⁻¹ f = J (λ _ _ p → ap f (p ⁻¹) ≡ ap f p ⁻¹) (λ _ → refl) _ _

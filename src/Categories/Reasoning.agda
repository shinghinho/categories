{-# OPTIONS --without-K --safe #-}

open import Categories.Core

module Categories.Reasoning {𝓁ob 𝓁mor 𝓁eq} (ℂ : Category {𝓁ob} {𝓁mor} {𝓁eq}) where

open import Relation.Binary
open Category renaming (_≃_ to _≃′_; _∘_ to _∘′_)
open IsEquivalence

variable
  a b c d e : ob ℂ
  f : hom ℂ a b
  g : hom ℂ b c
  h : hom ℂ c d
  i : hom ℂ d e

infixl 10 _≃_
_≃_ : hom ℂ a b
    → hom ℂ a b
    → Set 𝓁eq
_≃_ f g = _≃′_ ℂ f g

infixl 20 _∘_
_∘_ : hom ℂ b c → hom ℂ a b → hom ℂ a c
g ∘ f = _∘′_ ℂ g f

R : f ≃ f
R = refl (≃-isequiv ℂ)

T : f ≃ g → g ≃ h → f ≃ h
T = trans (≃-isequiv ℂ)

S : f ≃ g → g ≃ f
S = sym (≃-isequiv ℂ)

infixr 0 _≃⟨_⟩_
_≃⟨_⟩_ : (f : hom ℂ a b) → f ≃ g → g ≃ h → f ≃ h
f ≃⟨ p ⟩ q = T p q

infixr 1 _qed
_qed : (f : hom ℂ a b) → f ≃ f
f qed = R

test : id ℂ ∘ id ℂ ∘ f ≃ f
test {f = f} =
    id ℂ ∘ id ℂ ∘ f
  ≃⟨ {!!} ⟩
    id ℂ ∘ f
  ≃⟨ {!!} ⟩
    f
  qed

{-# OPTIONS --without-K --safe #-}

open import Categories.Core

module Categories.Reasoning {𝓁ob 𝓁mor 𝓁eq} (ℂ : Category {𝓁ob} {𝓁mor} {𝓁eq}) where

open import Relation.Binary
open Category
open IsEquivalence

variable
  a b c d e : ob ℂ
  f : arr ℂ a b
  g : arr ℂ b c
  h : arr ℂ c d
  i : arr ℂ d e

hom : ob ℂ → ob ℂ → Set 𝓁mor
hom a b = arr ℂ a b

dom : hom a b → ob ℂ
dom {a = a} _ = a

cod : hom a b → ob ℂ
cod {b = b} _ = b

id : hom a a
id = ident ℂ

infixl 20 _∘_
_∘_ : hom b c → hom a b → hom a c
g ∘ f = comp ℂ g f

infixl 10 _≃_
_≃_ : hom a b → hom a b → Set 𝓁eq
f ≃ g = equiv ℂ f g

R : f ≃ f
R = refl (isequiv ℂ)

T : f ≃ g → g ≃ h → f ≃ h
T = trans (isequiv ℂ)

S : f ≃ g → g ≃ f
S = sym (isequiv ℂ)

A : (h ∘ g) ∘ f ≃ h ∘ (g ∘ f)
A = ca ℂ

IL : id ∘ f ≃ f
IL = 1li ℂ

IR : f ∘ id ≃ f
IR = 1ri ℂ

Left : g ≃ i → g ∘ f ≃ i ∘ f
Left = erc ℂ R

Right : f ≃ i → g ∘ f ≃ g ∘ i
Right p = erc ℂ p R

infixr 0 _≃⟨_⟩_
_≃⟨_⟩_ : (f : hom a b) → f ≃ g → g ≃ h → f ≃ h
f ≃⟨ p ⟩ q = T p q

infixr 1 _∎
_∎ : (f : hom a b) → f ≃ f
f ∎ = R

{-
Examples:

theorem₀ :
  ((i ∘ h) ∘ g) ∘ f ≃ i ∘ (h ∘ (g ∘ f))
theorem₀ {i = i} {h = h} {g = g} {f = f} =
    ((i ∘ h) ∘ g) ∘ f
  ≃⟨ A ⟩
    (i ∘ h) ∘ (g ∘ f)
  ≃⟨ A ⟩
    i ∘ (h ∘ (g ∘ f))
  ∎

theorem₁ :
  i ∘ h ∘ g ∘ f ≃ i ∘ (h ∘ g) ∘ f
theorem₁ {i = i} {h = h} {g = g} {f = f} =
    ((i ∘ h) ∘ g) ∘ f
  ≃⟨ Left A ⟩
    i ∘ (h ∘ g) ∘ f
  ∎
-}

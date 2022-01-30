{-# OPTIONS --without-K --safe #-}

module Categories.Core where

open import Level renaming (suc to lsuc)
open import Relation.Binary

-- Compute the universe level of a category
CatLevel : (𝓁ob 𝓁mor 𝓁eq : Level) → Level
CatLevel 𝓁ob 𝓁mor 𝓁eq = lsuc (𝓁ob ⊔ 𝓁mor ⊔ 𝓁eq)

-- Compute the type universe for the category
CatUni : (𝓁ob 𝓁mor 𝓁eq :  Level) → Set (lsuc (CatLevel 𝓁ob 𝓁mor 𝓁eq))
CatUni 𝓁ob 𝓁mor 𝓁eq = Set (CatLevel 𝓁ob 𝓁mor 𝓁eq)

record Category {𝓁ob 𝓁mor 𝓁eq : Level} : CatUni 𝓁ob 𝓁mor 𝓁eq where
  -- precedence
  infixl 20 _∘_
  infixl 10 _≃_
  -- data
  field
    ob  : Set 𝓁ob -- class of objects
    hom : ob → ob → Set 𝓁mor -- hom functor
    _≃_ : {a b : ob} → hom a b → hom a b → Set 𝓁eq -- equivalence
    id  : {a : ob} → hom a a -- identity arrow
    _∘_ : {a b c : ob} → hom b c → hom a b → hom a c -- composition
  -- higher witness is an equivalence
  field
    ≃-isequiv : {a b : ob} → IsEquivalence {A = hom a b} _≃_
  -- categorical axioms
  field
    -- id is left unital element
    1li : {a b : ob} {f : hom a b} 
        → id ∘ f ≃ f
    -- id is the right unital element
    1ri : {a b : ob} {f : hom a b} 
        → f ∘ id ≃ f
    -- composition is associative
    ca : {a b c d : ob} {f : hom a b} {g : hom b c} {h : hom c d} 
       → (h ∘ g) ∘ f ≃ h ∘ (g ∘ f)
open Category

private
  variable
    𝓁ob 𝓁mor 𝓁eq : Level
    ℂ : Category {𝓁ob} {𝓁mor} {𝓁eq}

dom : {a b : ob ℂ} → hom ℂ a b → ob ℂ
dom {a = a} _ = a

cod : {a b : ob ℂ} → hom ℂ a b → ob ℂ
cod {b = b} _ = b

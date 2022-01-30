{-# OPTIONS --without-K --safe #-}

module Categories.Core where

open import Level
open import Relation.Binary

record Category {𝓁ob 𝓁mor 𝓁eq : Level} : Set (suc (𝓁ob ⊔ 𝓁mor ⊔ 𝓁eq)) where
  -- data
  field
    ob    : Set 𝓁ob
    arr   : ob → ob → Set 𝓁mor
    equiv : {a b : ob} → arr a b → arr a b → Set 𝓁eq
    ident : {a : ob} → arr a a
    comp  : {a b c : ob} → arr b c → arr a b → arr a c
  -- higher witness is an equivalence
  field
    isequiv : {a b : ob} → IsEquivalence {A = arr a b} equiv
    erc : {a b c : ob} {f p : arr a b} {g q : arr b c}
        → equiv f p
        → equiv g q
        → equiv (comp g f) (comp q p)
  -- categorical axioms
  field
    -- id is left unital element
    1li : {a b : ob} {f : arr a b} → equiv (comp ident f) f
    -- id is the right unital element
    1ri : {a b : ob} {f : arr a b} → equiv (comp f ident) f
    -- composition is associative
    ca : {a b c d : ob} {f : arr a b} {g : arr b c} {h : arr c d} 
       → equiv (comp (comp h g) f) (comp h (comp g f))
open Category


{-# OPTIONS --without-K --safe #-}

module Categories.Set where

open import Level
open import Categories.Core
open import Relation.Binary.PropositionalEquality
open Category

FunctionSpace : Set → Set → Set
FunctionSpace A B = A → B

𝑆𝑒𝑡 : Category
ob        𝑆𝑒𝑡 = Set
hom       𝑆𝑒𝑡 = FunctionSpace
_≃_       𝑆𝑒𝑡 = _≡_
id        𝑆𝑒𝑡 = λ x → x
_∘_       𝑆𝑒𝑡 = λ g f x → g (f x)
≃-isequiv 𝑆𝑒𝑡 = record { refl = refl ; sym = sym ; trans = trans }
1li       𝑆𝑒𝑡 = refl
1ri       𝑆𝑒𝑡 = refl
ca        𝑆𝑒𝑡 = refl

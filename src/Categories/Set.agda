{-# OPTIONS --without-K --safe #-}

module Categories.Set where

open import Level
open import Categories.Core
open import Relation.Binary.PropositionalEquality
open Category

FunctionSpace : Set → Set → Set
FunctionSpace A B = A → B

𝑆𝑒𝑡 : Category
ob 𝑆𝑒𝑡 = Set
arr 𝑆𝑒𝑡 = FunctionSpace
equiv 𝑆𝑒𝑡 = _≡_
ident 𝑆𝑒𝑡 = λ x → x
comp 𝑆𝑒𝑡 = λ g f x → g (f x)
isequiv 𝑆𝑒𝑡 = record { refl = refl ; sym = sym ; trans = trans }
erc 𝑆𝑒𝑡 refl refl = refl
1li 𝑆𝑒𝑡 = refl
1ri 𝑆𝑒𝑡 = refl
ca 𝑆𝑒𝑡 = refl

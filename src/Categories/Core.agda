{-# OPTIONS --without-K --safe #-}

module Categories.Core where

open import Level
open import Relation.Binary

record Category {πob πmor πeq : Level} : Set (suc (πob β πmor β πeq)) where
  -- data
  field
    ob    : Set πob
    arr   : ob β ob β Set πmor
    equiv : {a b : ob} β arr a b β arr a b β Set πeq
    ident : {a : ob} β arr a a
    comp  : {a b c : ob} β arr b c β arr a b β arr a c
  -- higher witness is an equivalence
  field
    isequiv : {a b : ob} β IsEquivalence {A = arr a b} equiv
    erc : {a b c : ob} {f p : arr a b} {g q : arr b c}
        β equiv f p
        β equiv g q
        β equiv (comp g f) (comp q p)
  -- categorical axioms
  field
    -- id is left unital element
    1li : {a b : ob} {f : arr a b} β equiv (comp ident f) f
    -- id is the right unital element
    1ri : {a b : ob} {f : arr a b} β equiv (comp f ident) f
    -- composition is associative
    ca : {a b c d : ob} {f : arr a b} {g : arr b c} {h : arr c d} 
       β equiv (comp (comp h g) f) (comp h (comp g f))
open Category


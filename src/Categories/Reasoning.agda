{-# OPTIONS --without-K --safe #-}

open import Categories.Core

module Categories.Reasoning {πob πmor πeq} (β : Category {πob} {πmor} {πeq}) where

open import Relation.Binary
open Category
open IsEquivalence

variable
  a b c d e : ob β
  f : arr β a b
  g : arr β b c
  h : arr β c d
  i : arr β d e

hom : ob β β ob β β Set πmor
hom a b = arr β a b

dom : hom a b β ob β
dom {a = a} _ = a

cod : hom a b β ob β
cod {b = b} _ = b

id : hom a a
id = ident β

infixl 20 _β_
_β_ : hom b c β hom a b β hom a c
g β f = comp β g f

infixl 10 _β_
_β_ : hom a b β hom a b β Set πeq
f β g = equiv β f g

R : f β f
R = refl (isequiv β)

T : f β g β g β h β f β h
T = trans (isequiv β)

S : f β g β g β f
S = sym (isequiv β)

A : (h β g) β f β h β (g β f)
A = ca β

IL : id β f β f
IL = 1li β

IR : f β id β f
IR = 1ri β

Left : g β i β g β f β i β f
Left = erc β R

Right : f β i β g β f β g β i
Right p = erc β p R

infixr 0 _ββ¨_β©_
_ββ¨_β©_ : (f : hom a b) β f β g β g β h β f β h
f ββ¨ p β© q = T p q

infixr 1 _β
_β : (f : hom a b) β f β f
f β = R

{-
Examples:

theoremβ :
  ((i β h) β g) β f β i β (h β (g β f))
theoremβ {i = i} {h = h} {g = g} {f = f} =
    ((i β h) β g) β f
  ββ¨ A β©
    (i β h) β (g β f)
  ββ¨ A β©
    i β (h β (g β f))
  β

theoremβ :
  i β h β g β f β i β (h β g) β f
theoremβ {i = i} {h = h} {g = g} {f = f} =
    ((i β h) β g) β f
  ββ¨ Left A β©
    i β (h β g) β f
  β
-}

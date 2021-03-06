module Categories.Functor where

open import Level
open import Categories.Core
open import Categories.Reasoning
open Category

record Functor {πob πmor πeq πobβ² πmorβ² πeqβ² : Level}
               (π : Category {πob} {πmor} {πeq})
               (π : Category {πobβ²} {πmorβ²} {πeqβ²})
               : Set (suc (πob β πmor β πeq β πobβ² β πmorβ² β πeqβ²)) where
  field
    lift0 : ob π β ob π
    lift1 : {a b : ob π} β arr π a b β arr π (lift0 a) (lift0 b)
  field
    -- F(id) = id
    -- Hmm... maybe I should fix the syntax
    fid : {a : ob π} β equiv π (lift1 (ident π {a})) (ident π {lift0 a})
    -- F (g β f) = F g β F f
    fcomp : {a b c : ob π} {f : arr π a b} {g : arr π b c}
          β equiv π (lift1 (comp π g f)) (comp π (lift1 g) (lift1 f))

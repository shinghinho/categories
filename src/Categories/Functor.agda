module Categories.Functor where

open import Level
open import Categories.Core
open import Categories.Reasoning
open Category

record Functor {𝓁ob 𝓁mor 𝓁eq 𝓁ob′ 𝓁mor′ 𝓁eq′ : Level}
               (𝓒 : Category {𝓁ob} {𝓁mor} {𝓁eq})
               (𝓓 : Category {𝓁ob′} {𝓁mor′} {𝓁eq′})
               : Set (suc (𝓁ob ⊔ 𝓁mor ⊔ 𝓁eq ⊔ 𝓁ob′ ⊔ 𝓁mor′ ⊔ 𝓁eq′)) where
  field
    lift0 : ob 𝓒 → ob 𝓓
    lift1 : {a b : ob 𝓒} → arr 𝓒 a b → arr 𝓓 (lift0 a) (lift0 b)
  field
    -- F(id) = id
    -- Hmm... maybe I should fix the syntax
    fid : {a : ob 𝓒} → equiv 𝓓 (lift1 (ident 𝓒 {a})) (ident 𝓓 {lift0 a})
    -- F (g ∘ f) = F g ∘ F f
    fcomp : {a b c : ob 𝓒} {f : arr 𝓒 a b} {g : arr 𝓒 b c}
          → equiv 𝓓 (lift1 (comp 𝓒 g f)) (comp 𝓓 (lift1 g) (lift1 f))

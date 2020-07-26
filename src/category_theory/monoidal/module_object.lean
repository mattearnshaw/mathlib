import category_theory.monoidal.monoid_object

open category_theory

namespace Mod_obj

universes u v

variables (C : Type u) [category.{v} C] [monoidal_category.{v} C] (A : Mon_in C)

structure Mod_in :=
(N      : C)
(ρ      : A.X ⊗ N ⟶ N)
(unit   : (A.ι ⊗ 𝟙 N) ≫ ρ = (λ_ N).hom)
(action : (A.ι ⊗ 𝟙 N) ≫ ρ = (λ_ N).hom)

end Mod_obj

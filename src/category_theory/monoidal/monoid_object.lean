import algebra.category.Mon
import category_theory.monoidal.category

open category_theory

universes u v

variables (C : Type u) [category.{v} C] [monoidal_category.{v} C]

structure Mon_ :=
(X          : C)
(ι          : 𝟙_ C ⟶ X)
(μ          : X ⊗ X ⟶ X)
(assoc      : (α_ X X X).hom ≫ (𝟙 X ⊗ μ) ≫ μ = (μ ⊗ 𝟙 X) ≫ μ)
(unit_left  : (ι ⊗ 𝟙 X) ≫ μ = (λ_ X).hom)
(unit_right : (𝟙 X ⊗ ι) ≫ μ = (ρ_ X).hom)

namespace Mon_

variable {C}

@[ext]
structure hom (M N : Mon_ C) :=
(f : M.X ⟶ N.X)
(h₁ : M.ι ≫ f = N.ι)
(h₂ : M.μ ≫ f = (f ⊗ f) ≫ N.μ)

instance : category (Mon_ C) :=
{
  hom := λ M N, hom M N,
  id := λ _, {f := (𝟙 _), h₁ := by tidy, h₂ := by tidy},
  comp := λ _ _ _ f g, { f := f.f ≫ g.f,
  h₁ :=
  begin
    rw ← g.h₁,
    rw ← category.assoc,
    rw f.h₁,
  end,
  h₂ :=
  begin
    rw monoidal_category.tensor_comp,
    rw category.assoc,
    rw ← g.h₂,
    rw ← category.assoc,
    rw f.h₂,
    rw category.assoc,
  end },
}

end Mon_

variables (D : Type u) [category.{v} D] [braided_monoidal_category.{v} D]

structure CommMon_ extends Mon_ D :=
(comm : (σ X X).hom ≫ μ = μ)

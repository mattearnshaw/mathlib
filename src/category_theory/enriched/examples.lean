import category_theory.enriched.enriched_over
import algebra.category.Group.monoidal

universes u

namespace category_theory

example : enriched_over AddCommGroup.{u} AddCommGroup.{u} :=
{ e_hom := λ X Y, AddCommGroup.of (X ⟶ Y),
  e_id := λ X, λ _, 𝟙 _,
  e_comp := λ X Y Z p, p.val (limits.walking_pair.left) ≫ p.val (limits.walking_pair.right), -- that was ugly...
  e_hom_forget := λ X Y, equiv.refl _ }

-- TODO modules over a ring are enriched over themselves
-- TODO deduce from this that they are enriched over AddCommGroup

end category_theory
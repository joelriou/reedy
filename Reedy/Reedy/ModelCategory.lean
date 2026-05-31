/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.Reedy.WeakFactorizationSystem
public import Reedy.MorphismProperty.HasTwoOutOfThreeProperty
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# The Reedy model category structure

-/

@[expose] public section

namespace CategoryTheory

open HomotopicalAlgebra Limits

variable {C : Type u} [SmallCategory C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

namespace ReedyStructure

open MorphismProperty

def FunctorCategory (_ : ReedyStructure W₁ W₂ α) (D : Type*) [Category D] := C ⥤ D
deriving Category

variable (r : ReedyStructure W₁ W₂ α) {D : Type*} [Category D]
  (P₁ : MorphismProperty D) (P₂ : MorphismProperty D)
  [IsWeakFactorizationSystem P₁ P₂]
  [ModelCategory D]

namespace FunctorCategory

instance [HasFiniteLimits D] : HasFiniteLimits (r.FunctorCategory D) :=
  inferInstanceAs (HasFiniteLimits (C ⥤ D))

instance [HasFiniteColimits D] : HasFiniteColimits (r.FunctorCategory D) :=
  inferInstanceAs (HasFiniteColimits (C ⥤ D))

instance [HasColimitsOfSize.{u, u} D] : CategoryWithCofibrations (r.FunctorCategory D) where
  cofibrations := r.left (cofibrations D)

instance : CategoryWithFibrations (r.FunctorCategory D) where
  fibrations := r.right (fibrations D)

instance : CategoryWithWeakEquivalences (r.FunctorCategory D) where
  weakEquivalences := (weakEquivalences D).functorCategory C

lemma cofibrations_eq [HasColimitsOfSize.{u, u} D] :
    cofibrations (r.FunctorCategory D) = r.left (cofibrations D) := rfl

lemma fibrations_eq : fibrations (r.FunctorCategory D) = r.right (fibrations D) := rfl

lemma weakEquivalences_eq :
    weakEquivalences (r.FunctorCategory D) = (weakEquivalences D).functorCategory C := rfl

-- C.5.13 (i)
lemma trivialCofibrations_eq [HasColimitsOfSize.{u, u} D] :
    trivialCofibrations (r.FunctorCategory D) = r.left (trivialCofibrations D) := sorry

-- C.5.13 (ii)
lemma trivialFibrations_eq :
    trivialFibrations (r.FunctorCategory D) = r.right (trivialFibrations D) := sorry

instance : (weakEquivalences (r.FunctorCategory D)).HasTwoOutOfThreeProperty :=
  inferInstanceAs (HasTwoOutOfThreeProperty ((weakEquivalences D).functorCategory C))

variable [HasColimitsOfSize.{u, u} D]

instance :
    IsWeakFactorizationSystem (cofibrations (r.FunctorCategory D)) (trivialFibrations _) := by
  rw [cofibrations_eq, trivialFibrations_eq]
  exact r.isWeakFactorizationSystem _ _

instance :
    IsWeakFactorizationSystem (trivialCofibrations (r.FunctorCategory D)) (fibrations _) := by
  rw [fibrations_eq, trivialCofibrations_eq]
  exact r.isWeakFactorizationSystem _ _

-- C.5.14
instance : ModelCategory (r.FunctorCategory D) :=
  .mk' _

end FunctorCategory

end ReedyStructure

end CategoryTheory

/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.Arrow.MkFunctor
public import Reedy.Reedy.RelativeCellComplex
public import Reedy.WeightedLimits.Colimits

/-!
# Skeleton

-/

universe u

@[expose] public section

namespace CategoryTheory

open HomotopicalAlgebra Opposite Limits FunctorToTypes

variable {C : Type u} [SmallCategory C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

namespace ReedyStructure

variable (r : ReedyStructure W₁ W₂ α) {D : Type*} [Category D]
  [HasColimitsOfSize.{u, u} D]

noncomputable def skFunctor : α ⥤ (C ⥤ D) ⥤ C ⥤ D :=
  r.monotone_skYoneda.functor ⋙ Subfunctor₂.toFunctorFunctor yoneda ⋙ weightedColim₂

section Latching

-- C.4.14
noncomputable abbrev latching (X : C) : (C ⥤ D) ⥤ D :=
  weightedColim.obj (r.boundaryYonedaObj X).toFunctor

def latchingι (X : C) : r.latching X ⟶ (evaluation C D).obj X := by
  sorry

noncomputable def relativeLatchingSrc (X : C) : Arrow (C ⥤ D) ⥤ D :=
  pushout (Functor.whiskerLeft _ (r.latchingι X)) (Functor.whiskerRight Arrow.leftToRight _)

noncomputable def relativeLatchingMap (X : C) :
    r.relativeLatchingSrc X ⟶ Arrow.rightFunc ⋙ (evaluation C D).obj X :=
  pushout.desc _ _ (Functor.whiskerLeft_comp_whiskerRight _ _)

-- C.4.15
noncomputable def relativeLatchingFunctor (X : C) : Arrow (C ⥤ D) ⥤ Arrow D :=
  Arrow.mkFunctor (r.relativeLatchingMap X)

end Latching

section Matching

noncomputable def relativeMatchingFunctor (X : C) : Arrow (C ⥤ D) ⥤ Arrow D := by
  have := r
  sorry

end Matching

end ReedyStructure

end CategoryTheory

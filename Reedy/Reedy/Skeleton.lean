/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.Arrow.MkFunctor
public import Reedy.Arrow.Over
public import Reedy.Limits.RelativeCellComplex
public import Reedy.Reedy.RelativeCellComplex
public import Reedy.WeightedLimits.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Skeleton

-/

universe u

@[expose] public section

namespace CategoryTheory

open HomotopicalAlgebra Opposite Limits FunctorToTypes

namespace Limits

variable (C : Type u) [Category.{v} C] (D : Type*) [Category* D]
  [HasColimitsOfSize.{v, max u v} D]

noncomputable abbrev toArrowCompWeightedColim₂LeibnizPushout :
    Over (yoneda (C := C)) ⥤ Arrow (C ⥤ D) ⥤ Arrow (C ⥤ D) :=
  letI : HasColimitsOfSize.{0, 0} D := hasColimitsOfSizeShrink D
  Over.toArrow ⋙ weightedColim₂.leibnizPushout

instance (K : Type*) [Category* K] [HasColimitsOfShape K D] :
    PreservesColimitsOfShape K (toArrowCompWeightedColim₂LeibnizPushout C D) := sorry

instance {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
    [HasIterationOfShape α D] :
    PreservesWellOrderContinuousOfShape α (toArrowCompWeightedColim₂LeibnizPushout C D) where
  preservesColimitsOfShape m hm := by
    have := hasColimitsOfShape_of_isSuccLimit D m hm
    infer_instance

end Limits

variable {C : Type u} [SmallCategory C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

namespace ReedyStructure

variable (r : ReedyStructure W₁ W₂ α) {D : Type*} [Category D]
  [HasColimitsOfSize.{u, u} D] [HasColimitsOfShape α D]
  [HasIterationOfShape α D]

noncomputable def skFunctor : α ⥤ (C ⥤ D) ⥤ C ⥤ D :=
  r.monotone_skYoneda.functor ⋙ Subfunctor₂.toFunctorFunctor yoneda ⋙ weightedColim₂

variable (C D) in
noncomputable abbrev toArrowCompWeightedColim₂LeibnizPushout :
    Over (yoneda (C := C)) ⥤ Arrow (C ⥤ D) ⥤ Arrow (C ⥤ D) :=
  Over.toArrow ⋙ weightedColim₂.leibnizPushout

variable [NoMaxOrder α]

-- hopefully, up to isomorphisms, this should give the relative skeleton filtration
-- of a morphism (and functoriality in this map)
#check r.relativeCellComplexOver.map (toArrowCompWeightedColim₂LeibnizPushout C D)

end ReedyStructure

end CategoryTheory

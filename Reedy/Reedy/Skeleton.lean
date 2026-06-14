/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.Arrow.MkFunctor
public import Reedy.Arrow.Over
public import Reedy.RelativeCellComplex.Map
public import Reedy.Reedy.RelativeCellComplex
public import Reedy.RelativeCellComplex.OfArrowIso
public import Reedy.WeightedLimits.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib

/-!
# Skeleton

-/

universe u u'

@[expose] public section

namespace CategoryTheory

open HomotopicalAlgebra Opposite Limits FunctorToTypes

variable {C : Type u} [SmallCategory C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type u'} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

namespace ReedyStructure

variable (r : ReedyStructure W₁ W₂ α) {D : Type*} [Category D]
  [HasColimitsOfSize.{u', u'} (Type u)]
  [HasColimitsOfSize.{u, u} D]
  [HasProducts.{u} D]

instance :
    PreservesWellOrderContinuousOfShape α (weightedColim₂.{u} (J := C) (J' := C) (C := D)) where

noncomputable def skFunctor : α ⥤ (C ⥤ D) ⥤ C ⥤ D :=
  r.monotone_skYoneda.functor ⋙ Subfunctor₂.toFunctorFunctor yoneda ⋙ weightedColim₂

variable [NoMaxOrder α]

-- ??
local instance : HasInitial ((C ⥤ D) ⥤ (C ⥤ D)) := by infer_instance

noncomputable def relativeCellComplexSk :
    RelativeCellComplex.{u} (fun j i ↦ weightedColim₂.map (r.basicCell j i))
      (initial.to (𝟭 (C ⥤ D))) :=
  (r.relativeCellComplex.map (weightedColim₂.{u} (C := D))).ofArrowIso
    (Arrow.isoMk (initialIsInitial.uniqueUpToIso
      (IsInitial.isInitialObj weightedColim₂ _ (Subfunctor₂.isInitialBot _)))
    (weightedColim₂ObjYonedaIso C D).symm (initial.hom_ext _ _)).symm

noncomputable abbrev sk : α ⥤ (C ⥤ D) ⥤ (C ⥤ D) := r.relativeCellComplexSk.F

end ReedyStructure

end CategoryTheory

/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.Arrow.MkFunctor
public import Reedy.Arrow.Over
public import Reedy.RelativeCellComplex.Map
public import Reedy.RelativeCellComplex.Under
public import Reedy.Reedy.RelativeCellComplex
public import Reedy.Limits.Pushout
public import Reedy.RelativeCellComplex.OfArrowIso
public import Reedy.WeightedLimits.Colimits
public import Reedy.Limits.PreservesWellOrderContinuous
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib

/-!
# Skeleton

-/

universe u u' vD uD v'' u''

@[expose] public section

namespace CategoryTheory

open HomotopicalAlgebra Opposite Limits FunctorToTypes

namespace Over

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] (Ψ : C₁ ⥤ C₂)
  [HasPushouts C₂]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
def toArrowLeftOver : Over Ψ ⥤ ArrowLeftOver (Arrow.leftFunc ⋙ Ψ) where
  obj Φ :=
    ArrowLeftOver.mk
      (Functor.whiskerLeft (Functor.mapArrow Φ.left) Arrow.leftToRight)
      (Functor.whiskerLeft Arrow.leftFunc Φ.hom)
  map f :=
    ArrowLeftOver.homMk (Functor.whiskerRight ((Functor.mapArrowFunctor _ _).map f.left) _)
      (Functor.whiskerRight ((Functor.mapArrowFunctor _ _).map f.left) _) (by
      ext
      dsimp [ArrowLeftOver.mk, ArrowLeftOver.top]
      simp) (by
      ext
      rw [← Over.w f]
      dsimp)

noncomputable abbrev toUnderArrowLeftFunc : Over Ψ ⥤ Under (Arrow.leftFunc ⋙ Ψ) :=
  toArrowLeftOver Ψ ⋙ ArrowLeftOver.pushoutFunctor

end Over

variable {C : Type u} [SmallCategory C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type u'} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

namespace ReedyStructure

variable (r : ReedyStructure W₁ W₂ α) {D : Type uD} [Category.{vD} D]
  [HasColimitsOfSize.{u', u'} (Type u)]
  [HasColimitsOfSize.{u, u} D]
  [HasProducts.{u} D]

instance :
    PreservesWellOrderContinuousOfShape α (weightedColim₂.{u} (J := C) (J' := C) (C := D)) where

noncomputable def skFunctor : α ⥤ (C ⥤ D) ⥤ C ⥤ D :=
  r.monotone_skYoneda.functor ⋙ Subfunctor₂.toFunctorFunctor yoneda ⋙ weightedColim₂

variable [NoMaxOrder α]

-- ??
local instance {C' : Type*} [Category* C'] : HasInitial (C' ⥤ C ⥤ D) := by infer_instance

noncomputable def cellComplexSk :
    RelativeCellComplex.{u} (fun j i ↦ weightedColim₂.map (r.basicCell j i))
      (initial.to (𝟭 (C ⥤ D))) :=
  (r.relativeCellComplex.map weightedColim₂.{u}).ofArrowIso
    (Arrow.isoMk (initialIsInitial.uniqueUpToIso
      (IsInitial.isInitialObj weightedColim₂ _ (Subfunctor₂.isInitialBot _)))
    (weightedColim₂ObjYonedaIso C D).symm (initial.hom_ext _ _)).symm

noncomputable abbrev sk : α ⥤ (C ⥤ D) ⥤ (C ⥤ D) := r.cellComplexSk.F

variable [HasColimitsOfShape α D] [HasIterationOfShape α D]

instance {K : Type*} [Category* K] [HasColimitsOfShape K D] [HasColimitsOfShape K (Type u)] :
    PreservesColimitsOfShape K
      (Over.post (X := yoneda (C := C)) (weightedColim₂ (C := D))) where
  preservesColimit {G} := ⟨fun {c} hc ↦
    ⟨isColimitOfReflects (Over.forget _) (by
      exact isColimitOfPreserves (Over.forget _ ⋙ weightedColim₂.{u}) hc)⟩⟩

instance :
    PreservesWellOrderContinuousOfShape α
      (Over.post (X := yoneda (C := C)) (weightedColim₂ (C := D))) where
  preservesColimitsOfShape m hm := by
    have := hasColimitsOfShape_of_isSuccLimit D m hm
    infer_instance

instance [HasColimitsOfSize.{v'', u''} D] [HasColimitsOfSize.{v'', u''} (Type u)] :
    PreservesColimitsOfSize.{v'', u''}
      (Over.post (X := yoneda (C := C)) (weightedColim₂.{u} (J := C) (J' := C) (C := D))) where

local instance : HasFiniteColimits D := by
  have : HasColimitsOfSize.{0, 0} D := hasColimitsOfSizeShrink D
  infer_instance

section

instance : PreservesWellOrderContinuousOfShape α (Over.toArrowLeftOver (𝟭 (C ⥤ D))) := sorry

instance : PreservesColimitsOfShape α (Over.toArrowLeftOver (𝟭 (C ⥤ D))) := sorry

instance (T : Type u) :
    PreservesColimitsOfShape (Discrete T) (Over.toArrowLeftOver (𝟭 (C ⥤ D))) := sorry

instance : PreservesFiniteColimits (Over.toArrowLeftOver (𝟭 (C ⥤ D))) := sorry

-- this should be the relative skeleton of a map in `C ⥤ D`, functoriality in `Arrow (C ⥤ D)`
#check (r.relativeCellComplexOver.map (Over.post (weightedColim₂.{u} (C := D)) ⋙
  Over.map (weightedColim₂ObjYonedaIso C D).hom ⋙ Over.toUnderArrowLeftFunc (𝟭 (C ⥤ D)))).ofUnder

end

end ReedyStructure

end CategoryTheory

/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Reedy.Limits.Initial
public import Reedy.Limits.PreservesWellOrderContinuous
public import Reedy.Limits.Pushout
public import Reedy.Reedy.RelativeCellComplex
public import Reedy.RelativeCellComplex.Map
public import Reedy.RelativeCellComplex.OfArrowIso
public import Reedy.RelativeCellComplex.Under
public import Reedy.WeightedLimits.Colimits

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
@[simps]
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

section

instance {K : Type*} [Category* K] [HasColimitsOfShape K C₂] :
    PreservesColimitsOfShape K (toArrowLeftOver Ψ) where
  preservesColimit := ⟨fun hc ↦
    ⟨isColimitOfReflects (ArrowLeftOver.forget _)
      (Arrow.leftRightJointlyReflectColimit
        (evaluationJointlyReflectsColimits _
          (fun f ↦ isColimitOfPreserves (Over.forget _ ⋙ (evaluation _ _).obj f.left) hc))
        (evaluationJointlyReflectsColimits _
          (fun f ↦ isColimitOfPreserves (Over.forget _ ⋙ (evaluation _ _).obj f.right) hc)))⟩⟩

instance {α : Type*} [LinearOrder α] [HasIterationOfShape α C₂] :
    PreservesWellOrderContinuousOfShape α (toArrowLeftOver Ψ) where
  preservesColimitsOfShape m hm := by
    have := hasColimitsOfShape_of_isSuccLimit C₂ m hm
    infer_instance

end

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

noncomputable def basicCellRelativeSk (a : α) (c : r.Cell a) :=
  (Over.post (weightedColim₂.{u} (C := D)) ⋙
    Over.map (weightedColim₂ObjYonedaIso C D).hom ⋙ Over.toUnderArrowLeftFunc (𝟭 (C ⥤ D)) ⋙
      Under.forget _).map (r.basicCellOver a c)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
noncomputable def relativeCellComplexSk :
    RelativeCellComplex.{u} (r.basicCellRelativeSk (D := D)) Arrow.leftToRight :=
    (r.relativeCellComplexOver.map (Over.post (weightedColim₂.{u} (C := D)) ⋙
      Over.map (weightedColim₂ObjYonedaIso C D).hom ⋙
        Over.toUnderArrowLeftFunc (𝟭 (C ⥤ D)))).ofUnder.ofArrowIso (by
    refine (Arrow.isoMk ?_ ?_ ?_).symm
    · exact (Functor.rightUnitor _).symm ≪≫ pushout.inrIso' _ _ (by
        refine isIso_of_isInitial ?_ ?_ _
        all_goals
        · exact IsInitial.functorComp
            (IsInitial.functorMapArrow
              (IsInitial.isInitialObj weightedColim₂ _
                (Subfunctor₂.isInitialBot _))) _)
    · exact (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight ((Functor.mapArrowFunctor _ _).mapIso
          (weightedColim₂ObjYonedaIso C D).symm) _ ≪≫ pushout.inlIso' _ _ (by
        dsimp
        simp only [Functor.map_id, Functor.whiskerLeft_id', Category.id_comp]
        infer_instance)
    · dsimp [ArrowLeftOver.mk, ArrowLeftOver.top]
      simp only [Category.assoc, colimit.ι_desc, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app,
        Category.id_comp]
      let b := Arrow.leftFunc.whiskerLeft (weightedColim₂.{u}.map (𝟙 yoneda)) ≫
        Arrow.leftFunc.whiskerLeft (weightedColim₂ObjYonedaIso C D).hom
      have : Arrow.leftFunc.rightUnitor.inv =
        Arrow.leftFunc.rightUnitor.inv ≫ Arrow.leftFunc.whiskerLeft
          (weightedColim₂ObjYonedaIso C D).inv ≫ b := by
        dsimp [b]
        rw [Functor.map_id, Functor.whiskerLeft_id', Category.id_comp,
          ← Functor.whiskerLeft_comp]
        simp
      rw [this, Category.assoc, Category.assoc, ← pushout.condition]
      simp only [← Category.assoc]
      congr 1
      ext f X
      dsimp
      simp only [Category.id_comp, Category.comp_id]
      exact ((weightedColimObjYonedaObjIso D X).inv.naturality f.hom).symm)

lemma exists_isPushout (a : α) (c : r.Cell a) {F G : C ⥤ D} (f : F ⟶ G) :
    ∃ t b, IsPushout t
      ((weightedColim₂.{u}.leibnizPushout.obj
        (Arrow.mk (r.externalUnionProd c.val).ι)).obj (Arrow.mk f)).hom
      ((r.basicCellRelativeSk a c).app (Arrow.mk f)) b := by
  sorry

end ReedyStructure

end CategoryTheory

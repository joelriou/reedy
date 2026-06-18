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

open Limits

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

end Over

end CategoryTheory

namespace HomotopicalAlgebra

open CategoryTheory Limits Opposite FunctorToTypes

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

variable (D) in
noncomputable abbrev overYonedaToUnderArrowLeftFunc :
    Over (yoneda (C := C)) ⥤ Under (Arrow.leftFunc (C := C ⥤ D)) :=
    (Over.post (weightedColim₂.{u} (C := D)) ⋙
      Over.map (weightedColim₂ObjYonedaIso C D).hom ⋙
      Over.toArrowLeftOver (𝟭 (C ⥤ D)) ⋙ ArrowLeftOver.pushoutFunctor)

namespace overYonedaToUnderArrowLeftFunc

variable (D)

section

variable {W : C ⥤ Cᵒᵖ ⥤ Type u} (ιW : W ⟶ yoneda)

noncomputable abbrev inl :
    Arrow.rightFunc ⋙ weightedColim₂.obj W ⟶
      ((overYonedaToUnderArrowLeftFunc D).obj (Over.mk ιW)).right :=
  pushout.inl _ _

noncomputable abbrev inr :
    Arrow.leftFunc ⟶
      ((overYonedaToUnderArrowLeftFunc D).obj (Over.mk ιW)).right :=
  pushout.inr _ _

variable (W) in
noncomputable abbrev top :
    Arrow.leftFunc ⋙ (weightedColim₂ (C := D)).obj W ⟶
      Arrow.rightFunc ⋙ weightedColim₂.obj W :=
  Functor.whiskerRight Arrow.leftToRight _

noncomputable abbrev left :
    Arrow.leftFunc ⋙ (weightedColim₂ (C := D)).obj W ⟶ Arrow.leftFunc :=
  Arrow.leftFunc.whiskerLeft (weightedColim₂.map ιW) ≫
  Arrow.leftFunc.whiskerLeft (weightedColim₂ObjYonedaIso C D).hom

omit [HasColimitsOfSize.{u', u'} (Type u)] [HasProducts D] in
lemma isPushout :
    IsPushout (top D W) (left D ιW) (inl D ιW) (inr D ιW) :=
  .of_hasPushout ..

omit [HasColimitsOfSize.{u', u'} (Type u)] [HasProducts D] in
@[reassoc (attr := simp)]
lemma w : top D W ≫ inl D ιW = left D ιW ≫ inr D ιW :=
  (isPushout D ιW).w

end

section

variable {W₁ W₂ : C ⥤ Cᵒᵖ ⥤ Type u} (f : W₁ ⟶ W₂)
  (ιW₁ : W₁ ⟶ yoneda) (ιW₂ : W₂ ⟶ yoneda) (fac : f ≫ ιW₂ = ιW₁)

noncomputable def pushoutOfHom :
    Arrow (C ⥤ D) ⥤ C ⥤ D :=
  pushout (Functor.whiskerRight Arrow.leftToRight (weightedColim₂.{u}.obj W₁))
    (Functor.whiskerLeft Arrow.leftFunc (weightedColim₂.{u}.map f))

protected noncomputable def pushoutOfHom.inl :
    Arrow.rightFunc ⋙ weightedColim₂.obj W₁ ⟶ pushoutOfHom D f :=
  pushout.inl _ _

protected noncomputable def pushoutOfHom.inr :
    Arrow.leftFunc ⋙ weightedColim₂.obj W₂ ⟶ pushoutOfHom D f :=
  pushout.inr _ _

omit [HasColimitsOfSize.{u', u'} (Type u)] [HasProducts D] in
lemma isPushout_pushoutOfHom :
    IsPushout
      (Functor.whiskerRight Arrow.leftToRight (weightedColim₂.obj W₁))
      (Functor.whiskerLeft Arrow.leftFunc (weightedColim₂.map f))
      (pushoutOfHom.inl D f) (pushoutOfHom.inr D f) :=
  .of_hasPushout ..

set_option backward.defeqAttrib.useBackward true in
noncomputable def pushoutOfHom.ι : pushoutOfHom D f ⟶ Arrow.rightFunc ⋙ weightedColim₂.obj W₂ :=
  pushout.desc (Functor.whiskerLeft _ (weightedColim₂.map f))
    (Functor.whiskerRight (Arrow.leftToRight) _)

omit [HasColimitsOfSize.{u', u'} (Type u)] [HasProducts D] in
@[reassoc (attr := simp)]
lemma pushoutOfHom.inl_ι :
    pushoutOfHom.inl D f ≫ pushoutOfHom.ι D f = Functor.whiskerLeft _ (weightedColim₂.map f) :=
  pushout.inl_desc ..

omit [HasColimitsOfSize.{u', u'} (Type u)] [HasProducts D] in
@[reassoc (attr := simp)]
lemma pushoutOfHom.inr_ι :
    pushoutOfHom.inr D f ≫ pushoutOfHom.ι D f = Functor.whiskerRight (Arrow.leftToRight) _ :=
  pushout.inr_desc ..

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
noncomputable def pushoutOfHom.toSrc :
    dsimp% pushoutOfHom D f ⟶ ((overYonedaToUnderArrowLeftFunc D).obj (Over.mk ιW₁)).right :=
  pushout.desc (inl D ιW₁) (left D ιW₂ ≫ inr D ιW₁)

omit [HasColimitsOfSize.{u', u'} (Type u)] [HasProducts D] in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma pushoutOfHom.inr_toSrc :
    dsimp% pushoutOfHom.inr D f ≫ pushoutOfHom.toSrc D f ιW₁ ιW₂ fac =
      left D ιW₂ ≫ inr D ιW₁ :=
  pushout.inr_desc ..

omit [HasColimitsOfSize.{u', u'} (Type u)] [HasProducts D] in
@[reassoc (attr := simp)]
lemma pushoutOfHom.inl_toSrc :
    pushoutOfHom.inl D f ≫ pushoutOfHom.toSrc D f ιW₁ ιW₂ fac =
      inl D ιW₁ :=
  pushout.inl_desc ..

omit [HasColimitsOfSize.{u', u'} (Type u)] [HasProducts D] in
lemma isPushout₁ :
    IsPushout (pushoutOfHom.inr D f)
      (left D ιW₂) (pushoutOfHom.toSrc D f ιW₁ ιW₂ fac)
      (inr D ιW₁) := by
  refine IsPushout.of_top ?_ (by simp) (isPushout_pushoutOfHom D f)
  convert isPushout D ιW₁ using 1 <;> cat_disch

set_option backward.isDefEq.respectTransparency false in
omit [HasColimitsOfSize.{u', u'} (Type u)] [HasProducts D] in
lemma isPushout₁₂ :
    IsPushout (pushoutOfHom.ι D f)
      (pushoutOfHom.toSrc D f ιW₁ ιW₂ fac)
      (inl D ιW₂)
      ((overYonedaToUnderArrowLeftFunc D).map
      (Over.homMk f : Over.mk ιW₁ ⟶ Over.mk ιW₂)).right := by
  apply IsPushout.of_left ?_ ?_ (isPushout₁ D f ιW₁ ιW₂ fac)
  · convert isPushout D ιW₂ <;> simp
  · set_option backward.defeqAttrib.useBackward true in
    apply pushout.hom_ext
    · dsimp [pushoutOfHom.ι]
      rw [pushout.inl_desc_assoc]
      erw [pushoutOfHom.inl_toSrc_assoc]
      rw [pushout.inl_desc]
      rfl
    · dsimp [pushoutOfHom.ι]
      rw [pushout.inr_desc_assoc]
      erw [pushoutOfHom.inr_toSrc_assoc]
      rw [pushout.inr_desc]
      cat_disch

end

end overYonedaToUnderArrowLeftFunc

noncomputable def basicCellRelativeSk (a : α) (c : r.Cell a) :=
  (overYonedaToUnderArrowLeftFunc D ⋙ Under.forget _).map (r.basicCellOver a c)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
noncomputable def relativeCellComplexSk :
    RelativeCellComplex.{u} (r.basicCellRelativeSk (D := D)) Arrow.leftToRight :=
    (r.relativeCellComplexOver.map (overYonedaToUnderArrowLeftFunc D)).ofUnder.ofArrowIso (by
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
        simp only [CategoryTheory.Functor.map_id, Functor.whiskerLeft_id', Category.id_comp]
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
        rw [CategoryTheory.Functor.map_id, Functor.whiskerLeft_id', Category.id_comp,
          ← Functor.whiskerLeft_comp]
        simp
      rw [this, Category.assoc, Category.assoc, ← pushout.condition]
      simp only [← Category.assoc]
      congr 1
      ext f X
      dsimp
      simp only [Category.id_comp, Category.comp_id]
      exact ((weightedColimObjYonedaObjIso D X).inv.naturality f.hom).symm)

omit [HasColimitsOfSize.{u', u'} (Type u)] [HasProducts D]
  [NoMaxOrder α] [HasColimitsOfShape α D] [HasIterationOfShape α D] in
lemma exists_isPushout (a : α) (c : r.Cell a) {F G : C ⥤ D} (f : F ⟶ G) :
    ∃ t b, IsPushout t ((overYonedaToUnderArrowLeftFunc.pushoutOfHom.ι D
      ((r.boundaryCoyonedaObj c).unionExternalProd (r.boundaryYonedaObj c)).ι).app
      (Arrow.mk f)) ((r.basicCellRelativeSk a c).app (Arrow.mk f)) b :=
  ⟨_, _, (overYonedaToUnderArrowLeftFunc.isPushout₁₂ D _ _ _
    (Over.w (r.basicCellOver a c))).flip.map ((evaluation _ _).obj (Arrow.mk f))⟩

end ReedyStructure

end HomotopicalAlgebra

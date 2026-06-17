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
# Latching objects

-/

universe u

@[expose] public section

namespace HomotopicalAlgebra

open CategoryTheory Opposite Limits FunctorToTypes

variable {C : Type u} [SmallCategory C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

namespace ReedyStructure

variable (r : ReedyStructure W₁ W₂ α) {D : Type*} [Category* D]
  [HasColimitsOfSize.{u, u} D] (X : C)

-- C.4.14
noncomputable abbrev latching : (C ⥤ D) ⥤ D :=
  weightedColim.obj (r.boundaryYonedaObj X).toFunctor

noncomputable def latchingι : r.latching X ⟶ (evaluation C D).obj X :=
  weightedColim.map (r.boundaryYonedaObj X).ι ≫
    (weightedColimObjYonedaObjIso D X).hom

noncomputable def relativeLatchingSrc : Arrow (C ⥤ D) ⥤ D :=
  pushout (Functor.whiskerLeft _ (r.latchingι X)) (Functor.whiskerRight Arrow.leftToRight _)

noncomputable def relativeLatchingSrc.inl :
    Arrow.leftFunc ⋙ (evaluation C D).obj X ⟶ r.relativeLatchingSrc X :=
  pushout.inl _ _

noncomputable def relativeLatchingSrc.inr :
    Arrow.rightFunc ⋙ r.latching (D := D) X ⟶ r.relativeLatchingSrc X :=
  pushout.inr _ _

@[reassoc]
lemma relativeLatchingSrc.condition :
    Functor.whiskerLeft _ (r.latchingι X) ≫ relativeLatchingSrc.inl r (D := D) X =
      Functor.whiskerRight Arrow.leftToRight _ ≫ relativeLatchingSrc.inr r X :=
  pushout.condition

lemma relativeLatchingSrc.isPushout :
    IsPushout (Functor.whiskerLeft _ (r.latchingι X))
      (Functor.whiskerRight Arrow.leftToRight _)
      (relativeLatchingSrc.inl r (D := D) X)
      (relativeLatchingSrc.inr r X) :=
  IsPushout.of_hasPushout _ _

section

variable (X : C) {F₁ F₂ : C ⥤ D} (f : F₁ ⟶ F₂)

noncomputable abbrev relativeLatchingObj : D :=
  (r.relativeLatchingSrc X).obj (Arrow.mk f)

noncomputable abbrev relativeLatchingObj.inl : F₁.obj X ⟶ r.relativeLatchingObj X f :=
  (relativeLatchingSrc.inl r X).app (Arrow.mk f)

noncomputable abbrev relativeLatchingObj.inr : (r.latching X).obj F₂ ⟶ r.relativeLatchingObj X f :=
  (relativeLatchingSrc.inr r X).app (Arrow.mk f)

lemma relativeLatchingObj.isPushout :
    IsPushout ((r.latchingι X).app F₁) ((r.latching X).map f)
      (relativeLatchingObj.inl r X f) (relativeLatchingObj.inr r X f) :=
  (relativeLatchingSrc.isPushout r X).map ((evaluation _ _).obj (Arrow.mk f))

@[reassoc]
lemma relativeLatchingObj.condition :
    (r.latchingι X).app F₁ ≫ relativeLatchingObj.inl r X f =
      (r.latching X).map f ≫ relativeLatchingObj.inr r X f :=
  (relativeLatchingObj.isPushout r X f).w

end

noncomputable def relativeLatchingMap (X : C) :
    r.relativeLatchingSrc X ⟶ Arrow.rightFunc ⋙ (evaluation C D).obj X :=
  pushout.desc _ _ (Functor.whiskerLeft_comp_whiskerRight _ _)

-- C.4.15
noncomputable def relativeLatchingFunctor (X : C) : Arrow (C ⥤ D) ⥤ Arrow D :=
  Arrow.mkFunctor (r.relativeLatchingMap X)

end ReedyStructure

end HomotopicalAlgebra

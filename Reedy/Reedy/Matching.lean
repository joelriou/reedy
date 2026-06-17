/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.Arrow.MkFunctor
public import Reedy.Reedy.RelativeCellComplex
public import Reedy.WeightedLimits.Limits

/-!
# Matching

-/

universe u

@[expose] public section

namespace CategoryTheory

open HomotopicalAlgebra Opposite Limits FunctorToTypes

variable {C : Type u} [SmallCategory C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

namespace ReedyStructure

variable (r : ReedyStructure W₁ W₂ α) {D : Type*} [Category* D]
  [HasLimitsOfSize.{u, u} D]

variable (X : C)

-- C.4.14
noncomputable abbrev matching : (C ⥤ D) ⥤ D :=
  weightedLim.obj (op (r.boundaryCoyonedaObj X).toFunctor)

noncomputable def matchingπ : (evaluation C D).obj X ⟶ r.matching X :=
  (weightedLimObjCoyonedaObjIso D X).inv ≫
    weightedLim.map (r.boundaryCoyonedaObj X).ι.op

noncomputable def relativeMatchingTgt : Arrow (C ⥤ D) ⥤ D :=
  pullback (Functor.whiskerLeft _ (r.matchingπ X)) (Functor.whiskerRight Arrow.leftToRight _)

noncomputable def relativeMatchingTgt.fst :
    r.relativeMatchingTgt X ⟶ Arrow.rightFunc ⋙ (evaluation C D).obj X :=
  pullback.fst _ _

noncomputable def relativeMatchingTgt.snd :
    r.relativeMatchingTgt X ⟶ Arrow.leftFunc ⋙ r.matching (D := D) X :=
  pullback.snd _ _

@[reassoc]
lemma relativeMatchingTgt.condition :
  relativeMatchingTgt.fst r X ≫ Functor.whiskerLeft _ (r.matchingπ X) =
    relativeMatchingTgt.snd r (D := D) X ≫ Functor.whiskerRight Arrow.leftToRight _ :=
  pullback.condition

lemma relativeMatchingTgt.isPullback :
    IsPullback (relativeMatchingTgt.fst r X) (relativeMatchingTgt.snd r (D := D) X)
      (Functor.whiskerLeft _ (r.matchingπ X))  (Functor.whiskerRight Arrow.leftToRight _) :=
  IsPullback.of_hasPullback _ _

section

variable (X : C) {F₁ F₂ : C ⥤ D} (f : F₁ ⟶ F₂)

noncomputable abbrev relativeMatchingObj : D :=
  (r.relativeMatchingTgt X).obj (Arrow.mk f)

noncomputable abbrev relativeMatchingObj.fst : r.relativeMatchingObj X f ⟶ F₂.obj X :=
  (relativeMatchingTgt.fst r X).app (Arrow.mk f)

noncomputable abbrev relativeMatchingObj.snd : r.relativeMatchingObj X f ⟶ (r.matching X).obj F₁ :=
  (relativeMatchingTgt.snd r X).app (Arrow.mk f)

lemma relativeMatchingObj.isPullback :
    IsPullback (relativeMatchingObj.fst r X f) (relativeMatchingObj.snd r X f)
      ((r.matchingπ X).app F₂)
      ((r.matching X).map f) :=
  (relativeMatchingTgt.isPullback r X).map ((evaluation _ _).obj (Arrow.mk f))

@[reassoc]
lemma relativeMatchingObj.condition :
    relativeMatchingObj.fst r X f ≫ (r.matchingπ X).app F₂ =
      relativeMatchingObj.snd r X f ≫ (r.matching X).map f :=
  (relativeMatchingObj.isPullback r X f).w

end

noncomputable def relativeMatchingMap (X : C) :
    Arrow.leftFunc ⋙ (evaluation C D).obj X ⟶ r.relativeMatchingTgt X :=
  pullback.lift _ _ (Functor.whiskerLeft_comp_whiskerRight _ _).symm

-- C.4.15
noncomputable def relativeMatchingFunctor (X : C) : Arrow (C ⥤ D) ⥤ Arrow D :=
  Arrow.mkFunctor (r.relativeMatchingMap X)

end ReedyStructure

end CategoryTheory

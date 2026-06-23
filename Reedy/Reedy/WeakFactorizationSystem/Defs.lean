/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Reedy.Arrow.ObjectProperty
public import Reedy.MorphismProperty.Retracts
public import Reedy.ObjectProperty.Retracts
public import Reedy.Reedy.Latching
public import Reedy.Reedy.Matching
public import Reedy.Reedy.Skeleton
public import Reedy.Limits.PushoutObjObjObj

/-!
# Weak factorization systems on the category of functors

If `C` is a Reedy category, and `D` a category equipped with a
weak factorization system `(W₁, W₂)`, we define a weak
factorization system on `C ⥤ D`. If `D` is a model category
structure, the Reedy model category structure on `C ⥤ D` will
be obtained by applying this construction to
`(cofibrations D, trivialFibrations D)`
and `(trivialCofibrations D, fibrations D)`.


-/

universe w u

@[expose] public section

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable {C : Type u} [SmallCategory C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type w} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

namespace ReedyStructure

open MorphismProperty

variable (r : ReedyStructure W₁ W₂ α) {D : Type*} [Category* D]
  (P₁ : MorphismProperty D) (P₂ : MorphismProperty D)

def left [HasColimitsOfSize.{u, u} D] : MorphismProperty (C ⥤ D) :=
  ⨅ (X : C), .ofArrowObj (P₁.arrowObj.inverseImage (r.relativeLatchingFunctor X))

variable {r P₁} in
lemma left.apply [HasColimitsOfSize.{u, u} D] {F G : C ⥤ D} {f : F ⟶ G} (h : r.left P₁ f) (X : C) :
    P₁ ((r.relativeLatchingFunctor X).obj (Arrow.mk f)).hom := by
  simp only [left, iInf_iff] at h
  exact h _

variable {r P₁} in
set_option backward.isDefEq.respectTransparency false in
lemma left.apply' [P₁.RespectsIso] [HasColimitsOfSize.{u, u} D] {F G : C ⥤ D} {f : F ⟶ G}
    (h : r.left P₁ f) (X : C) :
    P₁ (r.relativeLatchingPushoutObjObj X f).ι := by
  refine (P₁.arrow_mk_iso_iff ?_).1 (h.apply X)
  exact Arrow.isoMk (Iso.refl _) ((weightedColimObjYonedaObjIso D X).symm.app G)

def right [HasLimitsOfSize.{u, u} D] : MorphismProperty (C ⥤ D) :=
  ⨅ (X : C), .ofArrowObj (P₂.arrowObj.inverseImage (r.relativeMatchingFunctor X))

variable {r P₂} in
lemma right.apply [HasLimitsOfSize.{u, u} D] {F G : C ⥤ D} {f : F ⟶ G} (h : r.right P₂ f) (X : C) :
    P₂ ((r.relativeMatchingFunctor X).obj (Arrow.mk f)).hom := by
  simp only [right, iInf_iff] at h
  exact h _

variable {r P₂} in
set_option backward.isDefEq.respectTransparency false in
lemma right.apply' [P₂.RespectsIso] [HasLimitsOfSize.{u, u} D] {F G : C ⥤ D} {f : F ⟶ G}
    (h : r.right P₂ f) (X : C) :
    P₂ (r.relativeMatchingPullbackObjObj X f).π := by
  refine (P₂.arrow_mk_iso_iff ?_).2 (h.apply X)
  exact Arrow.isoMk ((weightedLimObjCoyonedaObjIso D X).app _) (Iso.refl _)

variable [HasColimitsOfSize.{u, u} D] [HasLimitsOfSize.{u, u} D]

instance [P₁.IsStableUnderRetracts] : (r.left P₁).IsStableUnderRetracts := by
  dsimp [left]
  infer_instance

instance [P₂.IsStableUnderRetracts] : (r.right P₂).IsStableUnderRetracts := by
  dsimp [right]
  infer_instance

end ReedyStructure

end HomotopicalAlgebra

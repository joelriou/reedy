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

def right [HasLimitsOfSize.{u, u} D] : MorphismProperty (C ⥤ D) :=
  ⨅ (X : C), .ofArrowObj (P₂.arrowObj.inverseImage (r.relativeMatchingFunctor X))

variable {r P₂} in
lemma right.apply [HasLimitsOfSize.{u, u} D] {F G : C ⥤ D} {f : F ⟶ G} (h : r.right P₂ f) (X : C) :
    P₂ ((r.relativeMatchingFunctor X).obj (Arrow.mk f)).hom := by
  simp only [right, iInf_iff] at h
  exact h _

variable [HasColimitsOfSize.{u, u} D] [HasLimitsOfSize.{u, u} D]

instance [P₁.IsStableUnderRetracts] : (r.left P₁).IsStableUnderRetracts := by
  dsimp [left]
  infer_instance

instance [P₂.IsStableUnderRetracts] : (r.right P₂).IsStableUnderRetracts := by
  dsimp [right]
  infer_instance

-- C.5.7
instance [P₁.HasFactorization P₂] : (r.left P₁).HasFactorization (r.right P₂) := sorry

variable [HasColimitsOfSize.{w, w} (Type u)] [NoMaxOrder α]
  [HasColimitsOfShape α D] [HasIterationOfShape α D]

-- C.5.6
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma hasLiftingProperty [IsWeakFactorizationSystem P₁ P₂]
    {A B X Y : C ⥤ D} (i : A ⟶ B) (p : X ⟶ Y) (hi : r.left P₁ i) (hp : r.right P₂ p) :
    HasLiftingProperty i p := by
  suffices llp (.single p) i from this _ (prop_single p)
  refine (?_ : (_ : MorphismProperty _) ≤ _) _
    ((r.relativeCellComplexSk.map ((evaluation _ _).obj
    (Arrow.mk i))).transfiniteCompositionOfShape'
    (I := (MorphismProperty.single p).llp) ?_).mem
  · simp only [coproducts_eq_self]
    exact le_trans (transfiniteCompositionsOfShape_monotone _ (by simp))
      (transfiniteCompositionsOfShape_le _ _)
  · intro c
    obtain ⟨t, b, sq⟩ := r.exists_isPushout c.j c.i i
    refine MorphismProperty.of_isPushout sq ?_
    replace hi := hi.apply c.i
    replace hp := hp.apply c.i
    rw [llp_ofHoms_iff_hasLiftingProperty]
    let α := (Subfunctor.pushoutObjObjExternalProductFunctor
      (r.boundaryCoyonedaObj c.i) (r.boundaryYonedaObj c.i))
    let β := overYonedaToUnderArrowLeftFunc.pushoutOfHom.pushoutObjObj D α.ι i
    let αβ := Functor.PushoutObjObj.bifunctorComp₁₂ α β
    let α' := r.relativeLatchingPushoutObjObj c.i i
    have (Z : C ⥤ Type u) : PreservesColimit
      (span ((weightedColim.map (r.boundaryYonedaObj ↑c.i).ι).app A)
      ((weightedColim.obj (r.boundaryYonedaObj ↑c.i).toFunctor).map i))
      (weightedLimLeftAdj.obj Z) := by sorry
    let β' : weightedLimLeftAdj.PushoutObjObj
      (r.boundaryCoyonedaObj c.i).ι α'.ι := .ofHasPushout ..
    let αβ' := (Functor.PushoutObjObj.bifunctorComp₂₃ α' β').ofNatIso
      weightedColim₂.bifunctorComp₁₂Iso.symm
    have e : Arrow.mk β.ι ≅ Arrow.mk β'.ι :=
      (αβ.arrowUnique ((Functor.PushoutObjObj.bifunctorComp₂₃ α' β').ofNatIso
        weightedColim₂.bifunctorComp₁₂Iso.symm)).trans
          (Arrow.isoMk (Iso.refl _)
            (((weightedColim₂.bifunctorComp₁₂Iso.app _).app _).app _))
    change HasLiftingProperty β.ι p
    rw [HasLiftingProperty.iff_of_arrow_iso_left e,
      weightedLimAdj₂.hasLiftingProperty_iff _ sorry]
    sorry

-- C.5.5
instance isWeakFactorizationSystem [IsWeakFactorizationSystem P₁ P₂] :
    IsWeakFactorizationSystem (r.left P₁) (r.right P₂) :=
  have : P₁.IsStableUnderRetracts := by rw [← llp_eq_of_wfs P₁ P₂]; infer_instance
  have : P₂.IsStableUnderRetracts := by rw [← rlp_eq_of_wfs P₁ P₂]; infer_instance
  .mk' _ _ (r.hasLiftingProperty _ _)

end ReedyStructure

end HomotopicalAlgebra

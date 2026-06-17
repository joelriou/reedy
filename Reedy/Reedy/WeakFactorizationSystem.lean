/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Reedy.Arrow.ObjectProperty
public import Reedy.MorphismProperty.Retracts
public import Reedy.ObjectProperty.Retracts
public import Reedy.Reedy.Latching
public import Reedy.Reedy.Matching
public import Reedy.Reedy.Skeleton

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

namespace CategoryTheory

open HomotopicalAlgebra Limits

variable {C : Type u} [SmallCategory C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type w} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

namespace ReedyStructure

open MorphismProperty

variable (r : ReedyStructure W₁ W₂ α) {D : Type*} [Category* D]
  [HasColimitsOfSize.{u, u} D] [HasLimitsOfSize.{u, u} D]
  (P₁ : MorphismProperty D) (P₂ : MorphismProperty D)

def left : MorphismProperty (C ⥤ D) :=
  ⨅ (X : C), .ofArrowObj (P₁.arrowObj.inverseImage (r.relativeLatchingFunctor X))

def right : MorphismProperty (C ⥤ D) :=
  ⨅ (X : C), .ofArrowObj (P₂.arrowObj.inverseImage (r.relativeMatchingFunctor X))

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
    sorry

-- C.5.5
instance isWeakFactorizationSystem [IsWeakFactorizationSystem P₁ P₂] :
    IsWeakFactorizationSystem (r.left P₁) (r.right P₂) :=
  have : P₁.IsStableUnderRetracts := by rw [← llp_eq_of_wfs P₁ P₂]; infer_instance
  have : P₂.IsStableUnderRetracts := by rw [← rlp_eq_of_wfs P₁ P₂]; infer_instance
  .mk' _ _ (r.hasLiftingProperty _ _)

end ReedyStructure

end CategoryTheory

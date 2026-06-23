/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.Reedy.WeakFactorizationSystem.Defs

/-!
# The lifting property

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
  [HasColimitsOfSize.{w, w} (Type u)] [NoMaxOrder α]
  [HasColimitsOfShape α D] [HasIterationOfShape α D]
  [HasColimitsOfSize.{u, u} D] [HasLimitsOfSize.{u, u} D]

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
    rw [llp_ofHoms_iff_hasLiftingProperty]
    let α := (Subfunctor.pushoutObjObjExternalProductFunctor
      (r.boundaryCoyonedaObj c.i) (r.boundaryYonedaObj c.i))
    let β := overYonedaToUnderArrowLeftFunc.pushoutOfHom.pushoutObjObj D α.ι i
    let αβ := Functor.PushoutObjObj.bifunctorComp₁₂ α β
    let α' := r.relativeLatchingPushoutObjObj c.i i
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
      weightedLimAdj₂.hasLiftingProperty_iff _
        (r.relativeMatchingPullbackObjObj c.i p)]
    have : P₁.RespectsIso := by
      rw [← llp_eq_of_wfs P₁ P₂]
      infer_instance
    have : P₂.RespectsIso := by
      rw [← rlp_eq_of_wfs P₁ P₂]
      infer_instance
    exact hasLiftingProperty_of_wfs _ _ (hi.apply' c.i) (hp.apply' c.i)

end ReedyStructure

end HomotopicalAlgebra

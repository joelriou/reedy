/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.Adjunction.ParametrizedColimits
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Weighted colimits

-/

-- When working on this file, claim the following issue:
-- https://github.com/joelriou/reedy/issues/12


@[expose] public section

universe w v u

namespace CategoryTheory.Limits

open Opposite

-- See A.6 in Riehl-Verity (here, we do not need the enriched version)

variable {J : Type u} [Category.{v} J] {C : Type*} [Category* C]

abbrev WeightedCocone (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) :=
  Cocone ((CategoryOfElements.π P).leftOp ⋙ F)

namespace WeightedCocone

variable {P : Jᵒᵖ ⥤ Type w} {F : J ⥤ C}

protected abbrev ι (c : WeightedCocone P F) {j : J} (x : P.obj (op j)) :
    F.obj j ⟶ c.pt :=
  (Cocone.ι c).app (op (Functor.elementsMk _ _ x))

variable (pt : C) (ι : ∀ ⦃j : J⦄ (_ : P.obj (op j)), F.obj j ⟶ pt)
  (hι : ∀ ⦃j₁ j₂ : J⦄ (x : P.obj (op j₁)) (f : j₂ ⟶ j₁),
    F.map f ≫ ι x = ι (P.map f.op x))
set_option backward.defeqAttrib.useBackward true in

@[simps pt]
def mk : WeightedCocone P F where
  pt := pt
  ι.app x := ι x.unop.2
  ι.naturality x₁ x₂ f := by simpa using hι (x₂.unop.2) f.unop.1.unop

@[simp]
lemma mk_ι {j : J} (x : P.obj (op j)) :
    (mk pt ι hι).ι x = ι x := rfl

protected abbrev IsColimit (c : WeightedCocone P F) := Limits.IsColimit c

namespace IsColimit

variable {c : WeightedCocone P F} (hc : c.IsColimit)
  {Z : C} (ι : ∀ ⦃j : J⦄ (_ : P.obj (op j)), F.obj j ⟶ Z)
  (hι : ∀ ⦃j₁ j₂ : J⦄ (x : P.obj (op j₁)) (f : j₂ ⟶ j₁),
    F.map f ≫ ι x = ι (P.map f.op x))

def desc : c.pt ⟶ Z :=
  Limits.IsColimit.desc hc (WeightedCocone.mk Z ι hι)

@[reassoc (attr := simp)]
lemma fac {j : J} (x : P.obj (op j)) :
    c.ι x ≫ hc.desc ι hι = ι x :=
  Limits.IsColimit.fac hc (WeightedCocone.mk Z ι hι) (op (Functor.elementsMk _ _ x))

end IsColimit

set_option backward.defeqAttrib.useBackward true in
@[simps]
protected def yoneda (F : J ⥤ C) (j : J) :
    WeightedCocone (yoneda.obj j) F where
  pt := F.obj j
  ι.app u := F.map u.unop.2
  ι.naturality _ _ f := by
    dsimp
    simp only [← Functor.map_comp, Category.comp_id]
    congr
    exact f.unop.2

def isColimitYoneda (F : J ⥤ C) (j : J) : (WeightedCocone.yoneda F j).IsColimit  := by
  -- use that the category of elements has an initial object
  sorry

end WeightedCocone

section

variable [HasColimitsOfSize.{v, max u w} C]

noncomputable def weightedColim : (Jᵒᵖ ⥤ Type w) ⥤ (J ⥤ C) ⥤ C where
  obj P := (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π P).leftOp ⋙ colim
  map := sorry

noncomputable def weightedColimObjObjι
    (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) ⦃j : J⦄ (x : P.obj (op j)) :
    F.obj j ⟶ (weightedColim.obj P).obj F :=
  colimit.ι ((CategoryOfElements.π P).leftOp ⋙ F) (op (Functor.elementsMk _ _ x))

@[reassoc (attr := simp)]
noncomputable def weightedColimObjObj_w
    (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) ⦃j₁ j₂ : J⦄ (x : P.obj (op j₁))
    (f : j₂ ⟶ j₁) :
    F.map f ≫ weightedColimObjObjι P F x =
      weightedColimObjObjι P F (P.map f.op x) := by
  let g : Functor.elementsMk _ _ x ⟶ Functor.elementsMk _ _ (P.map f.op x) :=
    ⟨f.op, rfl⟩
  exact colimit.w ((CategoryOfElements.π P).leftOp ⋙ F) g.op

noncomputable abbrev weightedColimCocone (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) :
    WeightedCocone P F :=
  WeightedCocone.mk ((weightedColim.obj P).obj F)
    (fun j x ↦ weightedColimObjObjι P F x)
    (fun j₁ j₂ x f ↦ by simp)

noncomputable def isColimitWeightedColimCocone (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) :
    (weightedColimCocone P F).IsColimit :=
  colimit.isColimit _

noncomputable def WeightedCocone.IsColimit.iso
    {P : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {c : WeightedCocone P F}
    (hc : c.IsColimit) :
    (weightedColim.obj P).obj F ≅ c.pt :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc

instance (P : Jᵒᵖ ⥤ Type w) {K : Type*} [Category* K] [HasColimitsOfShape K C] :
    PreservesColimitsOfShape K (weightedColim.obj P : (J ⥤ C) ⥤ C) where
  preservesColimit {G} := by dsimp [weightedColim]; infer_instance

section

variable [HasProducts.{w} C]

-- hopefully, this is the expect parametrized right adjoint to `weightedColim`
@[simps]
noncomputable def weightedColimRightAdj : (Jᵒᵖ ⥤ Type w)ᵒᵖ ⥤ C ⥤ (J ⥤ C) where
  obj P := piConst.{w} ⋙ (Functor.whiskeringLeft ..).obj P.unop.rightOp
  map {P₁ P₂} f := Functor.whiskerLeft _ ((Functor.whiskeringLeft ..).map f.unop.rightOp)

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Pi.lift_π in
noncomputable def weightedColimHomEquiv (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) (X : C) :
    ((weightedColim.obj P).obj F ⟶ X) ≃ (F ⟶ P.rightOp ⋙ piConst.obj X) where
  toFun x :=
    { app j := Pi.lift (fun y ↦ weightedColimObjObjι P F y ≫ x) }
  invFun f :=
    (isColimitWeightedColimCocone P F).desc (fun j y ↦ f.app j ≫ Pi.π _ y)
      (fun _ _ _ g ↦ by simp [dsimp% f.naturality_assoc g] )
  left_inv := sorry
  right_inv := sorry

noncomputable def weightedColimitAdj₂ :
    weightedColim.{w} (J := J) (C := C) ⊣₂ weightedColimRightAdj where
  adj P :=
    Adjunction.mkOfHomEquiv
      { homEquiv := weightedColimHomEquiv _
        homEquiv_naturality_left_symm := sorry
        homEquiv_naturality_right := sorry }
  unit_whiskerRight_map := sorry

instance (X : C) {K : Type*} [Category* K] [HasLimitsOfShape Kᵒᵖ (Type w)ᵒᵖ] :
    PreservesLimitsOfShape Kᵒᵖ ((piConst.{w}.obj X): (Type w)ᵒᵖ ⥤ C) := by
    sorry

instance (X : C) {K : Type*} [Category* K] [HasLimitsOfShape Kᵒᵖ (Type w)ᵒᵖ] :
    PreservesLimitsOfShape Kᵒᵖ (weightedColimRightAdj.flip.obj X : (Jᵒᵖ ⥤ Type w)ᵒᵖ ⥤ J ⥤ C) := by
    refine ⟨@fun F ↦ ⟨fun {c} hc ↦ ⟨?_⟩ ⟩ ⟩
    apply evaluationJointlyReflectsLimits
    intro j
    have : HasColimitsOfShape Kᵒᵖᵒᵖ (Type w) := by
      rwa [← hasLimitsOfShape_opposite_iff]
    have : PreservesLimit F ((evaluation Jᵒᵖ (Type w)).obj (op j)).op := by
      apply preservesLimit_op
    exact isLimitOfPreserves (((evaluation Jᵒᵖ (Type w)).obj (op j)).op ⋙ piConst.obj X) hc


instance (F : J ⥤ C) {K : Type*} [Category* K] [HasColimitsOfShape K (Type w)] :
    PreservesColimitsOfShape K (weightedColim.flip.obj F : (Jᵒᵖ ⥤ Type w) ⥤ C) := by
    have h : HasLimitsOfShape Kᵒᵖ (Type w)ᵒᵖ := by
      apply +allowSynthFailures hasLimitsOfShape_op_of_hasColimitsOfShape
      apply hasColimitsOfShape_of_equivalence (opOpEquivalence K).symm
    apply weightedColimitAdj₂.preservesColimitsOfShape_flip_obj
  -- strategy: show that `weightedColim` is a left bifunctor in a parametrized
  -- adjunction and dualize the result in `CategoryTheory.Adjunction.ParametrizedLimits`
  -- see https://github.com/joelriou/reedy/issues/11

end

-- A.6 (iv)
@[simps!]
noncomputable def weightedColim₂ {J' : Type*} [Category* J'] :
    (J' ⥤ Jᵒᵖ ⥤ Type w) ⥤ (J ⥤ C) ⥤ (J' ⥤ C) :=
  (weightedColim.{w}.flip ⋙ Functor.whiskeringRight _ _ _).flip

-- show that `weightedColim₂` also preserves colimits in both variables

end

set_option backward.defeqAttrib.useBackward true in
variable (J C) in
noncomputable def weightedColim₂ObjYonedaIso [HasColimitsOfSize.{v, max u v} C] :
    weightedColim₂.obj yoneda ≅ 𝟭 (J ⥤ C) :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents
    (fun j ↦ (WeightedCocone.isColimitYoneda F j).iso) sorry) sorry

end CategoryTheory.Limits

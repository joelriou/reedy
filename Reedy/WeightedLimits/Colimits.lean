/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nima Rasekh, Lyne Moser
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Reedy.Adjunction.ParametrizedColimits
public import Reedy.Limits.Colim
public import Reedy.Limits.PiConst
public import Reedy.Limits.Op

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

variable {c : WeightedCocone P F} (hc : c.IsColimit) {Z : C}

section

variable
  (ι : ∀ ⦃j : J⦄ (_ : P.obj (op j)), F.obj j ⟶ Z)
  (hι : ∀ ⦃j₁ j₂ : J⦄ (x : P.obj (op j₁)) (f : j₂ ⟶ j₁),
    F.map f ≫ ι x = ι (P.map f.op x))

def desc : c.pt ⟶ Z :=
  Limits.IsColimit.desc hc (WeightedCocone.mk Z ι hι)

@[reassoc (attr := simp)]
lemma fac {j : J} (x : P.obj (op j)) :
    c.ι x ≫ hc.desc ι hι = ι x :=
  Limits.IsColimit.fac hc (WeightedCocone.mk Z ι hι) (op (Functor.elementsMk _ _ x))

end

include hc in
lemma hom_ext {f g : c.pt ⟶ Z} (h : ∀ {j : J} (x : P.obj (op j)), c.ι x ≫ f = c.ι x ≫ g) :
    f = g :=
  Limits.IsColimit.hom_ext hc (fun _ ↦ h _)

end IsColimit

set_option backward.defeqAttrib.useBackward true in
@[simps]
protected abbrev yoneda (F : J ⥤ C) (j : J) :
    WeightedCocone (yoneda.obj j) F where
  pt := F.obj j
  ι.app u := F.map u.unop.2
  ι.naturality _ _ f := by
    dsimp
    simp only [← Functor.map_comp, Category.comp_id]
    congr
    exact f.unop.2

set_option backward.defeqAttrib.useBackward true in
def isColimitYoneda (F : J ⥤ C) (j : J) : (WeightedCocone.yoneda F j).IsColimit where
  desc s := WeightedCocone.ι s (𝟙 j)
  fac s x := Cocone.w s ((Functor.Elements.isInitial j).to x.unop).op
  uniq s m hm := by
    simpa [Functor.Elements.initial] using hm (op (Functor.Elements.initial j))

end WeightedCocone

section

variable [HasColimitsOfSize.{v, max u w} C]

set_option backward.defeqAttrib.useBackward true in
@[no_expose]
noncomputable def weightedColim : (Jᵒᵖ ⥤ Type w) ⥤ (J ⥤ C) ⥤ C where
  obj P := (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π P).leftOp ⋙ colim
  map {P₁ P₂} f :=
    Functor.whiskerLeft
      ((Functor.whiskeringLeft P₂.Elementsᵒᵖ J C).obj (CategoryOfElements.π P₂).leftOp)
        (colim.pre (NatTrans.mapElements f).op)
  map_id P := by
    ext F
    dsimp
    ext j
    rw [colimit.ι_pre]
    exact (Category.comp_id _).symm
  map_comp {P₁ P₂ P₃} f g := by
    ext F
    dsimp
    ext j
    rw [colimit.ι_pre]
    dsimp only [colimit.pre]
    -- this will need a cleamup...
    erw [colimit.ι_desc_assoc, colimit.ι_desc]
    rfl

@[no_expose]
noncomputable def weightedColimObjObjι
    (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) ⦃j : J⦄ (x : P.obj (op j)) :
    F.obj j ⟶ (weightedColim.obj P).obj F :=
  colimit.ι ((CategoryOfElements.π P).leftOp ⋙ F) (op (Functor.elementsMk _ _ x))

@[reassoc (attr := simp)]
lemma weightedColim.ι_map_app {P₁ P₂ : Jᵒᵖ ⥤ Type w} (f : P₁ ⟶ P₂) (F : J ⥤ C)
    {j : J} (x : P₁.obj (op j)) :
    weightedColimObjObjι P₁ F x ≫ (weightedColim.map f).app F =
      weightedColimObjObjι P₂ F (f.app _ x) :=
  colimit.ι_desc ..

@[reassoc (attr := simp)]
lemma weightedColim.ι_obj_map (P : Jᵒᵖ ⥤ Type w) {F₁ F₂ : J ⥤ C} (f : F₁ ⟶ F₂)
    {j : J} (x : P.obj (op j)) :
    weightedColimObjObjι P F₁ x ≫ ((weightedColim.obj P).map f) =
      f.app j ≫ weightedColimObjObjι P F₂ x :=
  ι_colimMap ..

@[reassoc (attr := simp)]
lemma weightedColimObjObj_w
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

@[no_expose]
noncomputable def isColimitWeightedColimCocone (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) :
    (weightedColimCocone P F).IsColimit :=
  colimit.isColimit _

@[ext]
lemma weightedColim.hom_ext {P : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {Z : C}
    {f g : (weightedColim.obj P).obj F ⟶ Z}
    (h : ∀ {j : J} (x : P.obj (op j)),
      weightedColimObjObjι P F x ≫ f = weightedColimObjObjι P F x ≫ g) :
    f = g :=
  (isColimitWeightedColimCocone P F).hom_ext h

@[no_expose]
noncomputable def WeightedCocone.IsColimit.iso
    {P : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {c : WeightedCocone P F}
    (hc : c.IsColimit) :
    (weightedColim.obj P).obj F ≅ c.pt :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc

@[reassoc (attr := simp)]
lemma WeightedCocone.IsColimit.ι_iso_hom
    {P : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {c : WeightedCocone P F}
    (hc : c.IsColimit) {j : J} (x : P.obj (op j)) :
    weightedColimObjObjι P F x ≫ hc.iso.hom = c.ι x :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) hc
    (op (Functor.elementsMk _ _ x))

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Pi.lift_π in
noncomputable def weightedColimHomEquiv {P : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {X : C} :
    ((weightedColim.obj P).obj F ⟶ X) ≃ (F ⟶ P.rightOp ⋙ piConst.obj X) where
  toFun x :=
    { app j := Pi.lift (fun y ↦ weightedColimObjObjι P F y ≫ x) }
  invFun f :=
    (isColimitWeightedColimCocone P F).desc (fun j y ↦ f.app j ≫ Pi.π _ y)
      (fun _ _ _ g ↦ by simp [dsimp% f.naturality_assoc g] )
  left_inv x := by
    ext j x
    dsimp
    simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
    apply WeightedCocone.IsColimit.fac
  right_inv f := by
    ext j
    dsimp
    ext x
    simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
    apply WeightedCocone.IsColimit.fac

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma ι_weightedColimHomEquiv_symm_apply {P : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {X : C}
    (f : F ⟶ P.rightOp ⋙ piConst.obj X) ⦃j : J⦄ (x : P.obj (op j)) :
    dsimp% weightedColimObjObjι P F x ≫ weightedColimHomEquiv.symm f =
      f.app j ≫ Pi.π _ x :=
  WeightedCocone.IsColimit.fac ..

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma weightedColimHomEquiv_apply_app_π {P : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {X : C}
    (x : (weightedColim.obj P).obj F ⟶ X) ⦃j : J⦄ (y : P.obj (op j)) :
    dsimp% (weightedColimHomEquiv x).app j ≫ Pi.π _ y =
      weightedColimObjObjι P F y ≫ x := by
  simp [weightedColimHomEquiv]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
noncomputable def weightedColimitAdj₂ :
    weightedColim.{w} (J := J) (C := C) ⊣₂ weightedColimRightAdj where
  adj P :=
    Adjunction.mkOfHomEquiv { homEquiv _ _ := weightedColimHomEquiv }

instance (X : C) {K : Type*} [Category* K] [HasColimitsOfShape K (Type w)] :
    PreservesLimitsOfShape Kᵒᵖ (weightedColimRightAdj.flip.obj X : (Jᵒᵖ ⥤ Type w)ᵒᵖ ⥤ J ⥤ C) := by
  refine ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨evaluationJointlyReflectsLimits _ (fun j ↦ ?_)⟩⟩⟩
  have : PreservesLimit F ((evaluation Jᵒᵖ (Type w)).obj (op j)).op := by
    apply preservesLimit_op
  exact isLimitOfPreserves (((evaluation Jᵒᵖ (Type w)).obj (op j)).op ⋙ piConst.obj X) hc

instance (F : J ⥤ C) {K : Type*} [Category* K] [HasColimitsOfShape K (Type w)] :
    PreservesColimitsOfShape K (weightedColim.flip.obj F : (Jᵒᵖ ⥤ Type w) ⥤ C) :=
  weightedColimitAdj₂.preservesColimitsOfShape_flip_obj _ _

end

section

variable {J' : Type*} [Category* J']

-- A.6 (iv)
@[simps!]
noncomputable def weightedColim₂ :
    (J' ⥤ Jᵒᵖ ⥤ Type w) ⥤ (J ⥤ C) ⥤ (J' ⥤ C) :=
  (weightedColim.{w}.flip ⋙ Functor.whiskeringRight _ _ _).flip

instance (P : J' ⥤ Jᵒᵖ ⥤ Type w) {K : Type*} [Category* K] [HasColimitsOfShape K C] :
    PreservesColimitsOfShape K ((weightedColim₂ (C := C)).obj P) where
  preservesColimit := ⟨fun hc ↦
    ⟨evaluationJointlyReflectsColimits _
      (fun j' ↦ isColimitOfPreserves ((weightedColim (C := C)).obj (P.obj j')) hc)⟩⟩

instance (F : J ⥤ C) {K : Type*} [Category* K] [HasProducts.{w} C]
    [HasColimitsOfShape K (Type w)] :
    PreservesColimitsOfShape K ((weightedColim₂ (J' := J')).flip.obj F) where
  preservesColimit := ⟨fun hc ↦ ⟨evaluationJointlyReflectsColimits _
    (fun j' ↦ (isColimitOfPreserves ((evaluation _ _ ).obj j' ⋙ weightedColim.flip.obj F) hc))⟩⟩

end

end

variable (C) in
set_option backward.defeqAttrib.useBackward true in
@[simps!]
noncomputable def weightColimObjYonedaObjIso [HasColimitsOfSize.{v, max u v} C] (j : J) :
    weightedColim.obj (yoneda.obj j) ≅ (evaluation J C).obj j :=
  NatIso.ofComponents (fun F ↦
    (WeightedCocone.isColimitYoneda F j).iso)

set_option backward.defeqAttrib.useBackward true in
variable (J C) in
@[simps!]
noncomputable def weightedColim₂ObjYonedaIso [HasColimitsOfSize.{v, max u v} C] :
    weightedColim₂.obj yoneda ≅ 𝟭 (J ⥤ C) :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents
    (fun j ↦ (WeightedCocone.isColimitYoneda F j).iso))

end CategoryTheory.Limits

/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nima Rasekh, Lyne Moser
-/
module

public import Mathlib.CategoryTheory.Functor.Trifunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Reedy.Adjunction.ParametrizedColimits
public import Reedy.Subfunctor.ExternalUnionProd
public import Reedy.Limits.Colim
public import Reedy.Limits.PiConst
public import Reedy.Limits.Op

/-!
# Weighted colimits

-/

@[expose] public section

universe w v'' v u'' u

namespace CategoryTheory.Limits

open Opposite

-- See A.6 in Riehl-Verity (here, we do not need the enriched version)

variable {J : Type u} [Category.{v} J] {C : Type*} [Category* C]

abbrev WeightedCocone (W : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) :=
  Cocone ((CategoryOfElements.π W).leftOp ⋙ F)

namespace WeightedCocone

variable {W : Jᵒᵖ ⥤ Type w} {F : J ⥤ C}

protected abbrev ι (c : WeightedCocone W F) {j : J} (x : W.obj (op j)) :
    F.obj j ⟶ c.pt :=
  (Cocone.ι c).app (op (Functor.elementsMk _ _ x))

variable (pt : C) (ι : ∀ ⦃j : J⦄ (_ : W.obj (op j)), F.obj j ⟶ pt)
  (hι : ∀ ⦃j₁ j₂ : J⦄ (x : W.obj (op j₁)) (f : j₂ ⟶ j₁),
    F.map f ≫ ι x = ι (W.map f.op x))
set_option backward.defeqAttrib.useBackward true in

@[simps pt]
def mk : WeightedCocone W F where
  pt := pt
  ι.app x := ι x.unop.2
  ι.naturality x₁ x₂ f := by simpa using hι (x₂.unop.2) f.unop.1.unop

@[simp]
lemma mk_ι {j : J} (x : W.obj (op j)) :
    (mk pt ι hι).ι x = ι x := rfl

protected abbrev IsColimit (c : WeightedCocone W F) := Limits.IsColimit c

namespace IsColimit

variable {c : WeightedCocone W F} (hc : c.IsColimit) {Z : C}

section

variable
  (ι : ∀ ⦃j : J⦄ (_ : W.obj (op j)), F.obj j ⟶ Z)
  (hι : ∀ ⦃j₁ j₂ : J⦄ (x : W.obj (op j₁)) (f : j₂ ⟶ j₁),
    F.map f ≫ ι x = ι (W.map f.op x))

def desc : c.pt ⟶ Z :=
  Limits.IsColimit.desc hc (WeightedCocone.mk Z ι hι)

@[reassoc (attr := simp)]
lemma fac {j : J} (x : W.obj (op j)) :
    c.ι x ≫ hc.desc ι hι = ι x :=
  Limits.IsColimit.fac hc (WeightedCocone.mk Z ι hι) (op (Functor.elementsMk _ _ x))

end

include hc in
lemma hom_ext {f g : c.pt ⟶ Z} (h : ∀ {j : J} (x : W.obj (op j)), c.ι x ≫ f = c.ι x ≫ g) :
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
  obj W := (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π W).leftOp ⋙ colim
  map {W₁ W₂} f :=
    Functor.whiskerLeft
      ((Functor.whiskeringLeft W₂.Elementsᵒᵖ J C).obj (CategoryOfElements.π W₂).leftOp)
        (colim.pre (NatTrans.mapElements f).op)
  map_id W := by
    ext F
    dsimp
    ext j
    rw [colimit.ι_pre]
    exact (Category.comp_id _).symm
  map_comp {W₁ W₂ W₃} f g := by
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
    (W : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) ⦃j : J⦄ (x : W.obj (op j)) :
    F.obj j ⟶ (weightedColim.obj W).obj F :=
  colimit.ι ((CategoryOfElements.π W).leftOp ⋙ F) (op (Functor.elementsMk _ _ x))

@[reassoc (attr := simp)]
lemma weightedColim.ι_map_app {W₁ W₂ : Jᵒᵖ ⥤ Type w} (f : W₁ ⟶ W₂) (F : J ⥤ C)
    {j : J} (x : W₁.obj (op j)) :
    weightedColimObjObjι W₁ F x ≫ (weightedColim.map f).app F =
      weightedColimObjObjι W₂ F (f.app _ x) :=
  colimit.ι_desc ..

@[reassoc (attr := simp)]
lemma weightedColim.ι_obj_map (W : Jᵒᵖ ⥤ Type w) {F₁ F₂ : J ⥤ C} (f : F₁ ⟶ F₂)
    {j : J} (x : W.obj (op j)) :
    weightedColimObjObjι W F₁ x ≫ ((weightedColim.obj W).map f) =
      f.app j ≫ weightedColimObjObjι W F₂ x :=
  ι_colimMap ..

@[reassoc (attr := simp)]
lemma weightedColimObjObj_w
    (W : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) ⦃j₁ j₂ : J⦄ (x : W.obj (op j₁))
    (f : j₂ ⟶ j₁) :
    F.map f ≫ weightedColimObjObjι W F x =
      weightedColimObjObjι W F (W.map f.op x) := by
  let g : Functor.elementsMk _ _ x ⟶ Functor.elementsMk _ _ (W.map f.op x) :=
    ⟨f.op, rfl⟩
  exact colimit.w ((CategoryOfElements.π W).leftOp ⋙ F) g.op

noncomputable abbrev weightedColimCocone (W : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) :
    WeightedCocone W F :=
  WeightedCocone.mk ((weightedColim.obj W).obj F)
    (fun j x ↦ weightedColimObjObjι W F x)
    (fun j₁ j₂ x f ↦ by simp)

@[no_expose]
noncomputable def isColimitWeightedColimCocone (W : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) :
    (weightedColimCocone W F).IsColimit :=
  colimit.isColimit _

@[ext]
lemma weightedColim.hom_ext {W : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {Z : C}
    {f g : (weightedColim.obj W).obj F ⟶ Z}
    (h : ∀ {j : J} (x : W.obj (op j)),
      weightedColimObjObjι W F x ≫ f = weightedColimObjObjι W F x ≫ g) :
    f = g :=
  (isColimitWeightedColimCocone W F).hom_ext h

@[no_expose]
noncomputable def WeightedCocone.IsColimit.iso
    {W : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {c : WeightedCocone W F}
    (hc : c.IsColimit) :
    (weightedColim.obj W).obj F ≅ c.pt :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc

@[reassoc (attr := simp)]
lemma ι_weightedColimCocone_desc {P : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {Z : C}
    (ι : ∀ ⦃j : J⦄ (_ : P.obj (op j)), F.obj j ⟶ Z)
    (hι : ∀ ⦃j₁ j₂ : J⦄ (x : P.obj (op j₁)) (f : j₂ ⟶ j₁),
      F.map f ≫ ι x = ι (P.map f.op x))
    {j : J} (x : P.obj (op j)) :
    weightedColimObjObjι P F x ≫ (isColimitWeightedColimCocone P F).desc ι hι = ι x :=
  WeightedCocone.IsColimit.fac ..

@[reassoc (attr := simp)]
lemma WeightedCocone.IsColimit.ι_iso_hom
    {W : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {c : WeightedCocone W F}
    (hc : c.IsColimit) {j : J} (x : W.obj (op j)) :
    weightedColimObjObjι W F x ≫ hc.iso.hom = c.ι x :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) hc
    (op (Functor.elementsMk _ _ x))

@[reassoc (attr := simp)]
lemma WeightedCocone.IsColimit.ι_iso_inv
    {W : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {c : WeightedCocone W F}
    (hc : c.IsColimit) {j : J} (x : W.obj (op j)) :
    c.ι x ≫ hc.iso.inv = weightedColimObjObjι W F x :=
  IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit _) hc
    (op (Functor.elementsMk _ _ x))

instance (W : Jᵒᵖ ⥤ Type w) {K : Type*} [Category* K] [HasColimitsOfShape K C] :
    PreservesColimitsOfShape K (weightedColim.obj W : (J ⥤ C) ⥤ C) where
  preservesColimit {G} := by dsimp [weightedColim]; infer_instance

section

variable [HasProducts.{w} C]

-- hopefully, this is the expect parametrized right adjoint to `weightedColim`
@[simps]
noncomputable def weightedColimRightAdj : (Jᵒᵖ ⥤ Type w)ᵒᵖ ⥤ C ⥤ (J ⥤ C) where
  obj W := piConst.{w} ⋙ (Functor.whiskeringLeft ..).obj W.unop.rightOp
  map {W₁ W₂} f := Functor.whiskerLeft _ ((Functor.whiskeringLeft ..).map f.unop.rightOp)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Pi.lift_π in
noncomputable def weightedColimHomEquiv {W : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {X : C} :
    ((weightedColim.obj W).obj F ⟶ X) ≃ (F ⟶ W.rightOp ⋙ piConst.obj X) where
  toFun x :=
    { app j := Pi.lift (fun y ↦ weightedColimObjObjι W F y ≫ x) }
  invFun f :=
    (isColimitWeightedColimCocone W F).desc (fun j y ↦ f.app j ≫ Pi.π _ y)
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
lemma ι_weightedColimHomEquiv_symm_apply {W : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {X : C}
    (f : F ⟶ W.rightOp ⋙ piConst.obj X) ⦃j : J⦄ (x : W.obj (op j)) :
    dsimp% weightedColimObjObjι W F x ≫ weightedColimHomEquiv.symm f =
      f.app j ≫ Pi.π _ x :=
  WeightedCocone.IsColimit.fac ..

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma weightedColimHomEquiv_apply_app_π {W : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {X : C}
    (x : (weightedColim.obj W).obj F ⟶ X) ⦃j : J⦄ (y : W.obj (op j)) :
    dsimp% (weightedColimHomEquiv x).app j ≫ Pi.π _ y =
      weightedColimObjObjι W F y ≫ x := by
  simp [weightedColimHomEquiv]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
noncomputable def weightedColimitAdj₂ :
    weightedColim.{w} (J := J) (C := C) ⊣₂ weightedColimRightAdj where
  adj W := Adjunction.mkOfHomEquiv { homEquiv _ _ := weightedColimHomEquiv }

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

noncomputable def bifunctorComp₁₂ProdWeightedColimIso [HasCoproducts.{w} C] :
    bifunctorComp₁₂
      (Functor.const Jᵒᵖ ⋙ (Functor.whiskeringRight₂ Jᵒᵖ _ _ _).obj TypeCat.prod.{w, w})
      (weightedColim.{w} (C := C)) ≅
    bifunctorComp₂₃ (sigmaConst.{w} (C := C)).flip weightedColim.{w} := by
  sorry

end

section

variable {J' : Type*} [Category* J']

-- A.6 (iv)
@[simps!]
noncomputable def weightedColim₂ :
    (J' ⥤ Jᵒᵖ ⥤ Type w) ⥤ (J ⥤ C) ⥤ (J' ⥤ C) :=
  (weightedColim.{w}.flip ⋙ Functor.whiskeringRight _ _ _).flip

instance (W : J' ⥤ Jᵒᵖ ⥤ Type w) {K : Type*} [Category* K] [HasColimitsOfShape K C] :
    PreservesColimitsOfShape K ((weightedColim₂ (C := C)).obj W) where
  preservesColimit := ⟨fun hc ↦
    ⟨evaluationJointlyReflectsColimits _
      (fun j' ↦ isColimitOfPreserves ((weightedColim (C := C)).obj (W.obj j')) hc)⟩⟩

instance [HasColimitsOfSize.{v'', u''} C] (W : J' ⥤ Jᵒᵖ ⥤ Type w) :
    PreservesColimitsOfSize.{v'', u''} ((weightedColim₂.{w} (J := J) (C := C)).obj W) where

instance (F : J ⥤ C) {K : Type*} [Category* K] [HasProducts.{w} C]
    [HasColimitsOfShape K (Type w)] :
    PreservesColimitsOfShape K ((weightedColim₂ (J' := J')).flip.obj F) where
  preservesColimit := ⟨fun hc ↦ ⟨evaluationJointlyReflectsColimits _
    (fun j' ↦ (isColimitOfPreserves ((evaluation _ _ ).obj j' ⋙ weightedColim.flip.obj F) hc))⟩⟩

instance {K : Type*} [Category* K] [HasProducts.{w} C] [HasColimitsOfShape K (Type w)] :
    PreservesColimitsOfShape K (weightedColim₂ (J' := J') (J := J) (C := C)) where
  preservesColimit := ⟨fun hc ↦
    ⟨evaluationJointlyReflectsColimits _
      (fun G ↦ isColimitOfPreserves (weightedColim₂.flip.obj G) hc)⟩⟩

instance [HasProducts.{w} C] [HasColimitsOfSize.{v'', u''} (Type w)] :
    PreservesColimitsOfSize.{v'', u''} (weightedColim₂ (J' := J') (J := J) (C := C)) where

variable [HasCoproducts.{w} C]

set_option backward.defeqAttrib.useBackward true in
noncomputable def bifunctorComp₁₂ExternalProductFunctorWeightedColim₂Iso :
    bifunctorComp₁₂
      FunctorToTypes.externalProductFunctor.{w, w}
        (weightedColim₂.{w} (J := J) (J' := J') (C := C)) ≅
    bifunctorComp₂₃
      (sigmaConst.{w} ⋙ Functor.whiskeringRight J' (Type w) C).flip weightedColim.{w} :=
  NatIso.ofComponents
    (fun W₁ ↦ NatIso.ofComponents
      (fun W₂ ↦ NatIso.ofComponents
        (fun F ↦ NatIso.ofComponents
          (fun j' ↦ ((bifunctorComp₁₂ProdWeightedColimIso.app (W₁.obj j')).app W₂).app F)
          (fun {j₁' j₂'} f ↦
            NatTrans.congr_app (NatTrans.congr_app
                ((bifunctorComp₁₂ProdWeightedColimIso.hom.naturality (W₁.map f))) W₂) F))
        (fun {F₁ F₂} f ↦ by
          ext j'
          exact ((bifunctorComp₁₂ProdWeightedColimIso.hom.app
            (W₁.obj j')).app W₂).naturality f))
      (fun {W₂ W₂'} f ↦ by
        ext F j'
        exact NatTrans.congr_app
          ((bifunctorComp₁₂ProdWeightedColimIso.hom.app (W₁.obj j')).naturality f) F))
    (fun {W₁ W₁'} f ↦ by
      ext W₂ F j'
      exact NatTrans.congr_app (NatTrans.congr_app
        (bifunctorComp₁₂ProdWeightedColimIso.hom.naturality (f.app j')) W₂) F)

end

end

variable (C) in
set_option backward.defeqAttrib.useBackward true in
@[simps!]
noncomputable def weightedColimObjYonedaObjIso [HasColimitsOfSize.{v, max u v} C] (j : J) :
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

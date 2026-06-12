/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Yun Liu
-/
module

public import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Reedy.Limits.Lim
public import Reedy.WeightedLimits.Colimits

/-!
# Weighted limits

-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory.Limits

open Opposite

variable {J' : Type u} [Category.{v} J'] {C : Type*} [Category* C]

abbrev WeightedCone (Q : J' ⥤ Type w) (F : J' ⥤ C) :=
  Cone (CategoryOfElements.π Q ⋙ F)

namespace WeightedCone

variable {Q : J' ⥤ Type w} {F : J' ⥤ C}

protected abbrev π (c : WeightedCone Q F) {j : J'} (x : Q.obj j) :
    c.pt ⟶ F.obj j :=
  (Cone.π c).app (Functor.elementsMk _ _ x)

variable (pt : C) (π : ∀ ⦃j : J'⦄ (_ : Q.obj j), pt ⟶ F.obj j)
  (hπ : ∀ ⦃j₁ j₂ : J'⦄ (x : Q.obj j₁) (f : j₁ ⟶ j₂),
    π x ≫ F.map f = π (Q.map f x))

set_option backward.defeqAttrib.useBackward true in
@[simps pt]
def mk : WeightedCone Q F where
  pt := pt
  π.app x := π x.2
  π.naturality x₁ x₂ f := by simpa using (hπ x₁.2 f.1).symm

@[simp]
lemma mk_π {j : J'} (x : Q.obj j) :
    (mk pt π hπ).π x = π x := rfl

protected abbrev IsLimit (c : WeightedCone Q F) := Limits.IsLimit c

namespace IsLimit

variable {c : WeightedCone Q F} (hc : c.IsLimit) {Z : C}

section

variable
  (π : ∀ ⦃j : J'⦄ (_ : Q.obj j), Z ⟶ F.obj j)
  (hπ : ∀ ⦃j₁ j₂ : J'⦄ (x : Q.obj j₁) (f : j₁ ⟶ j₂),
    π x ≫ F.map f = π (Q.map f x))

def lift : Z ⟶ c.pt :=
  Limits.IsLimit.lift hc (WeightedCone.mk Z π hπ)

@[reassoc (attr := simp)]
lemma fac {j : J'} (x : Q.obj j) :
    hc.lift π hπ ≫ c.π x = π x :=
  Limits.IsLimit.fac hc (WeightedCone.mk Z π hπ) (Functor.elementsMk _ _ x)

end

include hc in
lemma hom_ext {f g : Z ⟶ c.pt} (h : ∀ {j : J'} (x : Q.obj j), f ≫ c.π x = g ≫ c.π x) :
    f = g :=
  Limits.IsLimit.hom_ext hc (fun _ ↦ h _)

end IsLimit

set_option backward.defeqAttrib.useBackward true in
@[simps]
protected abbrev coyoneda (F : J' ⥤ C) (j : J') :
    WeightedCone (coyoneda.obj (op j)) F where
  pt := F.obj j
  π.app u := F.map u.2
  π.naturality _ _ f := by
    dsimp
    simp only [← Functor.map_comp, Category.id_comp]
    congr 1
    exact f.2.symm

set_option backward.defeqAttrib.useBackward true in
def isLimitCoyoneda (F : J' ⥤ C) (j : J') : (WeightedCone.coyoneda F j).IsLimit where
  lift s := WeightedCone.π s (𝟙 j)
  fac s x := by
    simpa using s.w (⟨x.2, Category.id_comp _⟩ : Functor.elementsMk _ j (𝟙 j) ⟶ x)
  uniq s m hm := by
    simpa using hm (Functor.elementsMk _ j (𝟙 j))

end WeightedCone

section

variable [HasLimitsOfSize.{v, max u w} C]

set_option backward.defeqAttrib.useBackward true in
@[no_expose]
noncomputable def weightedLim : (J' ⥤ Type w)ᵒᵖ ⥤ (J' ⥤ C) ⥤ C where
  obj Q := (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π Q.unop) ⋙ lim
  map {Q₁ Q₂} f :=
    Functor.whiskerLeft
      ((Functor.whiskeringLeft Q₁.unop.Elements J' C).obj (CategoryOfElements.π Q₁.unop))
        (lim.pre (NatTrans.mapElements f.unop))
  map_id Q := by
    ext F
    dsimp
    apply limit.hom_ext
    intro j
    rw [limit.pre_π]
    exact (Category.id_comp _).symm
  map_comp {Q₁ Q₂ Q₃} f g := by
    ext F
    dsimp
    apply limit.hom_ext
    intro j
    rw [limit.pre_π]
    dsimp only [limit.pre]
    erw [Category.assoc, limit.lift_π, limit.lift_π]
    rfl

@[no_expose]
noncomputable def weightedLimObjObjπ
    (Q : J' ⥤ Type w) (F : J' ⥤ C) ⦃j : J'⦄ (x : Q.obj j) :
    (weightedLim.obj (op Q)).obj F ⟶ F.obj j :=
  limit.π (CategoryOfElements.π Q ⋙ F) (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]
lemma weightedLim.map_app_π {Q₁ Q₂ : J' ⥤ Type w} (f : Q₁ ⟶ Q₂) (F : J' ⥤ C)
    {j : J'} (x : Q₁.obj j) :
    (weightedLim.map f.op).app F ≫ weightedLimObjObjπ Q₁ F x =
      weightedLimObjObjπ Q₂ F (f.app _ x) :=
  limit.pre_π ..

@[reassoc (attr := simp)]
lemma weightedLim.obj_map_π (Q : J' ⥤ Type w) {F₁ F₂ : J' ⥤ C} (f : F₁ ⟶ F₂)
    {j : J'} (x : Q.obj j) :
    ((weightedLim.obj (op Q)).map f) ≫ weightedLimObjObjπ Q F₂ x =
      weightedLimObjObjπ Q F₁ x ≫ f.app j :=
  limMap_π ..

@[reassoc (attr := simp)]
lemma weightedLimObjObj_w
    (Q : J' ⥤ Type w) (F : J' ⥤ C) ⦃j₁ j₂ : J'⦄ (x : Q.obj j₁)
    (f : j₁ ⟶ j₂) :
    weightedLimObjObjπ Q F x ≫ F.map f =
      weightedLimObjObjπ Q F (Q.map f x) := by
  let g : Functor.elementsMk _ _ x ⟶ Functor.elementsMk _ _ (Q.map f x) := ⟨f, rfl⟩
  exact limit.w (CategoryOfElements.π Q ⋙ F) g

noncomputable abbrev weightedLimCone (Q : J' ⥤ Type w) (F : J' ⥤ C) :
    WeightedCone Q F :=
  WeightedCone.mk ((weightedLim.obj (op Q)).obj F)
    (fun j x ↦ weightedLimObjObjπ Q F x)
    (fun j₁ j₂ x f ↦ by simp)

@[no_expose]
noncomputable def isLimitWeightedLimCone (Q : J' ⥤ Type w) (F : J' ⥤ C) :
    (weightedLimCone Q F).IsLimit :=
  limit.isLimit _

@[ext]
lemma weightedLim.hom_ext {Q : J' ⥤ Type w} {F : J' ⥤ C} {Z : C}
    {f g : Z ⟶ (weightedLim.obj (op Q)).obj F}
    (h : ∀ {j : J'} (x : Q.obj j),
      f ≫ weightedLimObjObjπ Q F x = g ≫ weightedLimObjObjπ Q F x) :
    f = g :=
  (isLimitWeightedLimCone Q F).hom_ext h

@[no_expose]
noncomputable def WeightedCone.IsLimit.iso
    {Q : J' ⥤ Type w} {F : J' ⥤ C} {c : WeightedCone Q F} (hc : c.IsLimit) :
    (weightedLim.obj (op Q)).obj F ≅ c.pt :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) hc

@[reassoc (attr := simp)]
lemma WeightedCone.IsLimit.iso_hom_π
    {Q : J' ⥤ Type w} {F : J' ⥤ C} {c : WeightedCone Q F}
    (hc : c.IsLimit) {j : J'} (x : Q.obj j) :
    hc.iso.hom ≫ c.π x = weightedLimObjObjπ Q F x :=
  IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) hc (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]
lemma WeightedCone.IsLimit.inv_π
    {Q : J' ⥤ Type w} {F : J' ⥤ C} {c : WeightedCone Q F}
    (hc : c.IsLimit) {j : J'} (x : Q.obj j) :
    hc.iso.inv ≫ weightedLimObjObjπ Q F x = c.π x := by
  rw [Iso.inv_comp_eq]
  exact (hc.iso_hom_π x).symm

instance (Q : (J' ⥤ Type w)ᵒᵖ) {K : Type*} [Category* K] [HasLimitsOfShape K C] :
    PreservesLimitsOfShape K (weightedLim.obj Q : (J' ⥤ C) ⥤ C) where
  preservesLimit {G} := by dsimp [weightedLim]; infer_instance

section

variable [HasCoproducts.{w} C]

@[simps]
noncomputable def weightedLimLeftAdj : (J' ⥤ Type w) ⥤ C ⥤ (J' ⥤ C) where
  obj Q := sigmaConst.{w} ⋙ (Functor.whiskeringLeft ..).obj Q
  map {Q₁ Q₂} f := Functor.whiskerLeft _ ((Functor.whiskeringLeft ..).map f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Sigma.ι_desc in
noncomputable def weightedLimHomEquiv {Q : J' ⥤ Type w} {X : C} {F : J' ⥤ C} :
    ((weightedLimLeftAdj.obj Q).obj X ⟶ F) ≃ (X ⟶ (weightedLim.obj (op Q)).obj F) where
  toFun f :=
    (isLimitWeightedLimCone Q F).lift
      (fun j y ↦ Sigma.ι (fun (_ : Q.obj j) ↦ X) y ≫ f.app j)
      (fun _ _ y g ↦ by
        erw [Category.assoc, ← f.naturality g, ← Category.assoc]
        dsimp [weightedLimLeftAdj]
        simp)
  invFun x := { app j := Sigma.desc (fun y ↦ x ≫ weightedLimObjObjπ Q F y) }
  left_inv f := by
    ext j
    dsimp [weightedLimLeftAdj]
    ext y
    erw [Sigma.ι_desc]
    apply WeightedCone.IsLimit.fac
  right_inv x := by
    ext j y
    dsimp
    simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    apply WeightedCone.IsLimit.fac

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma weightedLimHomEquiv_apply_π {Q : J' ⥤ Type w} {X : C} {F : J' ⥤ C}
    (f : (weightedLimLeftAdj.obj Q).obj X ⟶ F) ⦃j : J'⦄ (y : Q.obj j) :
    dsimp% weightedLimHomEquiv f ≫ weightedLimObjObjπ Q F y =
      Sigma.ι (fun _ : Q.obj j ↦ X) y ≫ f.app j :=
  WeightedCone.IsLimit.fac ..

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma ι_weightedLimHomEquiv_symm_apply_app {Q : J' ⥤ Type w} {X : C} {F : J' ⥤ C}
    (x : X ⟶ (weightedLim.obj (op Q)).obj F) ⦃j : J'⦄ (y : Q.obj j) :
    dsimp% Sigma.ι (fun _ : Q.obj j ↦ X) y ≫ (weightedLimHomEquiv.symm x).app j =
      x ≫ weightedLimObjObjπ Q F y := by
  simp [weightedLimHomEquiv]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
noncomputable def weightedLimAdj₂ :
    weightedLimLeftAdj.{w} (J' := J') (C := C) ⊣₂ weightedLim where
  adj Q := Adjunction.mkOfHomEquiv { homEquiv _ _ := weightedLimHomEquiv }

instance (X : C) {K : Type*} [Category* K] [HasColimitsOfShape K (Type w)] :
    PreservesColimitsOfShape K (weightedLimLeftAdj.flip.obj X : (J' ⥤ Type w) ⥤ J' ⥤ C) := by
  refine ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨evaluationJointlyReflectsColimits _ (fun j ↦ ?_)⟩⟩⟩
  exact isColimitOfPreserves (((evaluation J' (Type w)).obj j) ⋙ sigmaConst.obj X) hc

instance (F : J' ⥤ C) {K : Type*} [Category* K] [HasColimitsOfShape K (Type w)] :
    PreservesLimitsOfShape Kᵒᵖ (weightedLim.flip.obj F : (J' ⥤ Type w)ᵒᵖ ⥤ C) :=
  weightedLimAdj₂.preservesLimitsOfShape_flip_obj _ _

end

section

variable {J : Type u'} [Category.{v'} J]

-- A.6 (iv)
set_option backward.defeqAttrib.useBackward true in
@[simps!]
noncomputable def weightedLim₂ :
    (J' ⥤ Jᵒᵖ ⥤ Type w)ᵒᵖ ⥤ (J' ⥤ C) ⥤ (J ⥤ C) :=
  (flipFunctor J' Jᵒᵖ (Type w)).op ⋙
    Functor.opHom _ _ ⋙
    (Functor.whiskeringLeft J Jᵒᵖᵒᵖ ((J' ⥤ Type w)ᵒᵖ)).obj (opOp J) ⋙
    Functor.whiskeringLeft J ((J' ⥤ Type w)ᵒᵖ) C ⋙
    (Functor.whiskeringLeft (J' ⥤ C) (((J' ⥤ Type w)ᵒᵖ) ⥤ C) (J ⥤ C)).obj weightedLim.flip

instance (P : (J' ⥤ Jᵒᵖ ⥤ Type w)ᵒᵖ) {K : Type*} [Category* K] [HasLimitsOfShape K C] :
    PreservesLimitsOfShape K ((weightedLim₂ (C := C)).obj P) where
  preservesLimit := ⟨fun hc ↦
    ⟨evaluationJointlyReflectsLimits _
      (fun j ↦ isLimitOfPreserves
        ((weightedLim (C := C)).obj (op (P.unop.flip.obj (op j)))) hc)⟩⟩

instance (G : J' ⥤ C) {K : Type*} [Category* K] [HasCoproducts.{w} C]
    [HasColimitsOfShape K (Type w)] :
    PreservesLimitsOfShape Kᵒᵖ ((weightedLim₂ (J := J) (C := C)).flip.obj G) := by
  refine ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨evaluationJointlyReflectsLimits _ (fun j ↦ ?_)⟩⟩⟩
  have : PreservesLimit F
      (((Functor.whiskeringRight J' (Jᵒᵖ ⥤ Type w) (Type w)).obj
        ((evaluation Jᵒᵖ (Type w)).obj (op j))).op) := by
    apply preservesLimit_op
  exact isLimitOfPreserves
    ((((Functor.whiskeringRight J' (Jᵒᵖ ⥤ Type w) (Type w)).obj
        ((evaluation Jᵒᵖ (Type w)).obj (op j))).op) ⋙ weightedLim.flip.obj G) hc

end

end

variable (C) in
set_option backward.defeqAttrib.useBackward true in
@[simps!]
noncomputable def weightedLimObjCoyonedaObjIso [HasLimitsOfSize.{v, max u v} C] (j' : J') :
    weightedLim.obj (op (coyoneda.obj (op j'))) ≅ (evaluation J' C).obj j' :=
  NatIso.ofComponents (fun F ↦ (WeightedCone.isLimitCoyoneda F j').iso)
    (fun {F G} f ↦ by
      dsimp
      apply (cancel_mono (WeightedCone.isLimitCoyoneda G j').iso.inv).mp
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      apply weightedLim.hom_ext
      intro j x
      simp only [weightedLim.obj_map_π, Category.assoc]
      erw [WeightedCone.IsLimit.inv_π, ← f.naturality x, ← Category.assoc,
        WeightedCone.IsLimit.iso_hom_π])

set_option backward.defeqAttrib.useBackward true in
variable (J' C) in
@[simps!]
noncomputable def weightedLim₂ObjYonedaIso [HasLimitsOfSize.{v, max u v} C] :
    𝟭 (J' ⥤ C) ≅ weightedLim₂.obj (op yoneda) :=
  NatIso.ofComponents (fun G ↦ NatIso.ofComponents
    (fun j ↦ (WeightedCone.isLimitCoyoneda G j).iso.symm))

section

variable {J : Type u'} [Category.{v'} J]
variable [HasLimitsOfSize.{v, max u w} C] [HasColimitsOfSize.{v', max u' w} C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
noncomputable def weightedLim₂HomEquiv
    {P : J' ⥤ Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {G : J' ⥤ C} :
    ((weightedColim₂.obj P).obj F ⟶ G) ≃ (F ⟶ (weightedLim₂.obj (op P)).obj G) where
  toFun φ :=
    { app j := (isLimitWeightedLimCone (P.flip.obj (op j)) G).lift
        (fun j' x ↦ weightedColimObjObjι (P.obj j') F x ≫ φ.app j')
        (fun _ _ x g ↦ by
          have h := φ.naturality g
          dsimp [weightedColim₂] at h
          erw [Category.assoc, ← h, ← Category.assoc, weightedColim.ι_map_app]
          rfl)
      naturality _ _ h := by
        apply weightedLim.hom_ext
        intro j' x
        dsimp [weightedLim₂]
        erw [Category.assoc, Category.assoc, weightedLim.map_app_π,
          WeightedCone.IsLimit.fac, WeightedCone.IsLimit.fac,
          weightedColimObjObj_w_assoc]
        rfl
    }
  invFun ψ :=
    { app j' := (isColimitWeightedColimCocone (P.obj j') F).desc
        (fun j x ↦ ψ.app j ≫ weightedLimObjObjπ (P.flip.obj (op j)) G x)
        (fun _ _ x h ↦ by
          have g := ψ.naturality h
          dsimp [weightedLim₂] at g
          erw [reassoc_of% g, weightedLim.map_app_π]
          rfl)
      naturality _ _ g := by
        apply weightedColim.hom_ext
        intro j x
        dsimp [weightedLim₂]
        simp
    }
  left_inv φ := by
    ext j'
    apply weightedColim.hom_ext
    intro j x
    erw [ι_weightedColimCocone_desc]
    exact WeightedCone.IsLimit.fac ..
  right_inv ψ := by
    ext j
    apply weightedLim.hom_ext
    intro j' x
    erw [WeightedCone.IsLimit.fac]
    exact ι_weightedColimCocone_desc ..

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma weightedLim₂HomEquiv_apply_app_π {P : J' ⥤ Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {G : J' ⥤ C}
    (φ : (weightedColim₂.obj P).obj F ⟶ G) {j : J} ⦃j' : J'⦄ (x : (P.obj j').obj (op j)) :
    dsimp% (weightedLim₂HomEquiv φ).app j ≫ weightedLimObjObjπ (P.flip.obj (op j)) G x =
      weightedColimObjObjι (P.obj j') F x ≫ φ.app j' :=
  WeightedCone.IsLimit.fac ..

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma ι_weightedLim₂HomEquiv_symm_app {P : J' ⥤ Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {G : J' ⥤ C}
    (ψ : F ⟶ (weightedLim₂.obj (op P)).obj G) ⦃j' : J'⦄ {j : J} (x : (P.obj j').obj (op j)) :
    dsimp% weightedColimObjObjι (P.obj j') F x ≫ (weightedLim₂HomEquiv.symm ψ).app j' =
      ψ.app j ≫ weightedLimObjObjπ (P.flip.obj (op j)) G x :=
  ι_weightedColimCocone_desc ..

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
noncomputable def weightedLim₂Adj₂ :
    weightedColim₂.{w} (J := J) (J' := J') (C := C) ⊣₂ weightedLim₂ where
  adj P := Adjunction.mkOfHomEquiv { homEquiv _ _ := weightedLim₂HomEquiv }

end

end CategoryTheory.Limits

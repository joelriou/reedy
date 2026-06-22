/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Trifunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Reedy.Limits.TriplePushouts

/-!
# ...

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C₁ C₂ C₃ C₁₂ C₂₃ D : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₁₂] [Category* C₂₃] [Category* D]

namespace Functor

section

variable (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ D)
  {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁)
  {X₂ Y₂ : C₂} (f₂ : X₂ ⟶ Y₂)
  {X₃ Y₃ : C₃} (f₃ : X₃ ⟶ Y₃)

structure PushoutObjObjObj where
  pt : D
  ι₁ : ((F.obj X₁).obj Y₂).obj Y₃ ⟶ pt
  ι₂ : ((F.obj Y₁).obj X₂).obj Y₃ ⟶ pt
  ι₃ : ((F.obj Y₁).obj Y₂).obj X₃ ⟶ pt
  isPushout₃ : IsPushout₃
      (((F.obj Y₁).obj X₂).map f₃) (((F.obj Y₁).map f₂).app X₃)
      (((F.obj X₁).obj Y₂).map f₃) (((F.map f₁).app Y₂).app X₃)
      (((F.obj X₁).map f₂).app Y₃) (((F.map f₁).app X₂).app Y₃)
      ι₁ ι₂ ι₃
  ι : pt ⟶ ((F.obj Y₁).obj Y₂).obj Y₃ :=
    isPushout₃.desc (((F.map f₁).app Y₂).app Y₃) (((F.obj Y₁).map f₂).app Y₃)
      (((F.obj Y₁).obj Y₂).map f₃)
  ι₁_ι : ι₁ ≫ ι = ((F.map f₁).app Y₂).app Y₃ := by cat_disch
  ι₂_ι : ι₂ ≫ ι = ((F.obj Y₁).map f₂).app Y₃ := by cat_disch
  ι₃_ι : ι₃ ≫ ι = ((F.obj Y₁).obj Y₂).map f₃ := by cat_disch

namespace PushoutObjObjObj

variable {F f₁ f₂ f₃} (sq₃ : PushoutObjObjObj F f₁ f₂ f₃)

attribute [reassoc (attr := simp)] ι₁_ι ι₂_ι ι₃_ι

section

variable (sq₃' : PushoutObjObjObj F f₁ f₂ f₃)

noncomputable def ptUniqueUpToIso : sq₃.pt ≅ sq₃'.pt :=
  IsColimit.coconePointUniqueUpToIso sq₃.isPushout₃.isColimit sq₃'.isPushout₃.isColimit

@[reassoc (attr := simp)]
lemma ι₁_ptUniqueUpToIso_hom : sq₃.ι₁ ≫ (ptUniqueUpToIso sq₃ sq₃').hom = sq₃'.ι₁ :=
  IsColimit.comp_coconePointUniqueUpToIso_hom sq₃.isPushout₃.isColimit
    sq₃'.isPushout₃.isColimit (.right (0 : Fin 3))

@[reassoc (attr := simp)]
lemma ι₂_ptUniqueUpToIso_hom : sq₃.ι₂ ≫ (ptUniqueUpToIso sq₃ sq₃').hom = sq₃'.ι₂ :=
  IsColimit.comp_coconePointUniqueUpToIso_hom sq₃.isPushout₃.isColimit
    sq₃'.isPushout₃.isColimit (.right (1 : Fin 3))

@[reassoc (attr := simp)]
lemma ι₃_ptUniqueUpToIso_hom : sq₃.ι₃ ≫ (ptUniqueUpToIso sq₃ sq₃').hom = sq₃'.ι₃ :=
  IsColimit.comp_coconePointUniqueUpToIso_hom sq₃.isPushout₃.isColimit
    sq₃'.isPushout₃.isColimit (.right (2 : Fin 3))

@[reassoc (attr := simp)]
lemma ι₁_ptUniqueUpToIso_inv : sq₃'.ι₁ ≫ (ptUniqueUpToIso sq₃ sq₃').inv = sq₃.ι₁ :=
  IsColimit.comp_coconePointUniqueUpToIso_inv sq₃.isPushout₃.isColimit
    sq₃'.isPushout₃.isColimit (.right (0 : Fin 3))

@[reassoc (attr := simp)]
lemma ι₂_ptUniqueUpToIso_inv : sq₃'.ι₂ ≫ (ptUniqueUpToIso sq₃ sq₃').inv = sq₃.ι₂ :=
  IsColimit.comp_coconePointUniqueUpToIso_inv sq₃.isPushout₃.isColimit
    sq₃'.isPushout₃.isColimit (.right (1 : Fin 3))

@[reassoc (attr := simp)]
lemma ι₃_ptUniqueUpToIso_inv : sq₃'.ι₃ ≫ (ptUniqueUpToIso sq₃ sq₃').inv = sq₃.ι₃ :=
  IsColimit.comp_coconePointUniqueUpToIso_inv sq₃.isPushout₃.isColimit
    sq₃'.isPushout₃.isColimit (.right (2 : Fin 3))

@[reassoc (attr := simp)]
lemma ptUniqueUpToIso_hom_ι : (sq₃.ptUniqueUpToIso sq₃').hom ≫ sq₃'.ι = sq₃.ι := by
  apply sq₃.isPushout₃.hom_ext <;> simp

@[reassoc (attr := simp)]
lemma ptUniqueUpToIso_inv_ι : (sq₃.ptUniqueUpToIso sq₃').inv ≫ sq₃.ι = sq₃'.ι := by
  apply sq₃'.isPushout₃.hom_ext <;> simp

set_option backward.defeqAttrib.useBackward true in
noncomputable abbrev arrowUnique : Arrow.mk sq₃.ι ≅ Arrow.mk sq₃'.ι :=
  Arrow.isoMk (sq₃.ptUniqueUpToIso sq₃') (Iso.refl _)

end

section

variable {F' : C₁ ⥤ C₂ ⥤ C₃ ⥤ D} (e : F ≅ F')

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Multicofork.π in
/-- Transport a `Functor.PushoutObjObjObjObj` structure via a natural isomorphism of functors. -/
@[simps]
def ofNatIso : F'.PushoutObjObjObj f₁ f₂ f₃ where
  pt := sq₃.pt
  ι₁ := ((e.inv.app X₁).app Y₂).app Y₃ ≫ sq₃.ι₁
  ι₂ := ((e.inv.app Y₁).app X₂).app Y₃ ≫ sq₃.ι₂
  ι₃ := ((e.inv.app Y₁).app Y₂).app X₃ ≫ sq₃.ι₃
  isPushout₃.w₀ := by simp [sq₃.isPushout₃.w₀]
  isPushout₃.w₁ := by
    simp [sq₃.isPushout₃.w₁,
      reassoc_of% dsimp% NatTrans.congr_app (NatTrans.congr_app (e.inv.naturality f₁) Y₂) X₃]
  isPushout₃.w₂ := by
    simp [sq₃.isPushout₃.w₂,
      reassoc_of% dsimp% NatTrans.congr_app (NatTrans.congr_app (e.inv.naturality f₁) X₂) Y₃]
  isPushout₃.nonempty_isColimit :=
    ⟨IsColimit.equivOfNatIsoOfIso
      (MultispanIndex.pushout₃MultispanExt
      (((e.app _).app _).app _) (((e.app _).app _).app _) (((e.app _).app _).app _)
      (((e.app _).app _).app _) (((e.app _).app _).app _) (((e.app _).app _).app _)
      (by simp) (by simp) (by simp) (by simp)
      (NatTrans.congr_app (NatTrans.congr_app (e.hom.naturality f₁) _) _)
      (NatTrans.congr_app (NatTrans.congr_app (e.hom.naturality f₁) _) _)) _ _
        (by exact PushoutCocone₃.ext (Iso.refl _)) sq₃.isPushout₃.isColimit⟩
  ι := sq₃.ι ≫ ((e.hom.app _).app _).app _
  ι₁_ι := by simp [← NatTrans.comp_app]

end

end PushoutObjObjObj

end

set_option backward.defeqAttrib.useBackward true in
@[simps]
def PushoutObjObj.bifunctorComp₁₂
    {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ D}
    {X₁ Y₁ : C₁} {f₁ : X₁ ⟶ Y₁} {X₂ Y₂ : C₂} {f₂ : X₂ ⟶ Y₂}
    (sq₁₂ : F₁₂.PushoutObjObj f₁ f₂)
    {X₃ Y₃ : C₃} {f₃ : X₃ ⟶ Y₃}
    [PreservesColimit (span ((F₁₂.map f₁).app X₂) ((F₁₂.obj X₁).map f₂)) (G.flip.obj X₃)]
    [PreservesColimit (span ((F₁₂.map f₁).app X₂) ((F₁₂.obj X₁).map f₂)) (G.flip.obj Y₃)]
    (sq : G.PushoutObjObj sq₁₂.ι f₃) :
    (bifunctorComp₁₂ F₁₂ G).PushoutObjObjObj f₁ f₂ f₃ where
  pt := sq.pt
  ι₁ := (G.map sq₁₂.inr).app Y₃ ≫ sq.inr
  ι₂ := (G.map sq₁₂.inl).app Y₃ ≫ sq.inr
  ι₃ := sq.inl
  isPushout₃.w₀ := by
    dsimp
    rw [NatTrans.naturality_assoc, ← sq.isPushout.w,
      ← NatTrans.comp_app_assoc, ← G.map_comp, sq₁₂.inl_ι]
  isPushout₃.w₁ := by
    dsimp
    rw [NatTrans.naturality_assoc, ← sq.isPushout.w,
      ← NatTrans.comp_app_assoc, ← G.map_comp, sq₁₂.inr_ι]
  isPushout₃.w₂ := by
    dsimp
    simp only [← NatTrans.comp_app_assoc, ← G.map_comp, sq₁₂.isPushout.w]
  isPushout₃.nonempty_isColimit := by
    refine ⟨PushoutCocone₃.IsColimit.mk (fun T f g h₀ h₁ h₂ ↦ ?_)
      (fun T p₀ p₁ p₂ h₀ h₁ h₂ ↦ ?_)⟩
    · exact sq.hom_ext h₂
        ((sq₁₂.isPushout.map (G.flip.obj Y₃)).hom_ext
          (by simpa using h₁) (by simpa using h₀))
    · dsimp at p₀ p₁ p₂ h₀ h₁ h₂ ⊢
      obtain ⟨p, hp₁, hp₀⟩ := (sq₁₂.isPushout.map (G.flip.obj Y₃)).exists_desc p₁ p₀ h₂.symm
      dsimp at hp₁ hp₀
      obtain ⟨l, hl₁, hl₂⟩ := sq.isPushout.exists_desc p₂ p (by
        apply (sq₁₂.isPushout.map (G.flip.obj X₃)).hom_ext
        · dsimp
          rw [← NatTrans.comp_app_assoc, ← G.map_comp, sq₁₂.inl_ι, ← h₀,
            ← NatTrans.naturality_assoc, hp₁]
        · dsimp
          rw [← NatTrans.comp_app_assoc, ← G.map_comp, sq₁₂.inr_ι, ← h₁,
            ← NatTrans.naturality_assoc, hp₀])
      exact ⟨l, by simp [hl₂, hp₀], by simp [hl₂, hp₁], hl₁⟩
  ι := sq.ι
  ι₁_ι := by simp [← NatTrans.comp_app, ← Functor.map_comp]
  ι₂_ι := by simp [← NatTrans.comp_app, ← Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
@[simps]
def PushoutObjObj.bifunctorComp₂₃
    {F : C₁ ⥤ C₂₃ ⥤ D} {G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃}
    {X₂ Y₂ : C₂} {f₂ : X₂ ⟶ Y₂}
    {X₃ Y₃ : C₃} {f₃ : X₃ ⟶ Y₃}
    (sq₂₃ : G₂₃.PushoutObjObj f₂ f₃)
    {X₁ Y₁ : C₁} {f₁ : X₁ ⟶ Y₁}
    [PreservesColimit (span ((G₂₃.map f₂).app X₃) ((G₂₃.obj X₂).map f₃)) (F.obj X₁)]
    [PreservesColimit (span ((G₂₃.map f₂).app X₃) ((G₂₃.obj X₂).map f₃)) (F.obj Y₁)]
    (sq : F.PushoutObjObj f₁ sq₂₃.ι) :
    (bifunctorComp₂₃ F G₂₃).PushoutObjObjObj f₁ f₂ f₃ where
  pt := sq.pt
  ι₁ := sq.inr
  ι₂ := (F.obj Y₁).map sq₂₃.inr ≫ sq.inl
  ι₃ := (F.obj Y₁).map sq₂₃.inl ≫ sq.inl
  isPushout₃.w₀ := by
    dsimp
    simp only [← Functor.map_comp_assoc, sq₂₃.isPushout.w]
  isPushout₃.w₁ := by
    dsimp
    rw [← NatTrans.naturality_assoc, sq.isPushout.w,
      ← Functor.map_comp_assoc, inl_ι]
  isPushout₃.w₂ := by
    dsimp
    rw [← NatTrans.naturality_assoc, sq.isPushout.w,
      ← Functor.map_comp_assoc, inr_ι]
  isPushout₃.nonempty_isColimit := by
    refine ⟨PushoutCocone₃.IsColimit.mk (fun T f g h₀ h₁ h₂ ↦ ?_)
      (fun T p₀ p₁ p₂ h₀ h₁ h₂ ↦ ?_)⟩
    · exact sq.hom_ext
        ((sq₂₃.isPushout.map (F.obj Y₁)).hom_ext
          (by simpa using h₂) (by simpa using h₁)) h₀
    · dsimp at p₀ p₁ p₂ h₀ h₁ h₂ ⊢
      obtain ⟨p, hp₂, hp₁⟩ := (sq₂₃.isPushout.map (F.obj Y₁)).exists_desc p₂ p₁ h₀.symm
      obtain ⟨l, hl₁, hl₂⟩ := sq.isPushout.exists_desc p p₀ (by
        apply (sq₂₃.isPushout.map (F.obj X₁)).hom_ext
        · rw [NatTrans.naturality_assoc, hp₂,
            ← Functor.map_comp_assoc, inl_ι, h₁]
        · rw [NatTrans.naturality_assoc, hp₁,
            ← Functor.map_comp_assoc, inr_ι, h₂])
      exact ⟨l, hl₂, by simp [hl₁, hp₁], by simp [hl₁, hp₂]⟩
  ι := sq.ι
  ι₂_ι := by simp [← Functor.map_comp]
  ι₃_ι := by simp [← Functor.map_comp]

end Functor

end CategoryTheory

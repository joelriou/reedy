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

namespace PushoutObjObjObj

variable {F f₁ f₂ f₃} (sq₃ : PushoutObjObjObj F f₁ f₂ f₃)

@[no_expose]
noncomputable def ι : sq₃.pt ⟶ ((F.obj Y₁).obj Y₂).obj Y₃ :=
  sq₃.isPushout₃.desc (((F.map f₁).app Y₂).app Y₃) (((F.obj Y₁).map f₂).app Y₃)
    (((F.obj Y₁).obj Y₂).map f₃)

@[reassoc (attr := simp)]
lemma ι₁_ι : sq₃.ι₁ ≫ sq₃.ι = ((F.map f₁).app Y₂).app Y₃ := by simp [ι]

@[reassoc (attr := simp)]
lemma ι₂_ι : sq₃.ι₂ ≫ sq₃.ι = ((F.obj Y₁).map f₂).app Y₃ := by simp [ι]

@[reassoc (attr := simp)]
lemma ι₃_ι : sq₃.ι₃ ≫ sq₃.ι = ((F.obj Y₁).obj Y₂).map f₃ := by simp [ι]

end PushoutObjObjObj
end

variable {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ D}
  {X₁ Y₁ : C₁} {f₁ : X₁ ⟶ Y₁}
  {X₂ Y₂ : C₂} {f₂ : X₂ ⟶ Y₂}
  (sq₁₂ : F₁₂.PushoutObjObj f₁ f₂)
  {X₃ Y₃ : C₃} {f₃ : X₃ ⟶ Y₃}
  (sq : G.PushoutObjObj sq₁₂.ι f₃)

set_option backward.defeqAttrib.useBackward true in
-- add assumption about preservation of pushouts
def PushoutObjObj.bifunctorComp₁₂ :
    (bifunctorComp₁₂ F₁₂ G).PushoutObjObjObj f₁ f₂ f₃ where
  pt := sq.pt
  ι₁ := (G.map sq₁₂.inr).app Y₃ ≫ sq.inr
  ι₂ := (G.map sq₁₂.inl).app Y₃ ≫ sq.inr
  ι₃ := sq.inl
  isPushout₃ := by
    dsimp
    sorry

end Functor

end CategoryTheory

/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# ...

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] {X₀ : C}

variable (X₀) in
abbrev ArrowLeftOver := CostructuredArrow Arrow.leftFunc X₀

namespace ArrowLeftOver

variable (X₀) in
abbrev forget : ArrowLeftOver X₀ ⥤ Arrow C := CostructuredArrow.proj _ _

abbrev mk {X Y : C} (f : X ⟶ Y) (g : X ⟶ X₀) : ArrowLeftOver X₀ :=
  CostructuredArrow.mk (Y := Arrow.mk f) g

section

variable (E : ArrowLeftOver X₀)

abbrev leftObj : C :=
  (CostructuredArrow.left E).left

abbrev rightObj : C :=
  (CostructuredArrow.left E).right

abbrev top : E.leftObj ⟶ E.rightObj :=
  (CostructuredArrow.left E).hom

abbrev hom : E.leftObj ⟶ X₀ := CostructuredArrow.hom E

end

section

variable {E F : ArrowLeftOver X₀}

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
abbrev homMk (left : E.leftObj ⟶ F.leftObj)
    (right : E.rightObj ⟶ F.rightObj)
    (w : left ≫ F.top = E.top ≫ right := by cat_disch)
    (w' : left ≫ F.hom = E.hom := by cat_disch) : E ⟶ F :=
  CostructuredArrow.homMk (Arrow.homMk left right w) w'

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma w (f : E ⟶ F) : f.left.left ≫ F.hom = E.hom := by simpa using f.w

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[simps]
noncomputable def pushoutFunctor [HasPushouts C] :
    ArrowLeftOver X₀ ⥤ Under X₀ where
  obj E := Under.mk (pushout.inr E.top E.hom)
  map {E₁ E₂} f :=
    Under.homMk
      (pushout.map _ _ _ _ f.left.right (𝟙 X₀) f.left.left (by simp)
        (by simp)) (by simp)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[simps]
def pushoutFunctorRightAdjoint :
    Under X₀ ⥤ ArrowLeftOver X₀ where
  obj X := ArrowLeftOver.mk X.hom (𝟙 X₀)
  map f := homMk (𝟙 _) f.right (by simp [mk, top]) (by simp)
  map_comp f g := by
    ext
    · simp [mk, leftObj]
    · simp

variable [HasPushouts C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
noncomputable def pushoutFunctorHomEquiv (E : ArrowLeftOver X₀) (Y : Under X₀) :
    (pushoutFunctor.obj E ⟶ Y) ≃ (E ⟶ pushoutFunctorRightAdjoint.obj Y) where
  toFun f := homMk E.hom (pushout.inl _ _ ≫ f.right) (by
    simp [pushout.condition_assoc, dsimp% Under.w f, mk, top])
      (Category.comp_id _)
  invFun g :=
    Under.homMk (pushout.desc g.left.right Y.hom (by simp [← w g]))
  left_inv f := by
    ext
    dsimp
    ext
    · simp
    · simp [← Under.w f]
  right_inv g := by
    ext
    · simp [← w g]
    · simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
noncomputable def pushoutFunctorAdj :
    pushoutFunctor (X₀ := X₀) ⊣ pushoutFunctorRightAdjoint :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pushoutFunctorHomEquiv
      homEquiv_naturality_left_symm f g := by
        ext
        dsimp
        ext <;> simp [pushoutFunctorHomEquiv]
      homEquiv_naturality_right f g := by
        ext
        · simp [pushoutFunctorHomEquiv, mk, leftObj]
        · simp [pushoutFunctorHomEquiv] }

instance : (pushoutFunctor (X₀ := X₀)).IsLeftAdjoint :=
  pushoutFunctorAdj.isLeftAdjoint

end ArrowLeftOver

end CategoryTheory

/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic

/-!
#

-/

@[expose] public section

universe w

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C D : Type*} [Category* C] [Category* D]

-- this is from https://github.com/joelriou/topcat-model-category/blob/master/TopCatModelCategory/AttachCells.lean
namespace AttachCells

variable {α : Type*} {A B : α → C} {g : ∀ a, A a ⟶ B a}
  {X Y : C} {f : X ⟶ Y} (hf : AttachCells g f) (F : C ⥤ D)
  [PreservesColimit (Discrete.functor (fun i ↦ A (hf.π i))) F]
  [PreservesColimit (Discrete.functor (fun i ↦ B (hf.π i))) F]
  [PreservesColimit (span hf.g₁ hf.m) F]

set_option backward.defeqAttrib.useBackward true in
@[simps]
noncomputable def map : AttachCells (g := fun a ↦ F.map (g a)) (F.map f) where
  ι := hf.ι
  π := hf.π
  cofan₁ := Cofan.mk _ (fun i ↦ F.map (hf.cofan₁.inj i))
  cofan₂ := Cofan.mk _ (fun i ↦ F.map (hf.cofan₂.inj i))
  isColimit₁ := (isColimitMapCoconeCofanMkEquiv _ _ _).1 (isColimitOfPreserves F hf.isColimit₁)
  isColimit₂ := (isColimitMapCoconeCofanMkEquiv _ _ _).1 (isColimitOfPreserves F hf.isColimit₂)
  m := F.map hf.m
  hm i := by simp [← Functor.map_comp]
  g₁ := F.map hf.g₁
  g₂ := F.map hf.g₂
  isPushout := hf.isPushout.map F

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma cell_map (i : hf.ι) :
    (hf.map F).cell i = F.map (hf.cell i) := by
  simp [AttachCells.cell]

end AttachCells

-- this is from https://github.com/joelriou/topcat-model-category/blob/master/TopCatModelCategory/CellComplex.lean
namespace RelativeCellComplex

variable {J : Type*} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {α : J → Type*} {A B : ∀ (j : J), α j → C}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i} {X Y : C} {f : X ⟶ Y}

variable (hf : RelativeCellComplex.{w} basicCell f) (F : C ⥤ D)
  [PreservesWellOrderContinuousOfShape J F] [PreservesColimitsOfShape J F]
  [∀ (T : Type w), PreservesColimitsOfShape (Discrete T) F]
  [PreservesColimitsOfShape WalkingSpan F]

noncomputable def map :
    RelativeCellComplex.{w} (fun j i ↦ F.map (basicCell j i)) (F.map f) where
  toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape.map F
  attachCells j hj := (hf.attachCells j hj).map F

end RelativeCellComplex

end HomotopicalAlgebra

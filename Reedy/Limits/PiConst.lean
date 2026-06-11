/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# `piConst` preserves limits

-/

@[expose] public section

universe v' u' w v u

namespace CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance {C : Type u} [Category.{v} C] [HasProducts.{w} C] (R : C) :
    PreservesLimitsOfSize.{v', u'} (piConst.{w}.obj R) where
  -- This proof mimicks the proof of the dual result for `sigmaConst` in
  -- `Mathlib.CategoryTheory.Limits.Preserves.SigmaConst`.
  preservesLimitsOfShape := ⟨fun {K} ↦ ⟨fun {c} h_c ↦ ⟨by
    replace h_c := (Types.isColimit_iff_coconeTypesIsColimit ..).1
      ⟨isColimitCoconeLeftOpOfCone K h_c⟩
    let coconeTypes (s : Cone (K ⋙ piConst.obj R)) : K.leftOp.CoconeTypes :=
      { pt := s.pt ⟶ R
        ι j k := s.π.app (j.unop) ≫ Pi.π (fun _ ↦ R) k
        ι_naturality g := by ext; simp [← s.w g.unop] }
    exact {
      lift s := Pi.lift (h_c.desc (coconeTypes s))
      fac s j := by
        dsimp
        ext k
        simp [dsimp% h_c.fac_apply, coconeTypes]
      uniq s m hm := by
        dsimp
        ext x
        obtain ⟨j, k, rfl⟩ := Functor.CoconeTypes.IsColimit.ι_jointly_surjective h_c x
        simp [coconeTypes, ← hm, dsimp% h_c.fac_apply] }⟩⟩⟩

end CategoryTheory.Limits

/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Comma

/-!
# ...

-/

@[expose] public section

namespace CategoryTheory.Arrow

open Limits

variable {J C : Type*} [Category* J] [Category* C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
def leftRightJointlyReflectColimit {F : J ⥤ Arrow C} {c : Cocone F}
    (hc₁ : IsColimit (leftFunc.mapCocone c))
    (hc₂ : IsColimit (rightFunc.mapCocone c)) :
    IsColimit c where
  desc s :=
    Arrow.homMk (hc₁.desc (Cocone.mk _ (by exact Functor.whiskerRight s.ι leftFunc)))
      ((hc₂.desc (Cocone.mk _ (by exact Functor.whiskerRight s.ι rightFunc)))) (by
      refine hc₁.hom_ext (fun j ↦ ?_)
      dsimp
      erw [hc₁.fac_assoc, w_assoc, hc₂.fac]
      simp )
  fac s j := by
    ext
    · apply hc₁.fac
    · apply hc₂.fac
  uniq s m hm := by
    ext
    · exact hc₁.hom_ext (fun j ↦ Eq.symm ((hc₁.fac ..).trans (by simp [← hm])))
    · exact hc₂.hom_ext (fun j ↦ Eq.symm ((hc₂.fac ..).trans (by simp [← hm])))

end CategoryTheory.Arrow

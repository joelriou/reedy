/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Yun Liu
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Whiskering and the limit functor
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {J₁ J₂ C : Type*} [Category* J₁] [Category* J₂] [Category* C]
  [HasLimitsOfShape J₁ C] [HasLimitsOfShape J₂ C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[simps]
noncomputable def lim.pre (F : J₁ ⥤ J₂) :
    lim ⟶ (Functor.whiskeringLeft J₁ J₂ C).obj F ⋙ lim where
  app _ := limit.pre _ _

open Limits

end CategoryTheory.Limits

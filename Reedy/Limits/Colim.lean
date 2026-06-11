/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Whiskering and the colimit functor

-/

@[expose] public section

namespace CategoryTheory.Limits

variable {J₁ J₂ C : Type*} [Category* J₁] [Category* J₂] [Category* C]
  [HasColimitsOfShape J₁ C] [HasColimitsOfShape J₂ C]

-- It seems the following is very much missing from mathlib

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[simps]
noncomputable def colim.pre (F : J₁ ⥤ J₂) :
    (Functor.whiskeringLeft J₁ J₂ C).obj F ⋙ colim ⟶ colim where
  app _ := colimit.pre _ _

open Limits

end CategoryTheory.Limits

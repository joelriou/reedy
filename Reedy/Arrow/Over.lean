/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The functor `Over X ⥤ Arrow C`

-/

@[expose] public section

namespace CategoryTheory.Over

variable {C : Type*} [Category* C] {X : C}

set_option backward.defeqAttrib.useBackward true in
@[simps]
def toArrow : Over X ⥤ Arrow C where
  obj Y := Arrow.mk Y.hom
  map f := Arrow.homMk f.left (𝟙 _)

end CategoryTheory.Over

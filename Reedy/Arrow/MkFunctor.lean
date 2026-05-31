/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Functors to Arrow categories

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

set_option backward.defeqAttrib.useBackward true in
@[simps]
def Arrow.mkFunctor {F G : C ⥤ D} (τ : F ⟶ G) : C ⥤ Arrow D where
  obj X := Arrow.mk (τ.app X)
  map f := Arrow.homMk (F.map f) (G.map f)

end CategoryTheory

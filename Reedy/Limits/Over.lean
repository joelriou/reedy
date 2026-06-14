/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Over

/-!
# ...

-/

@[expose] public section

namespace CategoryTheory.Limits

instance {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {J : Type*} [Category* J] [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J F] (X : C) :
    PreservesColimitsOfShape J (Over.post (X := X) F) where
  preservesColimit {G} := ⟨fun {c} hc ↦
    ⟨isColimitOfReflects (Over.forget _) (by
      exact isColimitOfPreserves (Over.forget _ ⋙ F) hc)⟩⟩

end CategoryTheory.Limits

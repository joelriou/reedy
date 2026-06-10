/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
# Monomorphisms in functor categories and stability under colimits

-/

@[expose] public section

namespace CategoryTheory

open Limits MorphismProperty

variable {C D J : Type*} [Category* C] [Category* D] [Category* J]

instance [HasColimitsOfShape J D] [HasPullbacks D]
    [(monomorphisms D).IsStableUnderColimitsOfShape J] :
    (monomorphisms (C ⥤ D)).IsStableUnderColimitsOfShape J := by
  rw [← functorCategory_monomorphisms]
  infer_instance

end CategoryTheory

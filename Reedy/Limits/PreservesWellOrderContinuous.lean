/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Preorder

/-!
# ...

-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C D J : Type*} [Category* C] [Category* D] [LinearOrder J]

instance : PreservesWellOrderContinuousOfShape J (𝟭 C) where

instance (F : C ⥤ D) [F.IsLeftAdjoint] : PreservesWellOrderContinuousOfShape J F where

open Limits

end CategoryTheory.Limits

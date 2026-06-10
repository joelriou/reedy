/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.Reedy.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Nat.SuccPred

/-!
# The Reedy structure on the simplex category

-/

@[expose] public section

open CategoryTheory MorphismProperty

namespace SimplexCategory

-- C.4.4
-- claim https://github.com/joelriou/reedy/issues/22 if working on this
def reedyStructure :
    ReedyStructure (epimorphisms SimplexCategory) (monomorphisms _) ℕ where
-- the proof should follow from ingredients in the file
-- `Mathlib.AlgebraicTopology.SimplexCategory.Basic`
  deg := len
  lt₁ := sorry
  lt₂ := sorry
  nonempty_unique := sorry

end SimplexCategory

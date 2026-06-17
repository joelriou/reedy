/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.Reedy.ModelCategory
public import Reedy.Reedy.SimplexCategory
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Test file for the Reedy model category structure on (co)simplicial objects

-/

@[expose] public section

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable {C : Type*} [Category* C] [ModelCategory C]
  [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]

example : ModelCategory (CosimplicialObject C) :=
  inferInstanceAs (ModelCategory (SimplexCategory.reedyStructure.FunctorCategory C))

example : ModelCategory (SimplicialObject C) :=
  inferInstanceAs (ModelCategory (SimplexCategory.reedyStructure.op.FunctorCategory C))

end HomotopicalAlgebra

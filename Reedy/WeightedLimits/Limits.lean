/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.WeightedLimits.Colimits

/-!
# Weighted limits

-/

@[expose] public section

universe w

namespace CategoryTheory.Limits

open Opposite

variable {J' : Type u} [Category.{v} J'] {C : Type*} [Category* C]
  {J : Type*} [Category J]

-- TODO: dualize the API from the `Colimits.lean` file and
-- obtain the parametrized adjunction

-- in this file the weights shall be functors `J' ⥤ Type w`

noncomputable def weightedLim₂ :
    (J' ⥤ Jᵒᵖ ⥤ Type w)ᵒᵖ ⥤ (J' ⥤ C) ⥤ (J ⥤ C) := by
  sorry

variable [HasColimitsOfSize.{w} C]

def weightedLim₂Adj₂ :
    weightedColim₂.{w} (J := J) (J' := J') (C := C) ⊣₂ weightedLim₂ :=
  sorry

end CategoryTheory.Limits

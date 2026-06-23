/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.Reedy.WeakFactorizationSystem.Defs

/-!
# The factorization axiom

-/

universe w u

@[expose] public section

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable {C : Type u} [SmallCategory C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type w} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

namespace ReedyStructure

open MorphismProperty

variable (r : ReedyStructure W₁ W₂ α) {D : Type*} [Category* D]
  (P₁ : MorphismProperty D) (P₂ : MorphismProperty D)
  [HasColimitsOfSize.{w, w} (Type u)] [NoMaxOrder α]
  [HasColimitsOfShape α D] [HasIterationOfShape α D]
  [HasColimitsOfSize.{u, u} D] [HasLimitsOfSize.{u, u} D]

-- C.5.7
instance [P₁.HasFactorization P₂] : (r.left P₁).HasFactorization (r.right P₂) := sorry

end ReedyStructure

end HomotopicalAlgebra

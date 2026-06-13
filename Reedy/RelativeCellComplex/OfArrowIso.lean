/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic

/-!
# Relative cell complexes and isomorphisms of arrows

-/

universe w t v u

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

namespace RelativeCellComplex

variable {C : Type u} [Category.{v} C]
  {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A B : (j : J) → α j → C}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i} {X Y : C} {f : X ⟶ Y}

@[simps toTransfiniteCompositionOfShape]
def ofArrowIso (hf : RelativeCellComplex.{w} basicCell f) {X' Y' : C} {f' : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk f') :
    RelativeCellComplex.{w} basicCell f' where
  toTransfiniteCompositionOfShape :=
    hf.toTransfiniteCompositionOfShape.ofArrowIso e
  attachCells := hf.attachCells

end RelativeCellComplex

end HomotopicalAlgebra

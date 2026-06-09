/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# ...

-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C]

def MorphismProperty.arrowObj (P : MorphismProperty C) : ObjectProperty (Arrow C) :=
  fun f ↦ P f.hom

def MorphismProperty.ofArrowObj (P : ObjectProperty (Arrow C)) : MorphismProperty C :=
  fun _ _ f ↦ P (Arrow.mk f)

lemma MorphismProperty.isStableUnderRetracts_arrowObj_iff (P : MorphismProperty C) :
    (arrowObj P).IsStableUnderRetracts ↔ P.IsStableUnderRetracts :=
  ⟨fun h ↦ ⟨h.of_retract⟩, fun h ↦ ⟨h.of_retract⟩⟩

instance (P : MorphismProperty C) [P.IsStableUnderRetracts] :
    (MorphismProperty.arrowObj P).IsStableUnderRetracts := by
  rwa [MorphismProperty.isStableUnderRetracts_arrowObj_iff]

instance (P : ObjectProperty (Arrow C)) [P.IsStableUnderRetracts] :
    (MorphismProperty.ofArrowObj P).IsStableUnderRetracts := by
  rwa [← MorphismProperty.isStableUnderRetracts_arrowObj_iff]

end CategoryTheory

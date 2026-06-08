/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# ...

-/

universe u

@[expose] public section

namespace CategoryTheory

namespace MorphismProperty

variable (C : Type*) [Category* C]

abbrev identities : MorphismProperty C :=
  .ofHoms (fun X ↦ 𝟙 X)

variable {C} in
lemma identities_op_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    identities Cᵒᵖ f ↔ identities C f.unop := by
  simp only [identities, ofHoms_iff]
  constructor 
  · intro h 
    rcases h with ⟨i,hi⟩ 
    use i.unop 
    rw [Arrow.mk_eq_mk_iff] at hi
    rcases hi with ⟨hY, hX, h⟩
    subst hY
    subst hX
    simp only [Category.comp_id, eqToHom_refl] at h
    simp [h]
  · intro h
    rcases h with ⟨i,hi⟩
    use Opposite.op i 
    rw [Arrow.mk_eq_mk_iff] at hi
    rcases hi with ⟨hY, hX, h⟩
    subst hY  
    simp [hX] at h ⊢
    rw [Arrow.mk_eq_mk_iff]
    have hX' : X = Y := by
      rw [← Opposite.op_unop X, ← Opposite.op_unop Y]
      rw [congrArg Opposite.op hX]
    subst hX'  
    use rfl, rfl
    simp only [eqToHom_refl, Category.comp_id] 
    have hf : f = 𝟙 X := by
      simpa using congrArg Quiver.Hom.op h
    exact hf

end MorphismProperty

end CategoryTheory

/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Aras Ergus, Julian Külshammer
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
  constructor
    <;> simp only [ofHoms_iff]
    <;> rintro ⟨Z, h⟩
    <;> rw [Arrow.mk_eq_mk_iff] at h
    <;> obtain ⟨h_dom, h_cod, h_f⟩ := h
  · exists Opposite.unop Z
    rw [h_f, Arrow.mk_eq_mk_iff]
    simp only [Category.id_comp, eqToHom_trans, eqToHom_unop, Opposite.unop_inj_iff]
    exact ⟨h_cod, h_dom, True.intro⟩
  · exists Opposite.op Z
    rw [← Quiver.Hom.op_unop f, h_f, Arrow.mk_eq_mk_iff]
    simp only [Category.id_comp, eqToHom_trans, eqToHom_op, Opposite.op_unop]
    exact ⟨by rw [<- h_cod], by rw [<- h_dom], True.intro⟩

end MorphismProperty

end CategoryTheory

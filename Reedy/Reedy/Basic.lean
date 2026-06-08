/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nima Rasekh
-/
module

public import Reedy.MorphismProperty.Identities
public import Reedy.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.Order.SuccPred.Basic

/-!
# Reedy categories

-/

@[expose] public section

universe u

namespace CategoryTheory

-- C.4.1
open MorphismProperty in
structure ReedyStructure {C : Type*} [Category* C] (W₁ W₂ : MorphismProperty C)
    [W₁.IsMultiplicative] [W₂.IsMultiplicative]
    (α : Type*) [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
    where
  deg : C → α
  lt₁ {X Y : C} (f : X ⟶ Y) (hf : W₁ f) (hf' : ¬ identities C f) : deg Y < deg X
  lt₂ {X Y : C} (f : X ⟶ Y) (hf : W₂ f) (hf' : ¬ identities C f) : deg X < deg Y
  nonempty_unique {X Y : C} (f : X ⟶ Y) :
    Nonempty (Unique (W₁.MapFactorizationData W₂ f))

namespace ReedyStructure

variable {C : Type u} [SmallCategory C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure W₁ W₂ α)

@[simps]
protected def op : ReedyStructure W₂.op W₁.op α where
  deg := r.deg ∘ Opposite.unop
  lt₁ f hf hf' := r.lt₂ f.unop hf (by
    simpa [MorphismProperty.identities_op_iff] using hf')
  lt₂ f hf hf' := r.lt₁ f.unop hf (by
    simpa [MorphismProperty.identities_op_iff] using hf')
  nonempty_unique f :=
    MorphismProperty.MapFactorizationData.opEquiv.uniqueCongr.nonempty_congr.1
      (r.nonempty_unique f.unop)

lemma le₁ {X Y : C} (f : X ⟶ Y) (hf : W₁ f) : r.deg Y ≤ r.deg X := by
  by_cases hf' : MorphismProperty.identities C f
  · cases hf'
    rfl
  · exact (r.lt₁ f hf hf').le

lemma le₂ {X Y : C} (f : X ⟶ Y) (hf : W₂ f) : r.deg X ≤ r.deg Y := by
  by_cases hf' : MorphismProperty.identities C f
  · cases hf'
    rfl
  · exact (r.lt₂ f hf hf').le

include r in
lemma subsingleton_mapFactorizationData ⦃X Y : C⦄ (f : X ⟶ Y) :
    Subsingleton (W₁.MapFactorizationData W₂ f) := by
  have := (r.nonempty_unique f).some
  infer_instance

@[no_expose]
noncomputable def mapFactorizationData {X Y : C} (f : X ⟶ Y) :
    W₁.MapFactorizationData W₂ f := by
  letI := (r.nonempty_unique f).some
  exact default

@[no_expose]
noncomputable def degHom {X Y : C} (f : X ⟶ Y) : α := r.deg (r.mapFactorizationData f).Z
lemma degHom_eq {X Y : C} {f : X ⟶ Y} (h : W₁.MapFactorizationData W₂ f) :
    r.degHom f = r.deg h.Z := by
  have := r.subsingleton_mapFactorizationData
  rw [← Subsingleton.elim (r.mapFactorizationData f) h]
  rfl

lemma exists_fac {X Y : C} (f : X ⟶ Y) :
    ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), W₁ a ∧ W₂ b ∧ a ≫ b = f ∧ r.degHom f = r.deg Z :=
  ⟨_, _, _, (r.mapFactorizationData f).hi, (r.mapFactorizationData f).hp,
    (r.mapFactorizationData f).fac, rfl⟩

-- This is needed for the definition of `skYoneda` in the file `Reedy/Skeleton.lean`.
lemma degHom_le {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y) :
    r.degHom (f ≫ g) ≤ r.deg Z := by
  -- the argument is essentially in the diagram of lemma C.4.7
  obtain ⟨Zf, f₁, f₂, hf₁, hf₂, fac_f, eq_f⟩ := r.exists_fac f
  obtain ⟨Zg, g₁, g₂, hg₁, hg₂, fac_g, eq_g⟩ := r.exists_fac g
  obtain ⟨Zh, h₁, h₂, hh₁, hh₂, fac_h, eq_h⟩ := r.exists_fac (f₂ ≫ g₁)
  let factfg : W₁.MapFactorizationData W₂ (f ≫ g) :=
    { Z := Zh
      i := f₁ ≫ h₁
      p := h₂ ≫ g₂
      fac := by simp [reassoc_of% fac_h, reassoc_of% fac_f, fac_g]
      hi := W₁.comp_mem _ _ hf₁ hh₁
      hp := W₂.comp_mem _ _ hh₂ hg₂ }
  rw [r.degHom_eq factfg]
  exact (r.le₁ _ hh₁).trans (r.le₂ _ hf₂)

end ReedyStructure

end CategoryTheory

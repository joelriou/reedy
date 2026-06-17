/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Julian Külshammer
-/
module

public import Reedy.Reedy.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Nat.SuccPred

/-!
# The Reedy structure on the simplex category

-/

@[expose] public section

open CategoryTheory MorphismProperty HomotopicalAlgebra

namespace SimplexCategory

-- C.4.4
def reedyStructure :
    ReedyStructure (epimorphisms SimplexCategory) (monomorphisms _) ℕ where
  deg := len
  lt₁ := by
    intro n m f _ hf
    refine lt_of_le_of_ne (len_le_of_epi f) (fun h ↦ ?_)
    obtain rfl : m = n := SimplexCategory.ext_iff.mpr h
    obtain rfl := eq_id_of_epi f
    exact hf ⟨_⟩
  lt₂  := by
    intro n m f _ hf
    refine lt_of_le_of_ne (len_le_of_mono f) (fun h ↦ ?_)
    obtain rfl : m = n := SimplexCategory.ext_iff.mpr h.symm
    obtain rfl := eq_id_of_mono f
    exact hf ⟨_⟩
  nonempty_unique {x y} f := by
    refine ⟨?_, ?_⟩
    · haveI : CategoryTheory.Limits.HasStrongEpiMonoFactorisations SimplexCategory:= by
        infer_instance
      obtain ⟨F⟩ := this
      letI t := (F f).some
      exact ⟨t.I, t.e, t.m, t.fac, by infer_instance, by infer_instance⟩
    haveI : Subsingleton
      ((epimorphisms SimplexCategory).MapFactorizationData (monomorphisms SimplexCategory) f) := by
      refine ⟨?_⟩
      rintro ⟨z1, p1, i1, hfac1, _, _⟩ ⟨z2, p2, i2, hfac2, _, _⟩
      obtain rfl := (image_eq hfac1).symm
      obtain rfl := (image_eq hfac2).symm
      obtain rfl : i1 = i2 := by
        rw [← image_ι_eq hfac1, image_ι_eq hfac2]
      obtain rfl : p1 = p2 := by
        rw [← factorThruImage_eq hfac1, factorThruImage_eq hfac2]
      rfl
    exact fun _ ↦ Subsingleton.elim _ _

end SimplexCategory

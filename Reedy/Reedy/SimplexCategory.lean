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

open CategoryTheory MorphismProperty

namespace SimplexCategory

-- C.4.4
-- claim https://github.com/joelriou/reedy/issues/22 if working on this
def reedyStructure :
    ReedyStructure (epimorphisms SimplexCategory) (monomorphisms _) ℕ where
-- the proof should follow from ingredients in the file
-- `Mathlib.AlgebraicTopology.SimplexCategory.Basic`
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
      rintro ⟨z1, p1, i1, hfac1, hepi1, hmono1⟩ ⟨z2, p2, i2, hfac2, hepi2, hmono2⟩
      simp [monomorphisms.iff] at hmono1 hmono2
      simp [epimorphisms.iff] at hepi1 hepi2
      have hz1 := (@image_eq _ _ _ _ _ _ _ _ hfac1).symm
      have hz2 := (@image_eq _ _ _ _ _ _ _ _ hfac2).symm
      subst hz1 hz2
      have hi : i1 = i2 := by
        rw [← image_ι_eq hfac1, image_ι_eq hfac2]
      have hp : p1 = p2 := by
        rw [← factorThruImage_eq hfac1, factorThruImage_eq hfac2]
      subst hi hp
      rfl
    exact fun _ ↦ Subsingleton.elim _ _

end SimplexCategory

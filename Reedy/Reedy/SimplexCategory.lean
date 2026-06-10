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

lemma identities_of_epi_of_len_eq {x y : SimplexCategory} (f : x ⟶ y) [Epi f]
  (hlen : x.len = y.len) : identities SimplexCategory f := by
  have heq := SimplexCategory.ext_iff.mpr hlen
  subst heq
  have := eq_id_of_epi f
  rw [this]
  exact ofHoms.mk _

lemma identities_of_mono_of_len_eq {x y : SimplexCategory} (f : x ⟶ y) [Mono f]
  (hlen : x.len = y.len) : identities SimplexCategory f := by
  have heq := SimplexCategory.ext_iff.mpr hlen
  subst heq
  have := eq_id_of_mono f
  rw [this]
  exact ofHoms.mk _

-- C.4.4
-- claim https://github.com/joelriou/reedy/issues/22 if working on this
def reedyStructure :
    ReedyStructure (epimorphisms SimplexCategory) (monomorphisms _) ℕ where
-- the proof should follow from ingredients in the file
-- `Mathlib.AlgebraicTopology.SimplexCategory.Basic`
  deg := len
  lt₁ f hepi hnonid := by
    haveI := (epimorphisms.iff f).mp hepi
    exact lt_of_le_of_ne (len_le_of_epi f) (fun h ↦ hnonid (identities_of_epi_of_len_eq f h.symm))

  lt₂ f hmono hnonid := by
    haveI := (monomorphisms.iff f).mp hmono
    exact lt_of_le_of_ne (len_le_of_mono f) (fun h ↦ hnonid (identities_of_mono_of_len_eq f h))
  nonempty_unique := sorry

end SimplexCategory

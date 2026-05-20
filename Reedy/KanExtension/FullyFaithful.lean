/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction


/-!
# Kan extensions and fully faithful functors

-/

@[expose] public section

namespace CategoryTheory

variable {C₀ C D : Type*} [Category* C₀] [Category C] [Category D]

namespace Functor

variable (L : C₀ ⥤ C)
  [∀ (F : C₀ ⥤ D), Functor.HasPointwiseLeftKanExtension L F]
  [∀ (F : C₀ ⥤ D), Functor.HasPointwiseRightKanExtension L F]

noncomputable def lanRanTriple : Adjunction.Triple L.lan ((whiskeringLeft _ _ D).obj L) L.ran where
  adj₁ := L.lanAdjunction D
  adj₂ := L.ranAdjunction D

variable [L.Full] [L.Faithful]

noncomputable def fullyFaithfulLan : (L.lan (H := D)).FullyFaithful :=
  (L.lanAdjunction D).fullyFaithfulLOfIsIsoUnit

instance : (L.lan (H := D)).Full := L.fullyFaithfulLan.full

instance : (L.lan (H := D)).Faithful := L.fullyFaithfulLan.faithful

noncomputable def lanToRan : L.lan (H := D) ⟶ L.ran (H := D) :=
  (lanRanTriple L (D := D)).leftToRight

-- `lanToRan` is used in C.5.4 (i) [the statement needs a fix]

end Functor

end CategoryTheory

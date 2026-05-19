/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Reedy.Arrow.MkFunctor
public import Reedy.Reedy.Basic
public import Reedy.Subfunctor.ExternalUnionProd
public import Reedy.WeightedLimits.Colimits

/-!
# Skeleton

-/

universe u

@[expose] public section

namespace CategoryTheory

open HomotopicalAlgebra Opposite Limits FunctorToTypes

variable {C : Type u} [SmallCategory C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

namespace ReedyStructure

variable (r : ReedyStructure W₁ W₂ α) {D : Type*} [Category D]

-- given `a : α`, this is the subbifunctor of `yoneda` which consists of maps of degree `< a`
-- Note: contrary to C.4.9 in Riehl-Verity, *Elements of ∞-category theory*,
-- we use `< a` instead of `≤ a`, so that `r.sk ⊥` is empty
@[simps]
def skYoneda (a : α) : Subfunctor₂ (yoneda (C := C)) where
  obj _ _ := setOf (fun f ↦ r.degHom f < a)
  map₁ := sorry
  map₂ := sorry

lemma monotone_skYoneda : Monotone r.skYoneda := sorry

@[simps]
def boundaryYonedaObj (Y : C) : Subfunctor (yoneda.obj Y) where
  obj _ := setOf (fun f ↦ r.degHom f < r.deg Y)
  map _ _ hg := (r.skYoneda (r.deg Y)).map₂ _ _ hg

@[simps]
def boundaryCoyonedaObj (X : C) : Subfunctor (coyoneda.obj (op X)) where
  obj _ := setOf (fun f ↦ r.degHom f < r.deg X)
  map _ _ hf := (r.skYoneda (r.deg X)).map₁ _ _ hf

abbrev externalUnionProd (X : C) :
    Subfunctor₂ (FunctorToTypes.externalProduct (coyoneda.obj (op X)) (yoneda.obj X)) :=
  Subfunctor.unionExternalProd (r.boundaryCoyonedaObj X) (r.boundaryYonedaObj X)

abbrev Cell (a : α) := { X : C // r.deg X = a }

def basicCell (a : α) (c : r.Cell a) := (r.externalUnionProd c.val).ι

-- C.4.13 in Riehl-Verity, *Elements of ∞-category theory*
noncomputable def relativeCellComplex [NoMaxOrder α] :
    RelativeCellComplex r.basicCell (Subfunctor₂.ι (⊥ : Subfunctor₂ yoneda)) where
  F := r.monotone_skYoneda.functor ⋙ Subfunctor₂.toFunctorFunctor yoneda
  isoBot := sorry
  isWellOrderContinuous := sorry
  incl := sorry
  isColimit := sorry
  attachCells a ha :=
    { ι := r.Cell a
      π := id
      cofan₁ := _
      cofan₂ := _
      isColimit₁ := coproductIsCoproduct _
      isColimit₂ := coproductIsCoproduct _
      m := sorry
      hm := sorry
      g₁ := sorry
      g₂ := sorry
-- see https://github.com/leanprover-community/mathlib4/pull/38530 for similar proofs
      isPushout := sorry }

-- See https://github.com/joelriou/topcat-model-category/blob/2e3704c3bb65152d955eeea0a10c24b6bb8c41e8/TopCatModelCategory/CellComplex.lean#L136
-- for the "image" of a relative cell complex by a functor which preserves colimits

variable [HasColimitsOfSize.{u, u} D]

noncomputable def skFunctor : α ⥤ (C ⥤ D) ⥤ C ⥤ D :=
  r.monotone_skYoneda.functor ⋙ Subfunctor₂.toFunctorFunctor yoneda ⋙ weightedColim₂

section Latching

-- C.4.14
noncomputable abbrev latching (X : C) : (C ⥤ D) ⥤ D :=
  weightedColim.obj (r.boundaryYonedaObj X).toFunctor

def latchingι (X : C) : r.latching X ⟶ (evaluation C D).obj X := by
  sorry

noncomputable def relativeLatchingSrc (X : C) : Arrow (C ⥤ D) ⥤ D :=
  pushout (Functor.whiskerLeft _ (r.latchingι X)) (Functor.whiskerRight Arrow.leftToRight _)

noncomputable def relativeLatchingMap (X : C) :
    r.relativeLatchingSrc X ⟶ Arrow.rightFunc ⋙ (evaluation C D).obj X :=
  pushout.desc _ _ (Functor.whiskerLeft_comp_whiskerRight _ _)

-- C.4.15
noncomputable def relativeLatchingFunctor (X : C) : Arrow (C ⥤ D) ⥤ Arrow D :=
  Arrow.mkFunctor (r.relativeLatchingMap X)

end Latching

section Matching

noncomputable def relativeMatchingFunctor (X : C) : Arrow (C ⥤ D) ⥤ Arrow D := by
  have := r
  sorry

end Matching

end ReedyStructure

end CategoryTheory

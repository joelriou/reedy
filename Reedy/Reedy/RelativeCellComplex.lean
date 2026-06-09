/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Reedy.Reedy.Basic
public import Reedy.Subfunctor.ExternalUnionProd

/-!
# The relative cell complex structure on the Yoneda bifunctor

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
  map₁ _ _ _ hf := lt_of_le_of_lt (r.degHom_comp_le _ _) hf
  map₂ _ _ _ _ _ hf := lt_of_le_of_lt (r.degHom_comp_le' _ _) hf

lemma monotone_skYoneda : Monotone r.skYoneda :=
  fun _ _ h _ _ _ hf ↦ lt_of_lt_of_le hf h

@[simp]
lemma skYoneda_bot : r.skYoneda ⊥ = ⊥ := by aesop

lemma iSup_skYoneda [NoMaxOrder α] : ⨆ a, r.skYoneda a = ⊤ := by
  rw [← top_le_iff]
  intro U V f _
  simp only [Subfunctor₂.iSup_obj, skYoneda_obj, Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨Order.succ (r.degHom f), Order.lt_succ _⟩

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

abbrev basicCell (a : α) (c : r.Cell a) := (r.externalUnionProd c.val).ι

noncomputable abbrev sigmaExternalUnionProd (a : α) : C ⥤ Cᵒᵖ ⥤ Type u :=
  ∐ fun (c : r.Cell a) ↦ (r.externalUnionProd c).toFunctor

noncomputable abbrev ιSigmaExternalUnionProd {a : α} (c : r.Cell a) :
    (r.externalUnionProd c).toFunctor ⟶ sigmaExternalUnionProd r a :=
  Sigma.ι (fun (c : r.Cell a) ↦ (r.externalUnionProd c).toFunctor) c

noncomputable abbrev sigmaExternalProduct (a : α) : C ⥤ Cᵒᵖ ⥤ Type u :=
  ∐ fun (c : r.Cell a) ↦
    FunctorToTypes.externalProduct (coyoneda.obj (op c.val)) (yoneda.obj c.val)

noncomputable abbrev ιSigmaExternalProduct {a : α} (c : r.Cell a) :
    FunctorToTypes.externalProduct (coyoneda.obj (op c.val)) (yoneda.obj c.val) ⟶
      sigmaExternalProduct r a :=
  Sigma.ι (fun (c : r.Cell a) ↦
    FunctorToTypes.externalProduct (coyoneda.obj (op c.val)) (yoneda.obj c.val)) c

namespace relativeCellComplex

noncomputable def t (a : α) : r.sigmaExternalUnionProd a ⟶ (r.skYoneda a).toFunctor :=
  Sigma.desc (fun c ↦ Subfunctor₂.lift (Subfunctor₂.ι _ ≫
    fromExternalProductCoyonedaObjOpYonedaObj c.val) sorry)

noncomputable def b (a : α) : r.sigmaExternalProduct a ⟶ (r.skYoneda (Order.succ a)).toFunctor :=
  Sigma.desc (fun c ↦ Subfunctor₂.lift
    (fromExternalProductCoyonedaObjOpYonedaObj c.val) sorry)

noncomputable def l (a : α) : r.sigmaExternalUnionProd a ⟶ r.sigmaExternalProduct a :=
  Limits.Sigma.map (fun x ↦ (r.externalUnionProd x).ι)


@[reassoc (attr := simp)]
lemma ιSigmaExternalUnionProd_t {a : α} (c : r.Cell a) :
    r.ιSigmaExternalUnionProd c ≫ t r a ≫ Subfunctor₂.ι _ =
      (r.externalUnionProd c).ι ≫ fromExternalProductCoyonedaObjOpYonedaObj c.val := by
  simp [Sigma.ι_desc_assoc, t]

@[reassoc (attr := simp)]
lemma ιSigmaExternalProduct_b {a : α} (c : r.Cell a) :
    r.ιSigmaExternalProduct c ≫ b r a ≫ Subfunctor₂.ι _ =
      fromExternalProductCoyonedaObjOpYonedaObj c.val := by
  simp [Sigma.ι_desc_assoc, b]

@[reassoc (attr := simp)]
lemma ιSigmaExternalUnionProd_l {a : α} (c : r.Cell a) :
    r.ιSigmaExternalUnionProd c ≫ l r a =
      r.basicCell a c ≫ r.ιSigmaExternalProduct c := by
  simp [l, ιSigmaExternalProduct]

abbrev ρ (a : α) : (r.skYoneda a).toFunctor ⟶ (r.skYoneda (Order.succ a)).toFunctor :=
  Subfunctor₂.homOfLE (r.monotone_skYoneda (Order.le_succ a))

@[reassoc (attr := simp)]
lemma ρ_ι (a : α) : ρ r a ≫ Subfunctor₂.ι _ = Subfunctor₂.ι _ := rfl

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma w (a : α) : t r a ≫ ρ r a = l r a ≫ b r a := by
  rw [← cancel_mono (Subfunctor₂.ι _)]
  cat_disch

lemma isPullback (a : α) : IsPullback (t r a) (l r a) (ρ r a) (b r a) := sorry

lemma isPushout (a : α) : IsPushout (t r a) (l r a) (ρ r a) (b r a) := sorry

end relativeCellComplex

open relativeCellComplex in
set_option backward.defeqAttrib.useBackward true in
-- C.4.13 in Riehl-Verity, *Elements of ∞-category theory*
noncomputable def relativeCellComplex [NoMaxOrder α] :
    RelativeCellComplex r.basicCell (Subfunctor₂.ι (⊥ : Subfunctor₂ yoneda)) where
  F := r.monotone_skYoneda.functor ⋙ Subfunctor₂.toFunctorFunctor yoneda
  isoBot := Subfunctor₂.eqToIso (by simp)
  isWellOrderContinuous := by
    -- the proof should be roughly similar to the definition of
    -- the field `isColimit` below
    sorry
  incl := { app a := (r.skYoneda a).ι }
  isColimit := by
    -- use `iSup_skYoneda`
    sorry
  attachCells a ha :=
    { ι := r.Cell a
      π := id
      cofan₁ := _
      cofan₂ := _
      isColimit₁ := coproductIsCoproduct _
      isColimit₂ := coproductIsCoproduct _
      m := l r a
      g₁ := t r a
      g₂ := b r a
-- see https://github.com/leanprover-community/mathlib4/pull/38530 for similar proofs
      isPushout := isPushout r a }

-- See https://github.com/joelriou/topcat-model-category/blob/2e3704c3bb65152d955eeea0a10c24b6bb8c41e8/TopCatModelCategory/CellComplex.lean#L136
-- for the "image" of a relative cell complex by a functor which preserves colimits

end ReedyStructure

end CategoryTheory

/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Aras Ergus
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.Lattice
public import Reedy.Reedy.Basic
public import Reedy.Subfunctor.Colimits
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

lemma iSup_skYoneda_iio (m : α) (hm : Order.IsSuccLimit m) :
    ⨆ (a : Set.Iio m), r.skYoneda a = r.skYoneda m := by
  refine le_antisymm ?_ ?_
  · simp only [iSup_le_iff, Subtype.forall, Set.mem_Iio]
    exact fun a ha ↦ r.monotone_skYoneda ha.le
  · intro U V x hx
    simp only [skYoneda_obj, Set.mem_setOf_eq] at hx
    simp only [Subfunctor₂.iSup_obj, skYoneda_obj, Set.iUnion_coe_set, Set.mem_Iio,
      Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨Order.succ (r.degHom x), by rwa [hm.succ_lt_iff],
      Order.lt_succ_of_not_isMax (not_isMax_of_lt hx)⟩

set_option backward.defeqAttrib.useBackward true in
instance : r.monotone_skYoneda.functor.IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨Preorder.isColimitOfIsLUB _ _ (by
    dsimp
    rw [← r.iSup_skYoneda_iio m hm]
    apply isLUB_iSup)⟩

@[simp]
lemma skYoneda_bot : r.skYoneda ⊥ = ⊥ := by aesop

@[simp]
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
  Sigma.desc (fun ⟨X, h_X⟩ ↦ Subfunctor₂.lift (Subfunctor₂.ι _ ≫
    fromExternalProductCoyonedaObjOpYonedaObj X) (by
      rintro X₁ X₂ _ ⟨⟨⟨f₁, f₂⟩, h_f⟩, rfl⟩
      rcases h_f with ⟨_, h_boundary⟩ | ⟨h_boundary, _⟩
      · apply lt_of_le_of_lt
        · apply r.degHom_comp_le
        · change r.degHom f₂ < a
          simp only [boundaryYonedaObj, Set.mem_setOf_eq, h_X] at h_boundary
          exact h_boundary
      · apply lt_of_le_of_lt
        · apply r.degHom_comp_le'
        · change r.degHom f₁ < a
          simp only [boundaryCoyonedaObj_obj, Set.mem_setOf_eq, h_X] at h_boundary
          exact h_boundary))

noncomputable def b [NoMaxOrder α] (a : α) :
    r.sigmaExternalProduct a ⟶ (r.skYoneda (Order.succ a)).toFunctor :=
  Sigma.desc (fun ⟨X, h_X⟩ ↦ Subfunctor₂.lift
    (fromExternalProductCoyonedaObjOpYonedaObj X) (by
      intros X₁ X₂ f h_f
      simp only [skYoneda_obj, Order.lt_succ_iff, Set.mem_setOf_eq]
      rcases h_f with ⟨⟨f₁, f₂⟩, h_comp⟩
      simp only [fromExternalProductCoyonedaObjOpYonedaObj, TypeCat.hom_ofHom,
        TypeCat.Fun.coe_mk] at h_comp
      rw [<- h_comp, <- h_X]
      apply r.degHom_le
    ))

noncomputable def l (a : α) : r.sigmaExternalUnionProd a ⟶ r.sigmaExternalProduct a :=
  Limits.Sigma.map (fun x ↦ (r.externalUnionProd x).ι)

@[reassoc (attr := simp)]
lemma ιSigmaExternalUnionProd_t {a : α} (c : r.Cell a) :
    r.ιSigmaExternalUnionProd c ≫ t r a ≫ Subfunctor₂.ι _ =
      (r.externalUnionProd c).ι ≫ fromExternalProductCoyonedaObjOpYonedaObj c.val := by
  simp [Sigma.ι_desc_assoc, t]

@[reassoc (attr := simp)]
lemma ιSigmaExternalProduct_b [NoMaxOrder α] {a : α} (c : r.Cell a) :
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
lemma w [NoMaxOrder α] (a : α) : t r a ≫ ρ r a = l r a ≫ b r a := by
  rw [← cancel_mono (Subfunctor₂.ι _)]
  cat_disch

set_option backward.defeqAttrib.useBackward true in
lemma isPullback [NoMaxOrder α] (a : α) : IsPullback (t r a) (l r a) (ρ r a) (b r a) where
  w := w r a
  isLimit' :=
    ⟨evaluationJointlyReflectsLimits _
      (fun U ↦ (isLimitMapConePullbackConeEquiv _ _).symm
        (evaluationJointlyReflectsLimits _
          (fun V ↦ (isLimitMapConePullbackConeEquiv _ _).symm (by
            refine (IsPullback.isLimit ?_)
            rw [Types.isPullback_iff]
            refine ⟨NatTrans.congr_app (NatTrans.congr_app (w r a) U) V,
              ?_, ?_⟩
            · dsimp
              sorry
            · dsimp
              sorry))))⟩

set_option backward.defeqAttrib.useBackward true in
lemma isPushout [NoMaxOrder α] (a : α) : IsPushout (t r a) (l r a) (ρ r a) (b r a) where
  w := w r a
  isColimit' :=
    ⟨evaluationJointlyReflectsColimits _
      (fun U ↦ (isColimitMapCoconePushoutCoconeEquiv _ _).symm
        (evaluationJointlyReflectsColimits _
          (fun V ↦ (isColimitMapCoconePushoutCoconeEquiv _ _).symm (by
            refine (IsPushout.isColimit ?_)
            dsimp
            apply +allowSynthFailures Types.isPushout_of_isPullback_of_mono'
            · exact ((isPullback r a).map ((evaluation ..).obj U)).map ((evaluation ..).obj V)
            · rw [mono_iff_injective]
              rintro ⟨x, _⟩ ⟨y, _⟩ h
              rwa [Subtype.ext_iff] at h ⊢
            · sorry
            · sorry))))⟩

end relativeCellComplex

open relativeCellComplex in
set_option backward.defeqAttrib.useBackward true in
-- C.4.13 in Riehl-Verity, *Elements of ∞-category theory*
noncomputable def relativeCellComplex [NoMaxOrder α] :
    RelativeCellComplex r.basicCell (Subfunctor₂.ι (⊥ : Subfunctor₂ yoneda)) where
  F := r.monotone_skYoneda.functor ⋙ Subfunctor₂.toFunctorFunctor yoneda
  isoBot := Subfunctor₂.eqToIso (by simp)
  isWellOrderContinuous := ⟨fun m hm ↦
    ⟨isColimitOfPreserves (Subfunctor₂.toFunctorFunctor _)
      (r.monotone_skYoneda.functor.isColimitOfIsWellOrderContinuous m hm)⟩⟩
  incl := { app a := (r.skYoneda a).ι }
  isColimit :=
    IsColimit.ofIsoColimit
      (isColimitOfPreserves (Subfunctor₂.toFunctorFunctor _)
      (CompleteLattice.colimitCocone r.monotone_skYoneda.functor).isColimit)
        (Cocone.ext (Subfunctor₂.eqToIso (by simp) ≪≫ Subfunctor₂.topIso _))
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

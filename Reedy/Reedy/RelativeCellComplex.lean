/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Aras Ergus
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Types.Monomorphisms
public import Reedy.Reedy.Basic
public import Reedy.Limits.FunctorCategoryMono
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

lemma ιSigmaExternalUnionProd_jointly_surjective {a : α} {U : C} {V : Cᵒᵖ}
    (x : ((sigmaExternalUnionProd r a).obj U).obj V) :
    ∃ (c : r.Cell a) (y : _), ((r.ιSigmaExternalUnionProd c).app U).app V y = x := by
  obtain ⟨⟨c⟩, y, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj U ⋙ (evaluation _ _).obj V)
      (coproductIsCoproduct _)) x
  exact ⟨c, y, rfl⟩

noncomputable abbrev sigmaExternalProduct (a : α) : C ⥤ Cᵒᵖ ⥤ Type u :=
  ∐ fun (c : r.Cell a) ↦
    FunctorToTypes.externalProduct (coyoneda.obj (op c.val)) (yoneda.obj c.val)

noncomputable abbrev ιSigmaExternalProduct {a : α} (c : r.Cell a) :
    FunctorToTypes.externalProduct (coyoneda.obj (op c.val)) (yoneda.obj c.val) ⟶
      sigmaExternalProduct r a :=
  Sigma.ι (fun (c : r.Cell a) ↦
    FunctorToTypes.externalProduct (coyoneda.obj (op c.val)) (yoneda.obj c.val)) c

lemma ιSigmaExternalProduct_jointly_surjective {a : α} {U : C} {V : Cᵒᵖ}
    (x : ((r.sigmaExternalProduct a).obj U).obj V) :
    ∃ (c : r.Cell a) (y : _), ((r.ιSigmaExternalProduct c).app U).app V y = x := by
  obtain ⟨⟨c⟩, y, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj U ⋙ (evaluation _ _).obj V)
      (coproductIsCoproduct _)) x
  exact ⟨c, y, rfl⟩

lemma ιSigmaExternalProduct_eq_iff
    {a : α} {U : C} {V : Cᵒᵖ}
    (c : r.Cell a) (x : (c.val ⟶ U) × (V.unop ⟶ c.val))
    (d : r.Cell a) (y : (d.val ⟶ U) × (V.unop ⟶ d.val)) :
    ((r.ιSigmaExternalProduct c).app U).app V x =
      ((r.ιSigmaExternalProduct d).app U).app V y ↔
    ∃ (h : c = d), y = cast (by rw [h]) x :=
  Cofan.inj_apply_eq_iff_of_isColimit
    (isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj U ⋙ (evaluation _ _).obj V) _ _
      (coproductIsCoproduct _)) _ _

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
  Sigma.desc (fun ⟨X, hX⟩ ↦ Subfunctor₂.lift
    (fromExternalProductCoyonedaObjOpYonedaObj X) (by
      intros X₁ X₂ f hf
      simp only [skYoneda_obj, Order.lt_succ_iff, Set.mem_setOf_eq]
      obtain ⟨⟨f₁, f₂⟩, rfl⟩ := hf
      rw [← hX]
      apply r.degHom_le))

noncomputable def l (a : α) : r.sigmaExternalUnionProd a ⟶ r.sigmaExternalProduct a :=
  Limits.Sigma.map (fun x ↦ (r.externalUnionProd x).ι)

instance (a : α) : Mono (l r a) := by dsimp [l]; infer_instance

@[reassoc (attr := simp)]
lemma ιSigmaExternalUnionProd_t {a : α} (c : r.Cell a) :
    r.ιSigmaExternalUnionProd c ≫ t r a ≫ Subfunctor₂.ι _ =
      (r.externalUnionProd c).ι ≫ fromExternalProductCoyonedaObjOpYonedaObj c.val := by
  simp [Sigma.ι_desc_assoc, t]

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma ιSigmaExternalProduct_t_app_app_coe [NoMaxOrder α] {a : α} (c : r.Cell a)
    {U : C} {V : Cᵒᵖ} (i : c.val ⟶ U) (p : V.unop ⟶ c.val) (hip) :
    dsimp% (((t r a).app U).app V (((r.ιSigmaExternalUnionProd c).app U).app V ⟨⟨i, p⟩, hip⟩)).1 =
      p ≫ i :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app
    (ιSigmaExternalUnionProd_t r c) U) V) _

@[reassoc (attr := simp)]
lemma ιSigmaExternalProduct_b [NoMaxOrder α] {a : α} (c : r.Cell a) :
    r.ιSigmaExternalProduct c ≫ b r a ≫ Subfunctor₂.ι _ =
      fromExternalProductCoyonedaObjOpYonedaObj c.val := by
  simp [Sigma.ι_desc_assoc, b]

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma ιSigmaExternalProduct_b_app_app_coe [NoMaxOrder α] {a : α} (c : r.Cell a)
    {U : C} {V : Cᵒᵖ} (i : c.val ⟶ U) (p : V.unop ⟶ c.val) :
    dsimp% (((b r a).app _).app _ (((r.ιSigmaExternalProduct c).app U).app V ⟨i, p⟩)).val =
      p ≫ i :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app
    (ιSigmaExternalProduct_b r c) U) V) _

@[reassoc (attr := simp)]
lemma ιSigmaExternalUnionProd_l {a : α} (c : r.Cell a) :
    r.ιSigmaExternalUnionProd c ≫ l r a =
      r.basicCell a c ≫ r.ιSigmaExternalProduct c := by
  simp [l, ιSigmaExternalProduct]

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma ιSigmaExternalUnionProd_app_app {a : α} {c : r.Cell a} {U : C} {V : Cᵒᵖ}
    (i : c.val ⟶ U) (p : V.unop ⟶ c.val) (hip) :
    dsimp% ((l r a).app U).app V (((r.ιSigmaExternalUnionProd c).app U).app V ⟨⟨i, p⟩, hip⟩) =
      ((r.ιSigmaExternalProduct c).app U).app V (i, p) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (NatTrans.congr_app (ιSigmaExternalUnionProd_l r c) U) V) _

abbrev ρ (a : α) : (r.skYoneda a).toFunctor ⟶ (r.skYoneda (Order.succ a)).toFunctor :=
  Subfunctor₂.homOfLE (r.monotone_skYoneda (Order.le_succ a))

@[reassoc (attr := simp)]
lemma ρ_ι (a : α) : ρ r a ≫ Subfunctor₂.ι _ = Subfunctor₂.ι _ := rfl

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma w [NoMaxOrder α] (a : α) : t r a ≫ ρ r a = l r a ≫ b r a := by
  rw [← cancel_mono (Subfunctor₂.ι _)]
  cat_disch

set_option backward.isDefEq.respectTransparency false in
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
                fun x y ⟨h₁, h₂⟩ ↦ ?_, ?_⟩
            · dsimp at x y h₁ h₂
              have : Mono (((l r a).app U).app V) := inferInstance
              rw [mono_iff_injective] at this
              exact this h₂
            · dsimp
              intro ⟨f, hf⟩ x h
              obtain ⟨c, ⟨i, p⟩, rfl⟩ := r.ιSigmaExternalProduct_jointly_surjective x
              obtain rfl : f = p ≫ i := by simpa [Subtype.ext_iff] using h
              refine ⟨((r.ιSigmaExternalUnionProd c).app U).app V ⟨(i, p), ?_⟩, ?_, ?_⟩
              · rw [Subfunctor.mem_unionExternalProd_obj_obj_iff]
                obtain hf | hf := r.degHom_lt_or_of_degHom_comp_lt p i
                  (by simpa only [c.prop] using hf)
                · exact Or.inl (by simpa)
                · exact Or.inr (by simpa)
              · simp [Subtype.ext_iff]
              · simp))))⟩

set_option backward.defeqAttrib.useBackward true in
lemma degHom₁_eq_of_nonMem_range_l {a : α} {c : r.Cell a} {U : C} {V : Cᵒᵖ}
    (i : c.val ⟶ U) (p : V.unop ⟶ c.val)
    (hip : ((r.ιSigmaExternalProduct c).app U).app V (i, p) ∉ Set.range (((l r a).app U).app V)) :
    r.degHom p = a := by
  by_contra!
  have : r.degHom p < a :=
    lt_of_le_of_ne (by simpa [c.prop] using r.degHom_le_deg' p) this
  refine hip ⟨((r.ιSigmaExternalUnionProd c).app U).app V ⟨⟨i, p⟩, ?_⟩, ?_⟩
  · rw [Subfunctor.mem_unionExternalProd_obj_obj_iff]
    exact Or.inl (by simpa [c.prop])
  · simp

set_option backward.defeqAttrib.useBackward true in
lemma degHom₂_eq_of_nonMem_range_l {a : α} {c : r.Cell a} {U : C} {V : Cᵒᵖ}
    (i : c.val ⟶ U) (p : V.unop ⟶ c.val)
    (hip : ((r.ιSigmaExternalProduct c).app U).app V (i, p) ∉ Set.range (((l r a).app U).app V)) :
    r.degHom i = a := by
  by_contra!
  have : r.degHom i < a :=
    lt_of_le_of_ne (by simpa [c.prop] using r.degHom_le_deg i) this
  refine hip ⟨((r.ιSigmaExternalUnionProd c).app U).app V ⟨⟨i, p⟩, ?_⟩, ?_⟩
  · rw [Subfunctor.mem_unionExternalProd_obj_obj_iff]
    exact Or.inr (by simpa [c.prop])
  · simp

set_option backward.isDefEq.respectTransparency false in
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
            · ext ⟨f, hf⟩
              simp only [Order.lt_succ_iff] at hf
              simp only [TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Set.sup_eq_union, Set.mem_union,
                Set.mem_range, Subtype.mk.injEq, Subtype.exists, exists_prop, exists_eq_right,
                Set.mem_univ, iff_true]
              obtain hf | hf := hf.lt_or_eq
              · refine Or.inl hf
              · obtain ⟨Z, p, i, hp, hi, hpi, h⟩ := r.exists_fac f
                let c : r.Cell a := ⟨Z, by rwa [← h]⟩
                exact Or.inr ⟨((r.ιSigmaExternalProduct c).app _).app _ (i, p), by ext; simpa⟩
            -- https://github.com/joelriou/reedy/issues/35
            · intro x y hx hy fac
              obtain ⟨c, ⟨i, p⟩, rfl⟩ := r.ιSigmaExternalProduct_jointly_surjective x
              obtain ⟨c', ⟨i', p'⟩, rfl⟩ := r.ιSigmaExternalProduct_jointly_surjective y
              dsimp at i p
              simp only [Functor.flip_obj_obj, yoneda_obj_obj, Subtype.ext_iff,
                ιSigmaExternalProduct_b_app_app_coe] at fac
              let φ : W₁.MapFactorizationData W₂ (p ≫ i) :=
                { Z := c.val,
                  i := p
                  p := i
                  hp :=
                    r.prop_of_degHom_eq_deg_src
                      (by rw [degHom₂_eq_of_nonMem_range_l _ _ _ hx, c.prop])
                  hi :=
                    r.prop_of_degHom_eq_deg_tgt
                      (by rw [degHom₁_eq_of_nonMem_range_l _ _ _ hx, c.prop]) }
              let φ' : W₁.MapFactorizationData W₂ (p ≫ i) :=
                { Z := c'.val,
                  p := i'
                  i := p'
                  hp :=
                    r.prop_of_degHom_eq_deg_src
                      (by rw [degHom₂_eq_of_nonMem_range_l _ _ _ hy, c'.prop])
                  hi :=
                    r.prop_of_degHom_eq_deg_tgt
                      (by rw [degHom₁_eq_of_nonMem_range_l _ _ _ hy, c'.prop]) }
              obtain rfl : c = c' := by ext; exact r.unique_obj φ φ'
              have := r.unique φ φ'
              simp only [eqToHom_refl, Category.comp_id, Category.id_comp,
                exists_const, φ, φ'] at this
              obtain rfl : p = p' := this.1
              obtain rfl : i = i' := this.2
              rfl ))))⟩

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
      isPushout := isPushout r a }

-- See https://github.com/joelriou/topcat-model-category/blob/2e3704c3bb65152d955eeea0a10c24b6bb8c41e8/TopCatModelCategory/CellComplex.lean#L136
-- for the "image" of a relative cell complex by a functor which preserves colimits

end ReedyStructure

end CategoryTheory

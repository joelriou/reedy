/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Over

/-!
# Relative cell complexes in the `Under` category

-/

universe w t v u

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

instance {J C : Type*} [LinearOrder J] [Category* C] (X₀ : C) :
    PreservesWellOrderContinuousOfShape J (Under.forget X₀) where
  preservesColimitsOfShape j hj := by
    have : Nonempty (Set.Iio j) := by
      obtain ⟨b, hb⟩ := not_isMin_iff.1 hj.1
      exact ⟨b, hb⟩
    have : IsFiltered (↑(Set.Iio j)) := { }
    infer_instance

lemma IsPushout.of_exists {C : Type*} [Category* C] {Z X Y P : C}
    {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (w : f ≫ inl = g ≫ inr)
    (h₁ : ∀ ⦃T : C⦄ (a : X ⟶ T) (b : Y ⟶ T) (_ : f ≫ a = g ≫ b),
      ∃ (l : P ⟶ T), inl ≫ l = a ∧ inr ≫ l = b)
    (h₂ : ∀ ⦃T : C⦄ (l₁ l₂ : P ⟶ T), inl ≫ l₁ = inl ≫ l₂ →
      inr ≫ l₁ = inr ≫ l₂ → l₁ = l₂) :
    IsPushout f g inl inr where
  w := w
  isColimit' := ⟨ PushoutCocone.isColimitAux' _ (fun s ↦ Nonempty.some (by
    obtain ⟨l, hl₁, hl₂⟩ := h₁ _ _ s.condition
    exact ⟨⟨l, hl₁, hl₂, fun {m} hm₁ hm₂ ↦ h₂ _ _ (by cat_disch) (by cat_disch)⟩⟩))⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma IsPushout.map_underForget {C : Type*} [Category* C] {X₀ : C}
    {X₁ X₂ X₃ X₄ : Under X₀} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPushout t l r b) :
    IsPushout t.right l.right r.right b.right := by
  refine .of_exists ((Under.forget _).congr_map sq.w) ?_ ?_
  · intro T a b h
    obtain ⟨l, hl₁, hl₂⟩ := sq.exists_desc (W := Under.mk (X₂.hom ≫ a))
      (Under.homMk a) (Under.homMk b (by
        simp only [Under.mk_right, Under.mk_hom, ← Under.w l, Category.assoc,
          ← h, Under.w_assoc])) (by cat_disch)
    exact ⟨l.right, (Under.forget _).congr_map hl₁,
      (Under.forget _).congr_map hl₂⟩
  · intro T l₁ l₂ hl₁ hl₂
    let T' := Under.mk (X₄.hom ≫ l₁)
    let l₁' : X₄ ⟶ T' := Under.homMk l₁
    let l₂' : X₄ ⟶ T' := Under.homMk l₂ (by
      rw [← Under.w r, Category.assoc, ← hl₁]
      simp [T'])
    suffices l₁' = l₂' from (Under.forget _).congr_map this
    apply sq.hom_ext <;> cat_disch

-- TODO:
--instance {C : Type*} [Category* C] (X : C) :
--    PreservesColimitsOfShape WalkingSpan (Under.forget X) := sorry

variable {C : Type u} [Category.{v} C] {X₀ : C}
  {ι : Type w} {A B : ι → Under X₀} (f : ∀ i, A i ⟶ B i)
  {cA : Cofan A} {cB : Cofan B}
  (hcA : IsColimit cA) (hcB : IsColimit cB)
  {cA' : Cofan (fun i ↦ (A i).right)}
  {cB' : Cofan (fun i ↦ (B i).right)}
  (hcA' : IsColimit cA') (hcB' : IsColimit cB')

set_option backward.isDefEq.respectTransparency false in
include hcB in
lemma IsPushout.of_cofan_under :
    IsPushout (Z := cA'.pt) (X := cA.pt.right)
      (Y := cB'.pt) (P := cB.pt.right)
      (Cofan.IsColimit.desc hcA' (fun i ↦ (cA.inj i).right))
      (Cofan.IsColimit.desc hcA' (fun i ↦ (f i).right ≫ cB'.inj i))
      (Cofan.IsColimit.desc hcA (fun i ↦ f i ≫ cB.inj i)).right
      (Cofan.IsColimit.desc hcB' (fun i ↦ (cB.inj i).right)) := by
  refine IsPushout.of_exists ?_ ?_ ?_
  · exact Cofan.IsColimit.hom_ext hcA' _ _ (by simp [← Under.comp_right])
  · intro T a b h
    replace h (i) := cA'.inj i ≫= h
    simp only [Cofan.IsColimit.fac_assoc, Category.assoc] at h
    let T' := Under.mk (cA.pt.hom ≫ a)
    let a' : cA.pt ⟶ T' := Under.homMk a
    let φ (i) : B i ⟶ T' := Under.homMk (cB'.inj i ≫ b) (by
      dsimp [T']
      rw [← Under.w_assoc (f i), ← h]
      simp)
    refine ⟨(Cofan.IsColimit.desc hcB φ).right, ?_, ?_⟩
    · change _ = a'.right
      rw [← Under.comp_right]
      congr 1
      refine Cofan.IsColimit.hom_ext hcA _ _ (fun i ↦ ?_)
      simp only [Cofan.IsColimit.fac_assoc, Category.assoc]
      ext
      simp [φ, a', h]
    · exact Cofan.IsColimit.hom_ext hcB' _ _ (fun i ↦ by simp [← Under.comp_right, φ])
  · intro T l₁ l₂ h₁ h₂
    let T' := Under.mk (cA.pt.hom ≫ (Cofan.IsColimit.desc hcA (fun i ↦ f i ≫ cB.inj i)).right ≫ l₁)
    let l₁' : cB.pt ⟶ T' := Under.homMk l₁ (by simp [T'])
    let l₂' : cB.pt ⟶ T' := Under.homMk l₂ (by
      rw [← Under.w (Cofan.IsColimit.desc hcA (fun i ↦ f i ≫ cB.inj i))]
      simp only [T', Category.assoc, Under.mk_hom, h₁])
    suffices l₁' = l₂' from Functor.congr_map (Under.forget _) this
    exact Cofan.IsColimit.hom_ext hcB _ _ (fun i ↦ by ext; simpa using! cB'.inj i ≫= h₂)

end CategoryTheory

namespace HomotopicalAlgebra

namespace AttachCells

variable {C : Type u} [Category.{v} C] {X₀ : C}
  {α : Type t} {A B : α → Under X₀} {g : ∀ a, A a ⟶ B a}
  {X₁ X₂ : Under X₀} {f : X₁ ⟶ X₂}
  [HasCoproducts.{w} C]

set_option backward.isDefEq.respectTransparency false in
noncomputable def ofUnder (hf : AttachCells.{w, t} g f) :
    AttachCells (fun a ↦ (g a).right) f.right where
  ι := hf.ι
  π := hf.π
  cofan₁ := _
  cofan₂ := _
  isColimit₁ := coproductIsCoproduct _
  isColimit₂ := coproductIsCoproduct _
  m := Limits.Sigma.map (fun _ ↦ (g _).right)
  hm i := by simp
  g₁ := Sigma.desc (fun i ↦ (hf.cofan₁.inj _).right ≫ hf.g₁.right)
  g₂ := Sigma.desc (fun i ↦ (hf.cofan₂.inj _).right ≫ hf.g₂.right)
  isPushout := by
    have h₁ := IsPushout.of_cofan_under (fun i ↦ g (hf.π i)) hf.isColimit₁
      hf.isColimit₂ (coproductIsCoproduct _)
      (coproductIsCoproduct _)
    have h₂ := hf.isPushout.map_underForget
    have : Cofan.IsColimit.desc hf.isColimit₁ (fun i ↦ g (hf.π i) ≫ hf.cofan₂.inj i) =
        hf.m :=
      Cofan.IsColimit.hom_ext hf.isColimit₁ _ _ (fun i ↦ by simp)
    rw [← this] at h₂
    convert h₁.paste_horiz h₂ using 1
    · refine Sigma.hom_ext _ _ (fun i ↦ ?_)
      rw [colimit.ι_desc]
      symm
      apply Cofan.IsColimit.fac_assoc
    · refine Sigma.hom_ext _ _ (fun i ↦ ?_)
      simp only [Sigma.ι_map, cofan_mk_inj]
      erw [Cofan.IsColimit.fac]
    · refine Sigma.hom_ext _ _ (fun i ↦ ?_)
      simp only [colimit.ι_desc, Cofan.mk_ι_app]
      erw [Cofan.IsColimit.fac_assoc]

end AttachCells

namespace RelativeCellComplex

variable {C : Type u} [Category.{v} C] {X₀ : C}
  {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A B : (j : J) → α j → Under X₀}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i} {X Y : Under X₀} {f : X ⟶ Y}
  [HasCoproducts.{w} C]

noncomputable def ofUnder (hf : RelativeCellComplex.{w} basicCell f) :
    RelativeCellComplex.{w} (fun j i ↦ (basicCell j i).right) f.right where
  F := hf.F ⋙ Under.forget _
  isoBot := (Under.forget _).mapIso hf.isoBot
  incl.app i := (hf.incl.app i).right
  incl.naturality _ _ g := (Under.forget _).congr_map (hf.incl.naturality g)
  fac := (Under.forget _).congr_map hf.fac
  isColimit := isColimitOfPreserves (Under.forget _) hf.isColimit
  attachCells j hj := (hf.attachCells j hj).ofUnder

end RelativeCellComplex

end HomotopicalAlgebra

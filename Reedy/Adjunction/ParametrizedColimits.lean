/-
Copyright (c) 2026 Nima Rasekh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Rasekh
-/
module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Parametrized adjunctions and colimits

Given bifunctors `F : C₁ ⥤ C₂ ⥤ C₃`, `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂` and
a parametrized adjunction `adj₂ : F ⊣₂ G`, we show that for any `X₂ : C₂`,
the functor `F.flip.obj X₂ : C₁ ⥤ C₃` preserves colimits of shape `J`
if for any `X₃ : C₃`, the functor `G.flip.obj X₃ : C₁ᵒᵖ ⥤ C₂`
preserves limits of shape `Jᵒᵖ`.

-/

@[expose] public section

namespace CategoryTheory.ParametrizedAdjunction

open Limits Opposite

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂}
  (adj₂ : F ⊣₂ G) {J : Type*} [Category* J]

include adj₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma preservesColimit_flip_obj (P : J ⥤ C₁)
    [∀ (X₃ : C₃), PreservesLimit P.op (G.flip.obj X₃)] (X₂ : C₂) :
    PreservesColimit P (F.flip.obj X₂) where
  preserves {c} hc := ⟨by
    let cone (s : Cocone (P ⋙ F.flip.obj X₂)) :
        Cone (P.op ⋙ G.flip.obj s.pt) :=
      { pt := X₂
        π.app j := adj₂.homEquiv (s.ι.app j.unop)
        π.naturality _ _ f := by
          simp [← s.w f.unop, adj₂.homEquiv_naturality_one (P.map f.unop)]
          }
    let hc' (s : Cocone (P ⋙ F.flip.obj X₂)) :=
      isLimitOfPreserves (G.flip.obj s.pt) hc.op
    exact {
      desc s := adj₂.homEquiv.symm ((hc' s).lift (cone s))
      fac s j := by
        dsimp
        rw [← dsimp% adj₂.homEquiv_symm_naturality_one (c.ι.app j),
          dsimp% (hc' s).fac (cone s) (op j)]
        simp [cone]
      uniq s m hm := adj₂.homEquiv.injective (by
        simp only [Equiv.apply_symm_apply]
        refine (hc' s).uniq (cone s) _ (fun j ↦ ?_)
        simp [cone, ← hm,
          dsimp% adj₂.homEquiv_naturality_one (c.ι.app j.unop)]) }⟩

variable (J) in
lemma preservesColimitsOfShape_flip_obj
    [∀ (X₃ : C₃), PreservesLimitsOfShape Jᵒᵖ (G.flip.obj X₃)] (X₂ : C₂) :
    PreservesColimitsOfShape J (F.flip.obj X₂) where
  preservesColimit := preservesColimit_flip_obj adj₂ _ _

end CategoryTheory.ParametrizedAdjunction

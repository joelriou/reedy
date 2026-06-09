/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Weighted colimits

-/

@[expose] public section

universe w v u

namespace CategoryTheory.Limits

-- See A.6 in Riehl-Verity (here, we do not need the enriched version)

variable {J : Type u} [Category.{v} J] {C : Type*} [Category* C]

abbrev WeightedCocone (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) :=
  Cocone ((CategoryOfElements.π P).leftOp ⋙ F)

namespace WeightedCocone

set_option backward.defeqAttrib.useBackward true in
@[simps]
protected def yoneda (F : J ⥤ C) (j : J) :
    WeightedCocone (yoneda.obj j) F where
  pt := F.obj j
  ι.app u := F.map u.unop.2
  ι.naturality _ _ f := by
    dsimp
    simp only [← Functor.map_comp, Category.comp_id]
    congr
    exact f.unop.2

def isColimit (F : J ⥤ C) (j : J) : IsColimit (WeightedCocone.yoneda F j) := by
  -- use that the category of elements has an initial object
  sorry

end WeightedCocone

section

variable [HasColimitsOfSize.{v, max u w} C]

noncomputable def weightedColim : (Jᵒᵖ ⥤ Type w) ⥤ (J ⥤ C) ⥤ C where
  obj P := (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π P).leftOp ⋙ colim
  map := sorry

noncomputable def weightedColimitObjObjIsoOfIsColimit
    {P : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {c : WeightedCocone P F}
    (hc : IsColimit c) :
    (weightedColim.obj P).obj F ≅ c.pt :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc

instance (P : Jᵒᵖ ⥤ Type w) {K : Type*} [Category* K] [HasColimitsOfShape K C] :
    PreservesColimitsOfShape K (weightedColim.obj P : (J ⥤ C) ⥤ C) where
  preservesColimit {G} := by dsimp [weightedColim]; infer_instance

instance (F : J ⥤ C) {K : Type*} [Category* K] [HasColimitsOfShape K (Type w)] :
    PreservesColimitsOfShape K (weightedColim.flip.obj F : (Jᵒᵖ ⥤ Type w) ⥤ C) := by
  -- strategy: show that `weightedColim` is a left bifunctor in a parametrized
  -- adjunction and dualize the result in `CategoryTheory.Adjunction.ParametrizedLimits`
  sorry

-- A.6 (iv)
@[simps!]
noncomputable def weightedColim₂ {J' : Type*} [Category* J'] :
    (J' ⥤ Jᵒᵖ ⥤ Type w) ⥤ (J ⥤ C) ⥤ (J' ⥤ C) :=
  (weightedColim.{w}.flip ⋙ Functor.whiskeringRight _ _ _).flip

-- show that `weightedColim₂` also preserves colimits in both variables

end

variable (J C) in
def weightedColim₂ObjYonedaIso [HasColimitsOfSize.{v, max u v} C] :
    weightedColim₂.obj yoneda ≅ 𝟭 (J ⥤ C) :=
  sorry

end CategoryTheory.Limits

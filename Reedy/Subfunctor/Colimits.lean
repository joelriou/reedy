/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.Subfunctor.SubfunctorTwo
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Set

/-!
# Commutation to filtered colimits

-/

universe w

@[expose] public section

namespace CategoryTheory.Subfunctor₂

open Limits

@[simps]
def evaluation {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D ⥤ Type w)
    (X : C) (Y : D) :
    Subfunctor₂ F ⥤ Set ((F.obj X).obj Y) where
  obj A := A.obj X Y
  map f := CategoryTheory.homOfLE (leOfHom f X Y)

instance {C D J : Type*} [Category* C] [Category* D] [Category* J]
    [IsFilteredOrEmpty J] (F : C ⥤ D ⥤ Type w) :
    PreservesColimitsOfShape J (toFunctorFunctor F) where
  preservesColimit {K} :=
    preservesColimit_of_preserves_colimit_cocone
      (Preorder.colimitCoconeOfIsLUB K isLUB_iSup).isColimit
        (evaluationJointlyReflectsColimits _ (fun X ↦
          evaluationJointlyReflectsColimits _ (fun Y ↦ IsColimit.ofIsoColimit
            (isColimitOfPreserves Set.functorToTypes
              ((Preorder.colimitCoconeOfIsLUB
                (K ⋙ evaluation F X Y) isLUB_iSup).isColimit))
            (Cocone.ext (Set.functorToTypes.mapIso
              (CategoryTheory.eqToIso (by cat_disch)))))))

end CategoryTheory.Subfunctor₂

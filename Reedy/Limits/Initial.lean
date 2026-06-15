/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Reedy.Arrow.Limits

/-!
# ...

-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

noncomputable def IsInitial.obj [HasInitial D] {F : C ⥤ D} (hF : IsInitial F) (X : C) :
    IsInitial (F.obj X) :=
  IsInitial.isInitialObj ((evaluation _ _).obj X) _ hF

noncomputable def IsInitial.functorComp
    [HasInitial D] {F : C ⥤ D} (hF : IsInitial F) (G : D ⥤ E)
    [PreservesColimit (Functor.empty.{0} D) G] :
    IsInitial (F ⋙ G) :=
  Functor.isInitial (fun X ↦ IsInitial.isInitialObj G _ (hF.obj X))

noncomputable def IsInitial.functorMapArrow [HasInitial D] {F : C ⥤ D} (hF : IsInitial F) :
    IsInitial F.mapArrow :=
  Functor.isInitial (fun _ ↦ Arrow.isInitial (hF.obj _) (hF.obj _))

end CategoryTheory.Limits

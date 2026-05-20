/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Reedy.Subfunctor.SubfunctorTwo

/-!
# External product of functors to types

-/

@[expose] public section

universe w₁ w₂

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ C₃ C₄ C₅ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Category* C₅]

@[simps]
def postcompose₂'ObjObj (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₄ ⥤ C₁) :
    (C₅ ⥤ C₂) ⥤ C₄ ⥤ C₅ ⥤ C₃ where
  obj H := G ⋙ F ⋙ (whiskeringLeft _ _ _).obj H
  map γ := whiskerLeft _ (whiskerLeft _ ((whiskeringLeft _ _ _).map γ))

@[simps]
-- better names? (we already have `Functor.postcompose₂`)
def postcompose₂'Obj (F : C₁ ⥤ C₂ ⥤ C₃) :
    (C₄ ⥤ C₁) ⥤ (C₅ ⥤ C₂) ⥤ C₄ ⥤ C₅ ⥤ C₃ where
  obj G := postcompose₂'ObjObj F G
  map β := { app H := whiskerRight β _ }

def postcompose₂' :
    (C₁ ⥤ C₂ ⥤ C₃) ⥤ (C₄ ⥤ C₁) ⥤ (C₅ ⥤ C₂) ⥤ C₄ ⥤ C₅ ⥤ C₃ where
  obj := postcompose₂'Obj
  map f := { app G := { app H := whiskerLeft _ (whiskerRight f _) } }

end Functor

variable {C D : Type*} [Category* C] [Category* D]

namespace TypeCat

@[simps]
def prod : Type w₁ ⥤ Type w₂ ⥤ Type max w₁ w₂ where
  obj X :=
    { obj Y := X × Y
      map g := ↾(fun z ↦ (z.1, g z.2)) }
  map f :=
    { app Y := ↾(fun z ↦ (f z.1, z.2)) }

end TypeCat

namespace FunctorToTypes

open Functor

abbrev externalProductFunctor :
    (C ⥤ Type w₁) ⥤ (D ⥤ Type w₂) ⥤ (C ⥤ D ⥤ Type max w₁ w₂) :=
  Functor.postcompose₂'Obj TypeCat.prod.{w₁, w₂}

abbrev externalProduct (F : C ⥤ Type w₁) (G : D ⥤ Type w₂) :
    C ⥤ D ⥤ Type max w₁ w₂ :=
  (externalProductFunctor.obj F).obj G

end FunctorToTypes

namespace Subfunctor

open FunctorToTypes

variable {F : C ⥤ Type w₁} {G : D ⥤ Type w₂}
  (A : Subfunctor F) (B : Subfunctor G)

def externalProd : Subfunctor₂ (externalProduct F G) where
  obj U V := Set.prod (A.obj U) (B.obj V)
  map₁ := sorry
  map₂ := sorry

-- this is an "external" version of `SSet.Subcomplex.unionProd`
def unionExternalProd : Subfunctor₂ (FunctorToTypes.externalProduct F G) :=
  externalProd ⊤ B ⊔ externalProd A ⊤

end Subfunctor

end CategoryTheory

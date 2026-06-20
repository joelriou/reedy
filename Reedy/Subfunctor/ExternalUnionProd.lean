/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Reedy.Subfunctor.SubfunctorTwo

/-!
# External product of functors to types

-/

@[expose] public section

universe w₁ w₂

@[simps]
def Set.prodEquiv {X Y : Type*} (A : Set X) (B : Set Y) :
    A.prod B ≃ A × B where
  toFun := fun x ↦ ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
  invFun := fun x ↦ ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩

namespace CategoryTheory

open Opposite

namespace Functor

variable {C₁ C₂ C₃ C₄ C₅ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Category* C₅]

@[simps]
def postcompose₂'ObjObj (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₄ ⥤ C₁) :
    (C₅ ⥤ C₂) ⥤ C₄ ⥤ C₅ ⥤ C₃ where
  obj H := G ⋙ F ⋙ (whiskeringLeft _ _ _).obj H
  map γ := whiskerLeft _ (whiskerLeft _ ((whiskeringLeft _ _ _).map γ))

set_option backward.defeqAttrib.useBackward true in
@[simps]
-- better names? (we already have `Functor.postcompose₂`)
def postcompose₂'Obj (F : C₁ ⥤ C₂ ⥤ C₃) :
    (C₄ ⥤ C₁) ⥤ (C₅ ⥤ C₂) ⥤ C₄ ⥤ C₅ ⥤ C₃ where
  obj G := postcompose₂'ObjObj F G
  map β := { app H := whiskerRight β _ }

set_option backward.defeqAttrib.useBackward true in
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

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] externalProduct in
def fromExternalProductCoyonedaObjOpYonedaObj (X : C) :
    externalProduct (coyoneda.obj (op X)) (yoneda.obj X) ⟶ yoneda where
  app T := { app S := ↾(fun x ↦ x.2 ≫ x.1) }

end FunctorToTypes

namespace Subfunctor

@[simps!]
def topIso (F : C ⥤ Type w) : (⊤ : Subfunctor F).toFunctor ≅ F :=
  NatIso.ofComponents (fun X ↦ (Equiv.Set.univ _).toIso)

open FunctorToTypes

variable {F : C ⥤ Type w₁} {G : D ⥤ Type w₂}
  (A : Subfunctor F) (B : Subfunctor G)

@[simps]
def externalProd : Subfunctor₂ (externalProduct F G) where
  obj U V := Set.prod (A.obj U) (B.obj V)
  map₁ _ _ _ h := ⟨A.map _ h.1, h.2⟩
  map₂ _ _ _ _ _ h := ⟨h.1, B.map _ h.2⟩

-- this is an "external" version of `SSet.Subcomplex.unionProd`
def unionExternalProd : Subfunctor₂ (FunctorToTypes.externalProduct F G) :=
  externalProd ⊤ B ⊔ externalProd A ⊤

set_option backward.defeqAttrib.useBackward true in
lemma unionExternalProd.bicartSq :
    Subfunctor₂.BicartSq (externalProd A B) (externalProd ⊤ B) (externalProd A ⊤)
      (unionExternalProd A B) where
  sup_eq := rfl
  inf_eq := by
    ext U V ⟨x, y⟩
    dsimp [Set.prod]
    simp only [Set.mem_univ, true_and, and_true, Set.mem_inter_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₂, h₁⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₂, h₁⟩

lemma mem_unionExternalProd_obj_obj_iff {U : C} {V : D}
    (x : ((externalProduct F G).obj U).obj V) :
    x ∈ (unionExternalProd A B).obj U V ↔ x.2 ∈ B.obj V ∨ x.1 ∈ A.obj U := by
  simp [unionExternalProd, externalProd, Set.prod]
  rfl

lemma notMem_unionExternalProd_obj_obj_iff {U : C} {V : D}
    (x : ((externalProduct F G).obj U).obj V) :
    x ∉ (unionExternalProd A B).obj U V ↔ x.2 ∉ B.obj V ∧ x.1 ∉ A.obj U := by
  simp [mem_unionExternalProd_obj_obj_iff]

set_option backward.defeqAttrib.useBackward true in
def unionExternalProd.ι₁ :
    (externalProductFunctor.obj F).obj B.toFunctor ⟶
      (A.unionExternalProd B).toFunctor :=
  Subfunctor₂.lift ((externalProductFunctor.obj F).map B.ι) (by
    rintro X Y _ ⟨⟨_, y⟩, rfl⟩
    rw [mem_unionExternalProd_obj_obj_iff]
    exact Or.inl y.prop)

def unionExternalProd.ι₂ :
    (externalProductFunctor.obj A.toFunctor).obj G ⟶
    (A.unionExternalProd B).toFunctor :=
  Subfunctor₂.lift ((externalProductFunctor.map A.ι).app G) (by
    rintro X Y _ ⟨⟨x, _⟩, rfl⟩
    rw [mem_unionExternalProd_obj_obj_iff]
    exact Or.inr x.prop)

def externalProdIso :
    (A.externalProd B).toFunctor ≅
      (externalProductFunctor.obj A.toFunctor).obj B.toFunctor :=
  NatIso.ofComponents (fun X ↦
    NatIso.ofComponents (fun Y ↦ (Set.prodEquiv _ _).toIso))

@[simps]
def pushoutObjObjExternalProductFunctor :
    externalProductFunctor.PushoutObjObj A.ι B.ι where
  pt := (A.unionExternalProd B).toFunctor
  inl := unionExternalProd.ι₁ _ _
  inr := unionExternalProd.ι₂ _ _
  isPushout :=
    (unionExternalProd.bicartSq A B).isPushout.of_iso
      (externalProdIso A B)
      ((externalProdIso ⊤ B) ≪≫
        (externalProductFunctor.mapIso (topIso F)).app _)
      ((externalProdIso A ⊤) ≪≫
        (externalProductFunctor.obj _).mapIso (topIso G)) (Iso.refl _)
      rfl rfl rfl rfl
  ι := (A.unionExternalProd B).ι

end Subfunctor

end CategoryTheory

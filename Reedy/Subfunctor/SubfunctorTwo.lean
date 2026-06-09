/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Simon Henry
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Subfunctors of bifuntors to types

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D ⥤ Type w)

@[ext]
structure Subfunctor₂ where
  obj (U : C) (V : D) : Set ((F.obj U).obj V)
  map₁ {U₁ U₂ : C} (f : U₁ ⟶ U₂) (V : D) : obj U₁ V ⊆ ((F.map f).app V) ⁻¹' obj U₂ V
  map₂ (U : C) {V₁ V₂ : D} (g : V₁ ⟶ V₂) : obj U V₁ ⊆ ((F.obj U).map g) ⁻¹' obj U V₂

/-
* define a functor `Subfunctor₂ F ⥤ (C ⥤ D ⥤ Type w)` and show that it commutes
    with filtered colimits (this is similar to the result in the file
    `AlgebraicTopology.SimplicialSet.SubcomplexEvaluation`)
* more API which was developped only in the particular case `SSet.Subcomplex`
  (`AlgebraicTopology.SimplicialSet.Subcomplex`) should be generalized to `Subfunctor/Subfunctor₂`
-/

instance : PartialOrder (Subfunctor₂ F) :=
  PartialOrder.lift Subfunctor₂.obj (fun _ _ ↦ Subfunctor₂.ext)

-- claim https://github.com/joelriou/reedy/issues/13 when working on this
-- the proofs should be similar to the similar definition in `CategoryTheory.Subfunctor.Basic`
instance : CompleteLattice (Subfunctor₂ F) where
  sup F G :=
    { obj U V := F.obj U V ⊔ G.obj U V
      map₁ := sorry
      map₂ := sorry }
  le_sup_left := sorry
  le_sup_right := sorry
  sup_le := sorry
  inf S T :=
    { obj U V := S.obj U V ⊓ T.obj U V
      map₁ := sorry
      map₂ := sorry }
  inf_le_left := sorry
  inf_le_right := sorry
  le_inf := sorry
  sSup S :=
    { obj U V := sSup (Set.image (fun T ↦ T.obj U V) S)
      map₁ := sorry
      map₂ := sorry }
  isLUB_sSup _ := sorry
  sInf S :=
    { obj U V := sInf (Set.image (fun T ↦ T.obj U V) S)
      map₁ := sorry
      map₂ := sorry }
  isGLB_sInf _ := sorry
  bot :=
    { obj U V := ∅
      map₂ := by simp
      map₁ := by simp }
  bot_le := sorry
  top :=
    { obj U V := Set.univ
      map₁ := by simp
      map₂ := by simp }
  le_top := sorry

namespace Subfunctor₂

@[simp] lemma top_obj (U : C) (V : D) : (⊤ : Subfunctor₂ F).obj U V = ⊤ := rfl
@[simp] lemma bot_obj (U : C) (V : D) : (⊥ : Subfunctor₂ F).obj U V = ⊥ := rfl

variable {F}

lemma sSup_obj (S : Set (Subfunctor₂ F)) (U : C) (V : D) :
    (sSup S).obj U V = sSup (Set.image (fun T ↦ T.obj U V) S) := rfl

@[simp]
lemma iSup_obj {ι : Sort*} (S : ι → Subfunctor₂ F) (U : C) (V : D) :
    (⨆ i, S i).obj U V = ⋃ i, (S i).obj U V := by
  simp [iSup, sSup_obj]

@[simps]
def eval₁ (A : Subfunctor₂ F) (U : C) : Subfunctor (F.obj U) where
  obj V := A.obj U V
  map _ := A.map₂ _ _

@[simps]
def eval₂ (A : Subfunctor₂ F) (V : D) : Subfunctor (F.flip.obj V) where
  obj U := A.obj U V
  map _ := A.map₁ _ _

@[simps]
def toFunctor (A : Subfunctor₂ F) : C ⥤ D ⥤ Type w where
  obj U :=
    { obj V := A.obj U V
      map g := ↾(fun x ↦ ⟨(F.obj _).map g x, A.map₂ _ _ x.prop⟩) }
  map f :=
    { app V := ↾(fun x ↦ ⟨(F.map f).app _ x, A.map₁ _ _ x.prop⟩) }

@[simps]
def ι (A : Subfunctor₂ F) : A.toFunctor ⟶ F where
  app U := { app V := ↾Subtype.val }

variable (F) in
@[simps]
def toFunctorFunctor : Subfunctor₂ F ⥤ C ⥤ D ⥤ Type w where
  obj := toFunctor
  map f := { app U := { app V := ↾(fun x ↦ ⟨x.val, leOfHom f _ _ x.prop⟩) } }

section

variable {A₁ A₂ : Subfunctor₂ F}

@[simps]
def homOfLE (h : A₁ ≤ A₂) : A₁.toFunctor ⟶ A₂.toFunctor where
  app U := { app V := ↾fun x ↦ ⟨x.val, h _ _ x.prop⟩ }

@[simps]
protected def eqToIso (h : A₁ = A₂) : A₁.toFunctor ≅ A₂.toFunctor where
  hom := homOfLE h.le
  inv := homOfLE h.symm.le

end

end Subfunctor₂

end CategoryTheory

/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Simon Henry, Yun Liu
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
  (F G : C ⥤ D ⥤ Type w)

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
      map₁ := by
        rintro U₁ U₂ f V x (h | h)
        · exact Or.inl (F.map₁ f V h)
        · exact Or.inr (G.map₁ f V h)
      map₂ := by
        rintro U V₁ V₂ g x (h | h)
        · exact Or.inl (F.map₂ U g h)
        · exact Or.inr (G.map₂ U g h) }
  le_sup_left _ _ _ _ := by simp
  le_sup_right _ _ _ _ := by simp
  sup_le _ _ _ h₁ h₂ _ _ := by
    rintro x (h | h)
    · exact h₁ _ _ h
    · exact h₂ _ _ h
  inf S T :=
    { obj U V := S.obj U V ⊓ T.obj U V
      map₁ := by
        rintro U₁ U₂ f V x h
        exact ⟨S.map₁ f V h.1, T.map₁ f V h.2⟩
      map₂ := by
        rintro U V₁ V₂ g x h
        exact ⟨S.map₂ U g h.1, T.map₂ U g h.2⟩ }
  inf_le_left _ _ _ _ _ h := h.1
  inf_le_right _ _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ := by
    intro U V x hx
    exact ⟨h₁ _ _ hx, h₂ _ _ hx⟩
  sSup S :=
    { obj U V := sSup (Set.image (fun T ↦ T.obj U V) S)
      map₁ := by
        rintro U₁ U₂ f V x hx
        obtain ⟨_, ⟨W, h, rfl⟩, h'⟩ := hx
        simp only [Set.sSup_eq_sUnion, Set.sUnion_image, Set.preimage_iUnion,
          Set.mem_iUnion, Set.mem_preimage, exists_prop]
        exact ⟨_, h, W.map₁ f V h'⟩
      map₂ := by
        rintro U V₁ V₂ g x hx
        obtain ⟨_, ⟨W, h, rfl⟩, h'⟩ := hx
        simp only [Set.sSup_eq_sUnion, Set.sUnion_image, Set.preimage_iUnion,
          Set.mem_iUnion, Set.mem_preimage, exists_prop]
        exact ⟨_, h, W.map₂ U g h'⟩ }
  isLUB_sSup _ := by
    refine ⟨fun T hT U V x hx => ?_, fun b hb U V x hx => ?_⟩
    · exact ⟨_, ⟨T, hT, rfl⟩, hx⟩
    · obtain ⟨_, ⟨T, hT, rfl⟩, h'⟩ := hx
      exact hb hT _ _ h'
  sInf S :=
    { obj U V := sInf (Set.image (fun T ↦ T.obj U V) S)
      map₁ := by
        rintro U₁ U₂ f V x hx _ ⟨W, hW, rfl⟩
        exact W.map₁ f V (hx _ ⟨W, hW, rfl⟩)
      map₂ := by
        rintro U V₁ V₂ g x hx _ ⟨W, hW, rfl⟩
        exact W.map₂ U g (hx _ ⟨W, hW, rfl⟩) }
  isGLB_sInf _ := by
    refine ⟨fun T hT U V x hx => ?_, fun b hb U V x hx => ?_⟩
    · exact hx _ ⟨T, hT, rfl⟩
    · rintro _ ⟨T, hT, rfl⟩
      exact hb hT _ _ hx
  bot :=
    { obj U V := ∅
      map₁ := by simp
      map₂ := by simp }
  bot_le _ _ _ := bot_le
  top :=
    { obj U V := Set.univ
      map₁ := by simp
      map₂ := by simp }
  le_top _ _ _ := le_top

namespace Subfunctor₂

@[simp] lemma top_obj (U : C) (V : D) : (⊤ : Subfunctor₂ F).obj U V = ⊤ := rfl
@[simp] lemma bot_obj (U : C) (V : D) : (⊥ : Subfunctor₂ F).obj U V = ⊥ := rfl

variable {F}

lemma sSup_obj (S : Set (Subfunctor₂ F)) (U : C) (V : D) :
    (sSup S).obj U V = sSup (Set.image (fun T ↦ T.obj U V) S) := rfl

lemma sInf_obj (S : Set (Subfunctor₂ F)) (U : C) (V : D) :
    (sInf S).obj U V = sInf (Set.image (fun T ↦ T.obj U V) S) := rfl

@[simp]
lemma iSup_obj {ι : Sort*} (S : ι → Subfunctor₂ F) (U : C) (V : D) :
    (⨆ i, S i).obj U V = ⋃ i, (S i).obj U V := by
  simp [iSup, sSup_obj]

@[simp]
lemma iInf_obj {ι : Sort*} (S : ι → Subfunctor₂ F) (U : C) (V : D) :
    (⨅ i, S i).obj U V = ⋂ i, (S i).obj U V := by
  simp [iInf, sInf_obj]

@[simp]
lemma max_obj (S T : Subfunctor₂ F) (U : C) (V : D) :
    (S ⊔ T).obj U V = S.obj U V ∪ T.obj U V := rfl

@[simp]
lemma min_obj (S T : Subfunctor₂ F) (U : C) (V : D) :
    (S ⊓ T).obj U V = S.obj U V ∩ T.obj U V := rfl

lemma max_min (S₁ S₂ T : Subfunctor₂ F) :
    (S₁ ⊔ S₂) ⊓ T = (S₁ ⊓ T) ⊔ (S₂ ⊓ T) := by
  aesop

lemma iSup_min {ι : Sort*} (S : ι → Subfunctor₂ F) (T : Subfunctor₂ F) :
    (⨆ i, S i) ⊓ T = ⨆ i, S i ⊓ T := by
  aesop

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

open ConcreteCategory in
instance (A : Subfunctor₂ F) : Mono A.ι :=
  ⟨@fun _ _ _ e =>
    NatTrans.ext <| funext fun U => NatTrans.ext <| funext fun V =>
      hom_ext _ _ fun x => Subtype.ext <|
        congr_hom (congr_app (congr_app e U) V) x⟩

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

-- claim https://github.com/joelriou/reedy/issues/14
-- if you work on the following proofs
section

variable {G} (f : F ⟶ G)
@[simps]
def range : Subfunctor₂ G where
  obj U V := Set.range ((f.app U).app V)
  map₁ := sorry
  map₂ := sorry

variable (F) in
lemma range_id : range (𝟙 F) = ⊤ := by aesop

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma range_ι (G : Subfunctor₂ F) : range G.ι = G := by aesop

/-- The morphism `G ⟶ Subfunctor₂.range f` induced by `f : F ⟶ G`. -/
abbrev toRange : F ⟶ (Subfunctor₂.range f).toFunctor where
  app U := { app V := ↾(fun x ↦ ⟨(f.app _).app _ x, _, rfl⟩) }
  naturality := sorry

@[simp, reassoc]
lemma toRange_ι : toRange f ≫ (Subfunctor₂.range f).ι = f := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma toRange_app_val {U : C} {V : D} (x : (F.obj U).obj V) :
    dsimp% (((toRange f).app U).app V x).val = (f.app U).app V x := rfl

instance : Epi (toRange f) := sorry

instance [Mono f] : Mono (toRange f) :=
  mono_of_mono_fac (toRange_ι f)

instance [Mono f] : IsIso (toRange f) :=
  sorry

lemma range_eq_top_iff : Subfunctor₂.range f = ⊤ ↔ Epi f := by
  sorry

lemma range_eq_top [Epi f] : Subfunctor₂.range f = ⊤ := by
  rwa [range_eq_top_iff]

end

section

variable {G} (f : F ⟶ G) {B : Subfunctor₂ G} (hf : range f ≤ B)

def lift : F ⟶ B.toFunctor where
  app U := { app V := ↾(fun x ↦ ⟨(f.app _ ).app _ x, hf _ _ ⟨_, rfl⟩ ⟩) }
  naturality := sorry

@[reassoc (attr := simp)]
lemma lift_ι : lift f hf ≫ B.ι = f := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma lift_app_coe {U : C} {V : D} (x : (F.obj U).obj V) :
    dsimp% (((lift f hf).app _).app _ x).1 = (f.app _).app _ x := rfl

end

section

variable (F)

@[simps! inv_app_app_hom_apply]
def topIso : ((⊤ : Subfunctor₂ F).toFunctor) ≅ F :=
  NatIso.ofComponents
    (fun U ↦ NatIso.ofComponents (fun V ↦
      (Equiv.Set.univ ((F.obj U).obj V)).toIso))

@[simp]
lemma topIso_hom : (topIso F).hom = Subfunctor₂.ι _ := rfl

@[reassoc (attr := simp)]
lemma topIso_inv_ι : (topIso F).inv ≫ Subfunctor₂.ι _ = 𝟙 _ := rfl

end

end Subfunctor₂

end CategoryTheory

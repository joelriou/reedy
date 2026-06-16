/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# Triple pushouts

-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C]

namespace MultispanShape

@[simps]
def pushout₃ : MultispanShape where
  L := Fin 3
  R := Fin 3
  fst
    | 0 => 1
    | 1 => 0
    | 2 => 0
  snd
    | 0 => 2
    | 1 => 2
    | 2 => 1

end MultispanShape

namespace MultispanIndex

variable {zero one two zero' one' two' : C}
  (f₀ : zero' ⟶ one) (g₀ : zero' ⟶ two)
  (f₁ : one' ⟶ zero) (g₁ : one' ⟶ two)
  (f₂ : two' ⟶ zero) (g₂ : two' ⟶ one)

@[simps]
def pushout₃ : MultispanIndex .pushout₃ C where
  left (x : Fin 3) := match x with
    | 0 => zero'
    | 1 => one'
    | 2 => two'
  right (x : Fin 3) := match x with
    | 0 => zero
    | 1 => one
    | 2 => two
  fst (x : Fin 3) := match x with
    | 0 => f₀
    | 1 => f₁
    | 2 => f₂
  snd (x : Fin 3) := match x with
    | 0 => g₀
    | 1 => g₁
    | 2 => g₂

end MultispanIndex

section

variable {zero one two zero' one' two' : C}
  {f₀ : zero' ⟶ one} {g₀ : zero' ⟶ two}
  {f₁ : one' ⟶ zero} {g₁ : one' ⟶ two}
  {f₂ : two' ⟶ zero} {g₂ : two' ⟶ one}

variable (f₀ g₀ f₁ g₁ f₂ g₂) in
abbrev PushoutCocone₃ := Multicofork (.pushout₃ f₀ g₀ f₁ g₁ f₂ g₂)

namespace PushoutCocone₃

section

variable (c : PushoutCocone₃ f₀ g₀ f₁ g₁ f₂ g₂)

abbrev ι₀ : zero ⟶ c.pt := Multicofork.π c (0 : Fin 3)
abbrev ι₁ : one ⟶ c.pt := Multicofork.π c (1 : Fin 3)
abbrev ι₂ : two ⟶ c.pt := Multicofork.π c (2 : Fin 3)

@[reassoc] lemma w₀ : f₀ ≫ c.ι₁ = g₀ ≫ c.ι₂ := Multicofork.condition c (0 : Fin 3)
@[reassoc] lemma w₁ : f₁ ≫ c.ι₀ = g₁ ≫ c.ι₂ := Multicofork.condition c (1 : Fin 3)
@[reassoc] lemma w₂ : f₂ ≫ c.ι₀ = g₂ ≫ c.ι₁ := Multicofork.condition c (2 : Fin 3)

end

variable {pt : C} (i₀ : zero ⟶ pt) (i₁ : one ⟶ pt) (i₂ : two ⟶ pt)

abbrev mk (fac₀ : f₀ ≫ i₁ = g₀ ≫ i₂ := by cat_disch)
    (fac₁ : f₁ ≫ i₀ = g₁ ≫ i₂ := by cat_disch)
    (fac₂ : f₂ ≫ i₀ = g₂ ≫ i₁ := by cat_disch) :
    PushoutCocone₃ f₀ g₀ f₁ g₁ f₂ g₂ :=
  Multicofork.ofπ _ pt
    (fun (x : Fin 3) ↦ match x with
      | 0 => i₀
      | 1 => i₁
      | 2 => i₂)
    (fun (x : Fin 3) ↦ match x with
      | 0 => fac₀
      | 1 => fac₁
      | 2 => fac₂)

@[simp]
lemma mk_ι₀ (fac₀ : f₀ ≫ i₁ = g₀ ≫ i₂ := by cat_disch)
    (fac₁ : f₁ ≫ i₀ = g₁ ≫ i₂ := by cat_disch)
    (fac₂ : f₂ ≫ i₀ = g₂ ≫ i₁ := by cat_disch) :
    (mk i₀ i₁ i₂ fac₀ fac₁ fac₂).ι₀ = i₀ := rfl

@[simp]
lemma mk_ι₁ (fac₀ : f₀ ≫ i₁ = g₀ ≫ i₂ := by cat_disch)
    (fac₁ : f₁ ≫ i₀ = g₁ ≫ i₂ := by cat_disch)
    (fac₂ : f₂ ≫ i₀ = g₂ ≫ i₁ := by cat_disch) :
    (mk i₀ i₁ i₂ fac₀ fac₁ fac₂).ι₁ = i₁ := rfl

@[simp]
lemma mk_ι₂ (fac₀ : f₀ ≫ i₁ = g₀ ≫ i₂ := by cat_disch)
    (fac₁ : f₁ ≫ i₀ = g₁ ≫ i₂ := by cat_disch)
    (fac₂ : f₂ ≫ i₀ = g₂ ≫ i₁ := by cat_disch) :
    (mk i₀ i₁ i₂ fac₀ fac₁ fac₂).ι₂ = i₂ := rfl

namespace IsColimit

variable {c : PushoutCocone₃ f₀ g₀ f₁ g₁ f₂ g₂}

lemma hom_ext (hc : IsColimit c) {T : C} {f g : c.pt ⟶ T} (h₀ : c.ι₀ ≫ f = c.ι₀ ≫ g)
    (h₁ : c.ι₁ ≫ f = c.ι₁ ≫ g) (h₂ : c.ι₂ ≫ f = c.ι₂ ≫ g) :
    f = g :=
  Multicofork.IsColimit.hom_ext hc (fun (x : Fin 3) ↦ match x with
    | 0 => h₀
    | 1 => h₁
    | 2 => h₂)

noncomputable def mk (h₁ : ∀ ⦃T : C⦄ (f g : c.pt ⟶ T), c.ι₀ ≫ f = c.ι₀ ≫ g →
    c.ι₁ ≫ f = c.ι₁ ≫ g → c.ι₂ ≫ f = c.ι₂ ≫ g → f = g)
    (h₂ : ∀ ⦃T : C⦄ (p₀ : zero ⟶ T) (p₁ : one ⟶ T) (p₂ : two ⟶ T),
      f₀ ≫ p₁ = g₀ ≫ p₂ → f₁ ≫ p₀ = g₁ ≫ p₂ → f₂ ≫ p₀ = g₂ ≫ p₁ →
      ∃ (f : c.pt ⟶ T), c.ι₀ ≫ f = p₀ ∧ c.ι₁ ≫ f = p₁ ∧ c.ι₂ ≫ f = p₂) :
    IsColimit c := Nonempty.some (by
  choose l hl₀ hl₁ hl₂ using
    fun (s : PushoutCocone₃ f₀ g₀ f₁ g₁ f₂ g₂) ↦ h₂ s.ι₀ s.ι₁ s.ι₂ s.w₀ s.w₁ s.w₂
  refine ⟨Multicofork.IsColimit.mk _ l
    (fun s (i : Fin 3) ↦ match i with
      | 0 => hl₀ _
      | 1 => hl₁ _
      | 2 => hl₂ _) (fun s m hm ↦ ?_)⟩
  exact h₁ _ _
    ((hm (0 : Fin 3)).trans (hl₀ _).symm)
    ((hm (1 : Fin 3)).trans (hl₁ _).symm)
    ((hm (2 : Fin 3)).trans (hl₂ _).symm))

end IsColimit

end PushoutCocone₃

end

variable {zero one two zero' one' two' pt : C}
  (f₀ : zero' ⟶ one) (g₀ : zero' ⟶ two)
  (f₁ : one' ⟶ zero) (g₁ : one' ⟶ two)
  (f₂ : two' ⟶ zero) (g₂ : two' ⟶ one)
  (i₀ : zero ⟶ pt) (i₁ : one ⟶ pt) (i₂ : two ⟶ pt)

structure IsPushout₃ : Prop where
  w₀ : f₀ ≫ i₁ = g₀ ≫ i₂ := by cat_disch
  w₁ : f₁ ≫ i₀ = g₁ ≫ i₂ := by cat_disch
  w₂ : f₂ ≫ i₀ = g₂ ≫ i₁ := by cat_disch
  nonempty_isColimit : Nonempty (IsColimit (PushoutCocone₃.mk _ _ _ w₀ w₁ w₂))

namespace IsPushout₃

variable {f₀ g₀ f₁ g₁ f₂ g₂ i₀ i₁ i₂} (sq₃ : IsPushout₃ f₀ g₀ f₁ g₁ f₂ g₂ i₀ i₁ i₂)

abbrev pushoutCocone₃ : PushoutCocone₃ f₀ g₀ f₁ g₁ f₂ g₂ :=
  PushoutCocone₃.mk _ _ _ sq₃.w₀ sq₃.w₁ sq₃.w₂

@[no_expose]
noncomputable def isColimit : IsColimit sq₃.pushoutCocone₃ :=
  sq₃.nonempty_isColimit.some

include sq₃ in
lemma hom_ext {T : C} {f g : pt ⟶ T} (h₀ : i₀ ≫ f = i₀ ≫ g)
    (h₁ : i₁ ≫ f = i₁ ≫ g) (h₂ : i₂ ≫ f = i₂ ≫ g) : f = g :=
  PushoutCocone₃.IsColimit.hom_ext sq₃.isColimit h₀ h₁ h₂

section

variable {T : C} (p₀ : zero ⟶ T) (p₁ : one ⟶ T) (p₂ : two ⟶ T)

noncomputable def desc
    (w₀ : f₀ ≫ p₁ = g₀ ≫ p₂ := by cat_disch)
    (w₁ : f₁ ≫ p₀ = g₁ ≫ p₂ := by cat_disch)
    (w₂ : f₂ ≫ p₀ = g₂ ≫ p₁ := by cat_disch) :
    pt ⟶ T :=
  sq₃.isColimit.desc (PushoutCocone₃.mk p₀ p₁ p₂ w₀ w₁ w₂)

@[reassoc (attr := simp)]
lemma fac₀ (w₀ : f₀ ≫ p₁ = g₀ ≫ p₂ := by cat_disch)
    (w₁ : f₁ ≫ p₀ = g₁ ≫ p₂ := by cat_disch)
    (w₂ : f₂ ≫ p₀ = g₂ ≫ p₁ := by cat_disch) :
    i₀ ≫ sq₃.desc p₀ p₁ p₂ w₀ w₁ w₂ = p₀ :=
  sq₃.isColimit.fac (PushoutCocone₃.mk p₀ p₁ p₂ w₀ w₁ w₂) (.right (0 : Fin 3))

@[reassoc (attr := simp)]
lemma fac₁ (w₀ : f₀ ≫ p₁ = g₀ ≫ p₂ := by cat_disch)
    (w₁ : f₁ ≫ p₀ = g₁ ≫ p₂ := by cat_disch)
    (w₂ : f₂ ≫ p₀ = g₂ ≫ p₁ := by cat_disch) :
    i₁ ≫ sq₃.desc p₀ p₁ p₂ w₀ w₁ w₂ = p₁ :=
  sq₃.isColimit.fac (PushoutCocone₃.mk p₀ p₁ p₂ w₀ w₁ w₂) (.right (1 : Fin 3))

@[reassoc (attr := simp)]
lemma fac₂ (w₀ : f₀ ≫ p₁ = g₀ ≫ p₂ := by cat_disch)
    (w₁ : f₁ ≫ p₀ = g₁ ≫ p₂ := by cat_disch)
    (w₂ : f₂ ≫ p₀ = g₂ ≫ p₁ := by cat_disch) :
    i₂ ≫ sq₃.desc p₀ p₁ p₂ w₀ w₁ w₂ = p₂ :=
  sq₃.isColimit.fac (PushoutCocone₃.mk p₀ p₁ p₂ w₀ w₁ w₂) (.right (2 : Fin 3))

include sq₃ in
lemma exists_desc (w₀ : f₀ ≫ p₁ = g₀ ≫ p₂ := by cat_disch)
    (w₁ : f₁ ≫ p₀ = g₁ ≫ p₂ := by cat_disch)
    (w₂ : f₂ ≫ p₀ = g₂ ≫ p₁ := by cat_disch) :
    ∃ (l : pt ⟶ T), i₀ ≫ l = p₀ ∧ i₁ ≫ l = p₁ ∧ i₂ ≫ l = p₂ :=
  ⟨sq₃.desc p₀ p₁ p₂, by simp⟩

end

end IsPushout₃

end CategoryTheory.Limits

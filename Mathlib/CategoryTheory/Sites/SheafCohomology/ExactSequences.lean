/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# API for the long exact sequence for sheaf cohomology

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w' w v u

namespace CategoryTheory

open Abelian AddCommGrpCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable (C) in
/-- The category of short exact sequences -/
abbrev ShortExactSequences [Limits.HasZeroMorphisms C] :=
    ObjectProperty.FullSubcategory (ShortComplex.ShortExact (C := C))

namespace Sheaf

variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] (n : ℕ)

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) (n₀ : ℕ)
    (n₁ : ℕ := n₀ + 1)

namespace H

/-- The connecting homomorphism from `Hⁿ(S.X₃)` to `Hⁿ⁺¹(S.X₁)` -/
noncomputable def connectingHom (h : n₀ + 1 = n₁ := by omega) : H S.X₃ n₀ →+ H S.X₁ n₁ :=
  hS.extClass.postcomp _ h

variable {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem connectingHom_naturality (h : n₀ + 1 = n₁ := by omega) (x : H S₁.X₃ n₀) :
    connectingHom h₂ n₀ n₁ h (map f.τ₃ n₀ x) = map f.τ₁ n₁ (connectingHom h₁ n₀ n₁ h x) := by
  delta connectingHom H map
  simp [ShortComplex.ShortExact.extClass_naturality h₁ h₂ f]

/-- The long exact sequence on sheaf cohomology. -/
noncomputable def longSequence (h : n₀ + 1 = n₁ := by omega) :
    ComposableArrows AddCommGrpCat.{w'} 5 := ComposableArrows.mk₅
  (ofHom (H.map S.f n₀))
  (ofHom (H.map S.g n₀))
  (ofHom (H.connectingHom hS n₀ n₁ h))
  (ofHom (H.map S.f n₁))
  (ofHom (H.map S.g n₁))

theorem longSequence_exact (h : n₀ + 1 = n₁ := by omega) : (longSequence hS n₀ n₁ h).Exact :=
  Ext.covariantSequence_exact _ hS n₀ n₁ h

/-- The induced homomorphism of long exact equences -/
noncomputable def longSequence_hom (h : n₀ + 1 = n₁ := by omega) :
    longSequence h₁ n₀ n₁ h ⟶ longSequence h₂ n₀ n₁ h := ComposableArrows.homMk₅
  (ofHom (map f.τ₁ n₀))
  (ofHom (map f.τ₂ n₀))
  (ofHom (map f.τ₃ n₀))
  (ofHom (map f.τ₁ n₁))
  (ofHom (map f.τ₂ n₁))
  (ofHom (map f.τ₃ n₁))
  (by
    have := congr_arg (functorH J n₀).map f.4
    repeat rw [Functor.map_comp] at this
    exact this.symm)
  (by
    have := congr_arg (functorH J n₀).map f.5
    repeat rw [Functor.map_comp] at this
    exact this.symm)
  (by
    ext x
    simpa using (connectingHom_naturality n₀ n₁ h₁ h₂ f h x).symm)
  (by
    have := congr_arg (functorH J n₁).map f.4
    repeat rw [Functor.map_comp] at this
    exact this.symm)
  (by
    have := congr_arg (functorH J n₁).map f.5
    repeat rw [Functor.map_comp] at this
    exact this.symm)

@[simp]
lemma longSequence_hom_app_zero (h : n₀ + 1 = n₁ := by omega) :
  (longSequence_hom n₀ n₁ h₁ h₂ f).app 0 = ofHom (map f.τ₁ n₀) := rfl

@[simp]
lemma longSequence_hom_app_one (h : n₀ + 1 = n₁ := by omega) :
  (longSequence_hom n₀ n₁ h₁ h₂ f).app 1 = ofHom (map f.τ₂ n₀) := rfl

@[simp]
lemma longSequence_hom_app_two (h : n₀ + 1 = n₁ := by omega) :
  (longSequence_hom n₀ n₁ h₁ h₂ f).app 2 = ofHom (map f.τ₃ n₀) := rfl

@[simp]
lemma longSequence_hom_app_three (h : n₀ + 1 = n₁ := by omega) :
  (longSequence_hom n₀ n₁ h₁ h₂ f).app 3 = ofHom (map f.τ₁ n₁) := rfl

@[simp]
lemma longSequence_hom_app_four (h : n₀ + 1 = n₁ := by omega) :
  (longSequence_hom n₀ n₁ h₁ h₂ f).app 4 = ofHom (map f.τ₂ n₁) := rfl

@[simp]
lemma longSequence_hom_app_five (h : n₀ + 1 = n₁ := by omega) :
  (longSequence_hom n₀ n₁ h₁ h₂ f).app 5 = ofHom (map f.τ₃ n₁) := rfl

/-- The long exact sequence of cohomology is functorial -/
@[simps]
noncomputable def longSequenceFunctor (h : n₀ + 1 = n₁ := by omega) :
    ShortExactSequences (Sheaf J AddCommGrpCat.{w}) ⥤ ComposableArrows AddCommGrpCat.{w'} 5 where
      obj S := longSequence S.property n₀ n₁ h
      map {S₁ S₂} f := longSequence_hom n₀ n₁ S₁.property S₂.property f.hom h
      map_id S := by
        ext x
        any_goals convert map_id_apply x
      map_comp _ _ := by
        ext x
        any_goals convert map_comp_apply _ _ x

lemma longSequence_exact₁' (h : n₀ + 1 = n₁ := by omega) :
    (ShortComplex.mk (ofHom (H.connectingHom hS n₀ n₁ h)) (ofHom (H.map S.f n₁)) (by
      convert ((longSequence_exact hS n₀ n₁ h).sc 2).zero)).Exact := by
  convert (longSequence_exact hS n₀ n₁ h).exact 2

lemma longSequence_exact₃' (h : n₀ + 1 = n₁ := by omega) :
    (ShortComplex.mk (ofHom (H.map S.g n₀)) (ofHom (H.connectingHom hS n₀ n₁ h)) (by
      convert ((longSequence_exact hS n₀ n₁ h).sc 1).zero)).Exact := by
  convert (longSequence_exact hS n₀ n₁ h).exact 1

lemma longSequence_exact₂' (n : ℕ) :
    (ShortComplex.mk (ofHom (H.map S.f n)) (ofHom (H.map S.g n)) (by
      convert ((longSequence_exact hS n).sc 0).zero)).Exact := by
  convert (longSequence_exact hS n).exact 0

include hS in
lemma longSequence_exact₂ (x₂ : H S.X₂ n) (hx₂ : H.map S.g n x₂ = 0) :
    ∃ x₁ : H S.X₁ n, H.map S.f n x₁ = x₂ := by
  have := longSequence_exact₂' hS n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂

lemma longSequence_exact₃ (h : n₀ + 1 = n₁ := by omega) (x₃ : H S.X₃ n₀)
    (hx₃ : H.connectingHom hS n₀ n₁ h x₃ = 0) :
    ∃ x₂ : H S.X₂ n₀, H.map S.g n₀ x₂ = x₃ := by
  have := longSequence_exact₃' hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃

lemma longSequence_exact₁ (h : n₀ + 1 = n₁ := by omega) (x₁ : H S.X₁ n₁)
    (hx₁ : H.map S.f n₁ x₁ = 0) :
    ∃ x₃ : H S.X₃ n₀, H.connectingHom hS n₀ n₁ h x₃ = x₁ := by
  have := longSequence_exact₁' hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

variable {T : C} (hT : Limits.IsTerminal T)

open Opposite

lemma longSequence_equiv₀_exact₃ (x₃ : S.X₃.obj.obj (op T))
    (hx₃ : (H.connectingHom hS 0 1) ((H.equiv₀ S.X₃ hT).symm x₃) = 0) :
    ∃ x₂ : S.X₂.obj.obj (op T), S.g.hom.app (op T) x₂ = x₃ := by
  obtain ⟨x₂', hx₂'⟩ := longSequence_exact₃ hS 0 _ _ ((H.equiv₀ S.X₃ hT).symm x₃) hx₃
  use H.equiv₀ S.X₂ hT x₂'
  simp [H.equiv₀_naturality, hx₂']

end H

end Sheaf

end CategoryTheory

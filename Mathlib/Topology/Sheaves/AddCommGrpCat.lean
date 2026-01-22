/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
Results for sheaves of abelian groups on topological spaces.

-/

@[expose] public section

universe u

noncomputable section

open TopCat TopologicalSpace Opposite CategoryTheory AlgebraicGeometry TopCat.Sheaf TopCat.Presheaf

namespace TopCat

variable {X : TopCat.{u}} {U V : Opens X}

instance : Abelian (Sheaf AddCommGrpCat X) := sheafIsAbelian

instance : (forget AddCommGrpCat X).Additive where

theorem Presheaf.addCommGrpCat_shortExact_app_zero {S : ShortComplex (Presheaf AddCommGrpCat.{u} X)}
    {s : S.X₂.obj (op U)} (h : S.g.app (op U) s = 0) (hS : S.Exact) :
    ∃(t : S.X₁.obj (op U)), S.f.app (op U) t = s := by
  dsimp [Presheaf] at S
  let F := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  apply (ShortComplex.ab_exact_iff (S.map F)).mp
  · have := ((Functor.exact_tfae F).out 1 3).mpr
    exact this ⟨inferInstance, inferInstance⟩ S hS
  exact h

namespace Sheaf.AddCommGrpCat

abbrev Γ (U : Opens X) := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op U)

lemma Γ.map_app {F G : Sheaf AddCommGrpCat X} (g : F ⟶ G) :
    (Γ U).map g = g.val.app (op U) := rfl

lemma restrict_sum {F : Sheaf AddCommGrpCat X} (h : V ≤ U) (s t : F.val.obj (op U)) :
    (s + t) |_ V = s |_V + t |_V := by
  delta Presheaf.restrictOpen Presheaf.restrict
  aesop_cat

variable {S : ShortComplex (Sheaf AddCommGrpCat X)}

lemma shortExact_app_zero {S : ShortComplex (Sheaf AddCommGrpCat X)} (s : S.X₂.val.obj (op U))
    (h : S.g.val.app (op U) s = 0) (hS : S.ShortExact) :
    ∃(t : S.X₁.val.obj (op U)), S.f.val.app (op U) t = s := by
  have := ((Functor.preservesFiniteLimits_tfae (forget AddCommGrpCat X)).out 1 3).mpr
    (inferInstanceAs (Limits.PreservesFiniteLimits (forget AddCommGrpCat X)))
  exact Presheaf.addCommGrpCat_shortExact_app_zero h (this S ⟨hS.1, hS.2⟩).left

/- If sf is a family of sections, and each section maps to t via f : F ⟶ G, then when we glue
  sf together to form s, s is also mapped to t via f. -/
lemma isGluing_app_of_forall_eq {F G : Sheaf AddCommGrpCat X} {f : F ⟶ G} {ι : Type*}
    {U : ι → Opens X} {sf : ∀ i : ι, F.val.obj (op (U i))} {s : F.val.obj (op (iSup U))}
    (h : IsGluing F.val U sf s) {V : Opens X} {t : G.val.obj (op V)} (hV : ∀ i : ι, U i ≤ V)
    (ht : ∀ i : ι, f.val.app (op (U i)) (sf i) = G.val.map (homOfLE (hV i)).op t) :
    f.val.app (op (iSup U)) s = G.val.map (homOfLE (by aesop_cat)).op t := by
      have h_is_gluing : ∀ x y : G.val.obj (op (iSup U)), (∀ i : ι, G.val.map
        (homOfLE (le_iSup U i)).op x = G.val.map (homOfLE (le_iSup U i)).op y) → x = y := by
        intro x y hxy;
        apply G.isSeparated (iSup U)
          (Sieve.generate (Presieve.ofArrows (fun i => U i) fun i => homOfLE (le_iSup U i)))
        · intro x hx;
          obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := by simpa using hx
          exact ⟨U i, homOfLE ( le_iSup U i ), Sieve.le_generate _ _ (Presieve.ofArrows.mk i ), hi⟩
        · rintro Y f ⟨i, hi⟩
          rcases hi with ⟨h, g, hg, rfl⟩
          cases hg
          simp_all only [homOfLE_leOfHom, op_comp, Functor.map_comp, AddCommGrpCat.hom_comp,
            AddMonoidHom.coe_comp, Function.comp_apply]
      apply h_is_gluing _ _
      intro i ; have := le_iSup U i ; have := iSup_le hV
      change (f.val.app (op (iSup U)) s) |_ (U i) = (t |_ (iSup U)) |_ (U i)
      have : s |_ (U i) = sf i := h i
      rw[← map_restrict, restrict_restrict, this]
      exact ht i

end TopCat.Sheaf.AddCommGrpCat

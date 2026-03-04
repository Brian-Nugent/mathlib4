module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Flasque

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w' w v u

namespace CategoryTheory

open Abelian TopologicalSpace TopCat Limits Sheaf

variable {X : TopCat.{u}}

namespace Sheaf

section

abbrev embed (U : Opens X) : (Opens.toTopCat X).obj U ⟶ X := Opens.inclusion' U

noncomputable abbrev restrict (U : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U) ⋙ Sheaf.pushforward AddCommGrpCat
    (Opens.inclusion' U)

noncomputable abbrev to_restrict (U : Opens X) :
    𝟭 _ ⟶ restrict U := (Sheaf.pullbackPushforwardAdjunction _ (Opens.inclusion' U)).unit

local instance (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    IsFlasque ((restrict U).obj F) := by
  have := IsFlasque.pullbackIsFlasqueOfIsOpenEmbedding (Opens.isOpenEmbedding U)
  apply IsFlasque.pushforwardIsFlasque

local instance to_restrict_surjective_of_flasque (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [IsFlasque F] : Epi ((to_restrict U).app F) := sorry
-- This needs the stuff I did in the branch `pushpulladjunction`, to identify `to_restrict`
-- to a restriction map. The theorem is call `truc` right now.

set_option backward.isDefEq.respectTransparency false in
example (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) : 0 = 0 := by
  obtain ⟨I, _, f, hf⟩ := CategoryTheory.EnoughInjectives.presentation F
  let S := ShortComplex.mk f (cokernel.π f) (by cat_disch)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel f)
  let restrict_pres := ShortComplex.mk ((restrict U).map f) (cokernel.π ((restrict U).map f))
    (by cat_disch)
  have he : restrict_pres.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel _)
  let ι : restrict_pres.X₃ ⟶ (restrict U).obj S.X₃ := cokernel.desc ((restrict U).map S.f)
    ((restrict U).map S.g) (by rw [← Functor.map_comp, S.zero, Functor.map_zero])
  have ιcond : restrict_pres.g ≫ ι = (restrict U).map S.g := sorry
  have : Mono ι := sorry
  set η : S.X₃ ⟶ restrict_pres.X₃ := cokernel.desc S.f ((to_restrict U).app S.X₂ ≫ restrict_pres.g)
    (by simp only [← cancel_mono ι, Category.assoc, ιcond]; rw [← (to_restrict U).naturality];
        simp only [Functor.comp_obj, Functor.id_obj, Functor.id_map, ShortComplex.zero_assoc,
          zero_comp])
  have ηcond₁ : η ≫ ι = (to_restrict U).app S.X₃ := sorry
  have ηcond₂ : S.g ≫ η = (to_restrict U).app S.X₂ ≫ restrict_pres.g := sorry
  have : Epi η := sorry

--set_option backward.isDefEq.respectTransparency false in
theorem prop1 (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) {B : Set (Opens X)}
    (hB : Opens.IsBasis B)
    (hinter : ∀ (U V : Opens X), U ∈ B → V ∈ B → U ⊓ V ∈ B)
    (vanish : ∀ (r : ℕ) (U : Opens X), 1 ≤ r → r ≤ n → U ∈ B →
    IsZero (H ((Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U)).obj F) r))
    (α : H F n) : ∃ (I : Type*) (u : I → Opens X),
    (∀ i, u i ∈ B) ∧ (⋃ i, (u i).1 = Set.univ) ∧
    (∀ i, H.map (to_restrict (u i) F) n α = 0) := sorry

end

end Sheaf

end CategoryTheory

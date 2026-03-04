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

--local instance (U : Opens X) : PreservesFiniteLimits (restrict U) := inferInstance

local instance (U : Opens X) : (Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U)).Additive :=
  sorry

local instance (U : Opens X) : (restrict U).Additive := sorry

noncomputable abbrev to_restrict (U : Opens X) :
    𝟭 _ ⟶ restrict U := (Sheaf.pullbackPushforwardAdjunction _ (Opens.inclusion' U)).unit

local instance (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    IsFlasque ((restrict U).obj F) := by
  have := IsFlasque.pullbackIsFlasqueOfIsOpenEmbedding (Opens.isOpenEmbedding U)
  apply IsFlasque.pushforwardIsFlasque

local instance to_restrict_epi_of_flasque (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [IsFlasque F] : Epi ((to_restrict U).app F) := sorry
-- This needs the stuff I did in the branch `pushpulladjunction`, to identify `to_restrict`
-- to a restriction map. The theorem is call `truc` right now.

/-
First we set up some objects that will be useful for the proof:
* A short exact sequence `S` or `pres` : 0 -> F -> I -> G -> 0 with I injective.
* A short exact sequence `restrict_pres` : `0 -> (restict U).obj F -> (restrict U).obj I -> H -> 0`.
* A monomorphism `ι : H -> (restrict U).obj G` whose composition with `restrict_pres.g` is
`(restrict U).map S.g`.
* An epimorphism `η : G ⟶ H` such that `η ≫ ι = (to_restrict U).app G` and
`S.g ≫ η = (to_restrict U).app I ≫ restrict_pres.g`.
-/

noncomputable section

variable (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)

def injpres : InjectivePresentation F := Classical.choice (EnoughInjectives.presentation F)

local instance : Mono (injpres F).f := (injpres F).mono
local instance : Injective (injpres F).J := (injpres F).injective

def pres := ShortComplex.mk (injpres F).f (cokernel.π (injpres F).f) (by cat_disch)

local instance : Mono (pres F).f := by dsimp [pres]; infer_instance
local instance : Epi (pres F).g := by dsimp [pres]; infer_instance
local instance : Injective (pres F).X₂ := by dsimp [pres]; infer_instance

lemma pres_exact : (pres F).ShortExact :=
  ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel _)

def restrict_pres := ShortComplex.mk ((restrict U).map (injpres F).f)
  (cokernel.π ((restrict U).map (injpres F).f)) (by cat_disch)

local instance : Mono (restrict_pres U F).f := by dsimp [restrict_pres]; infer_instance
local instance : Epi (restrict_pres U F).g := by dsimp [restrict_pres]; infer_instance

lemma restrict_pres_exact : (restrict_pres U F).ShortExact :=
  ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel _)

lemma restrict_pres'_exact : ((pres F).map (restrict U)).Exact :=
  ((restrict U).preservesFiniteLimits_iff_forall_exact_map_and_mono.mp inferInstance _
  (pres_exact F)).1

def ι : (restrict_pres U F).X₃ ⟶ (restrict U).obj (pres F).X₃ :=
  cokernel.desc ((restrict U).map (pres F).f) ((restrict U).map (pres F).g)
  (by rw [← Functor.map_comp, (pres F).zero, Functor.map_zero])

lemma ιcond : (restrict_pres U F).g ≫ ι U F = ((pres F).map (restrict U)).g := by
  dsimp [ι, restrict_pres, pres]; cat_disch

set_option backward.isDefEq.respectTransparency false in
local instance : Mono (ι U F) := by
  refine Preadditive.mono_of_cancel_zero _ (fun u hu ↦ ?_)
  obtain ⟨A, v, _, w, hvw⟩ := surjective_up_to_refinements_of_epi (restrict_pres U F).g u
  rw [← cancel_epi v, comp_zero, hvw]
  have eq : w ≫ ((pres F).map (restrict U)).g = 0 := by
    rw [← ιcond, ← Category.assoc, ← hvw, Category.assoc, hu, comp_zero]
  obtain ⟨A', x, _, y, hxy⟩ := (restrict_pres'_exact U F).exact_up_to_refinements _ eq
  rw [← cancel_epi x, comp_zero, ← Category.assoc, hxy, Category.assoc]
  change y ≫ ((restrict_pres U F).f ≫_) = 0
  rw [ShortComplex.zero, comp_zero]

set_option backward.isDefEq.respectTransparency false in
def η : (pres F).X₃ ⟶ (restrict_pres U F).X₃ :=
  cokernel.desc (pres F).f ((to_restrict U).app (pres F).X₂ ≫ (restrict_pres U F).g)
    (by simp only [← cancel_mono (ι U F), Category.assoc, ιcond, ShortComplex.map_g]
        rw [← (to_restrict U).naturality];
        simp only [Functor.comp_obj, Functor.id_obj, Functor.id_map, ShortComplex.zero_assoc,
          zero_comp])

set_option backward.isDefEq.respectTransparency false in
lemma ηcond₁ : η U F ≫ ι U F = (to_restrict U).app (pres F).X₃ := by
  dsimp [η]
  rw [← cancel_epi (cokernel.π (pres F).f), ← Category.assoc, cokernel.π_desc, Category.assoc,
    ιcond, ShortComplex.map_g, ← (to_restrict U).naturality, Functor.id_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma ηcond₂ : (pres F).g ≫ η U F = (to_restrict U).app (pres F).X₂ ≫ (restrict_pres U F).g := by
    rw [← cancel_mono (ι U F), Category.assoc, ηcond₁, Category.assoc, ιcond, ShortComplex.map_g,
      ← (to_restrict U).naturality, Functor.id_map]

set_option backward.isDefEq.respectTransparency false in
local instance : Epi (η U F) := epi_of_epi_fac (ηcond₂ U F)

def pullback_pres := (pres F).map (Sheaf.pullback _ (Opens.inclusion' U))

lemma pullback_pres_exact : (pullback_pres U F).ShortExact :=
  (pres_exact F).map (Sheaf.pullback _ (Opens.inclusion' U))

set_option backward.isDefEq.respectTransparency false in
theorem prop1 (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) {B : Set (Opens X)}
    (hB : Opens.IsBasis B)
    (hinter : ∀ (U V : Opens X), U ∈ B → V ∈ B → U ⊓ V ∈ B)
    (vanish : ∀ (r : ℕ) (U : Opens X), 1 ≤ r → r ≤ n → U ∈ B →
    IsZero (H ((Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U)).obj F) r))
    (c : H F (n + 1)) : ∃ (I : Type*) (u : I → Opens X),
    (∀ i, u i ∈ B) ∧ (⋃ i, (u i).1 = Set.univ) ∧
    (∀ i, H.map ((to_restrict (u i)).app F) (n + 1) c = 0) := by
  induction n generalizing F with
  | zero =>
    have : Injective (pres F).X₂ := by dsimp [pres]; infer_instance
-- Why does Lean find the local instance I defined earlier?
    have : Subsingleton (Ext ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift.{u, 0} ℤ))) (pres F).X₂ 1) :=
      Abelian.Ext.subsingleton_of_injective _ _ 0
-- The first cohomology group of `(pres F).X₂` vanishes.
    obtain ⟨s, hs⟩ := Abelian.Ext.covariant_sequence_exact₁ ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of.{u} (ULift ℤ))) (pres_exact F) c
      (Subsingleton.elim _ _) (n₀ := 0) rfl
-- Using the long cohomology sequence, we find a global section `s` is `(pres F).X₃` that is
-- sent to `c` by the connecting morphism.
-- Technically `s` is not a section but an element of `H (pres F).X₃ 0`, so we need to apply
-- `TopCat.Sheaf.H.equiv₀` to make it a section.
    have : Sheaf.IsLocallySurjective (pres F).g :=
      (Sheaf.isLocallySurjective_iff_epi' _ _).mpr (pres_exact F).epi_g
    obtain ⟨I, U, hU, t, h⟩ := Presheaf.exists_lift_cover_basis_of_isLocallySurjective this hB
      (TopCat.Sheaf.H.equiv₀ (pres F).X₃ s)
-- As `(pres F).g : (pres F).X₂ ⟶ (pres F).X₃` is an epimorphism of sheaves, the section `s`
-- lifts locally to sections of `(pres F).X₂`, on a cover `U : ι → Opens X`.
    sorry
  | succ n hn => sorry

end

end

end Sheaf

end CategoryTheory

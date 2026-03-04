module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.AddCommGrpCat

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w' w v u

namespace CategoryTheory

open Abelian TopologicalSpace TopCat Limits

variable {X : TopCat.{u}}

namespace Sheaf

--instance : PreservesFilteredColimits (forget AddCommGrpCat.{u}) := sorry

section

abbrev embed (U : Opens X) : (Opens.toTopCat X).obj U ⟶ X := Opens.inclusion' U

noncomputable abbrev restrict (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
    (Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U) ⋙ Sheaf.pushforward AddCommGrpCat
    (Opens.inclusion' U)).obj F

noncomputable abbrev to_restrict (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    F ⟶ restrict U F := (Sheaf.pullbackPushforwardAdjunction _ (Opens.inclusion' U)).unit.app F

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

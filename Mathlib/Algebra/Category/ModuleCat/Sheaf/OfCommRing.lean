/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# Modules over sheaves of commutative rings

This file provides short names for categories and functors obtained from a sheaf of commutative
rings by forgetting to rings. In particular, these names reduce the need for
repeatedly writing the relevant forgetful functor.

Objects are constructed from a presheaf of modules together with a proof of the sheaf condition.
Pushforward and pullback use continuous functors between the underlying sites.

We assume that forgetting commutativity preserves sheaves, expressed by
`J.HasSheafCompose (forget₂ CommRingCat RingCat)`. This is inferred for sites whose object and
morphism universes are bounded by the universe of the rings.
-/

@[expose] public section

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Functor

/-- The category of sheaves of modules over a sheaf of commutative rings. -/
abbrev SheafOfModulesOfCommRing {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] :=
  SheafOfModules.{v} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)

namespace SheafOfModulesOfCommRing

section Basic

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]

/-- Construct a sheaf of modules over a sheaf of commutative rings. -/
abbrev mk (val : PresheafOfModulesOfCommRing.{v} R.obj)
    (isSheaf : Presheaf.IsSheaf J val.presheaf) : SheafOfModulesOfCommRing.{v} R where
  val := val
  isSheaf := isSheaf

/-- The underlying presheaf of modules over a presheaf of commutative rings. -/
abbrev val (M : SheafOfModulesOfCommRing.{v} R) :
    PresheafOfModulesOfCommRing.{v} R.obj :=
  SheafOfModules.val M

/-- Construct a morphism of sheaves of modules over a sheaf of commutative rings. -/
abbrev homMk {M₁ M₂ : SheafOfModulesOfCommRing.{v} R}
    (app : ∀ (X : Cᵒᵖ), M₁.val.obj X ⟶ M₂.val.obj X)
    (naturality : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
      M₁.val.map f ≫ (ModuleCat.restrictScalars (R.obj.map f).hom).map (app Y) =
        app X ≫ M₂.val.map f := by cat_disch) : M₁ ⟶ M₂ where
  val := PresheafOfModulesOfCommRing.homMk app naturality

/-- Construct an isomorphism of sheaves of modules over a sheaf of commutative rings. -/
abbrev isoMk {M₁ M₂ : SheafOfModulesOfCommRing.{v} R}
    (app : ∀ (X : Cᵒᵖ), M₁.val.obj X ≅ M₂.val.obj X)
    (naturality : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y),
      M₁.val.map f ≫ (ModuleCat.restrictScalars (R.obj.map f).hom).map (app Y).hom =
        (app X).hom ≫ M₂.val.map f := by cat_disch) : M₁ ≅ M₂ :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModulesOfCommRing.isoMk app naturality)

/-- The component of a morphism of sheaves of modules over a sheaf of commutative rings. -/
abbrev _root_.SheafOfModules.Hom.app' {M₁ M₂ : SheafOfModulesOfCommRing.{v} R}
    (f : M₁ ⟶ M₂) (X : Cᵒᵖ) : M₁.val.obj X ⟶ M₂.val.obj X :=
  f.val.app' X

lemma naturality_apply {M₁ M₂ : SheafOfModulesOfCommRing.{v} R}
    (f : M₁ ⟶ M₂) {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : M₁.val.obj X) :
    (f.app' Y) ((M₁.val.map g) x) = (M₂.val.map g) ((f.app' X) x) :=
  PresheafOfModulesOfCommRing.naturality_apply f.val g x

/-- The forgetful functor to presheaves of modules over a presheaf of commutative rings. -/
abbrev forget (R : Sheaf J CommRingCat.{u}) :
    SheafOfModulesOfCommRing.{v} R ⥤ PresheafOfModulesOfCommRing.{v} R.obj :=
  SheafOfModules.forget _

instance : (forget.{v} R).Full := (SheafOfModules.fullyFaithfulForget _).full

instance : (forget.{v} R).Faithful := (SheafOfModules.fullyFaithfulForget _).faithful

/-- Evaluation of sheaves of modules over a sheaf of commutative rings. -/
abbrev evaluation (R : Sheaf J CommRingCat.{u}) (X : Cᵒᵖ) :
    SheafOfModulesOfCommRing.{v} R ⥤ ModuleCat.{v} (R.obj.obj X) :=
  SheafOfModules.evaluation _ X

/-- The forgetful functor to sheaves of abelian groups. -/
noncomputable abbrev toSheaf (R : Sheaf J CommRingCat.{u}) :
    SheafOfModulesOfCommRing.{v} R ⥤ Sheaf J AddCommGrpCat.{v} :=
  SheafOfModules.toSheaf _

/-- The free sheaf of modules of rank one over a sheaf of commutative rings. -/
noncomputable abbrev unit (R : Sheaf J CommRingCat.{u}) :
    SheafOfModulesOfCommRing.{u} R :=
  SheafOfModules.unit _

/-- Restriction of scalars along a morphism of sheaves of commutative rings. -/
noncomputable abbrev restrictScalars {S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    SheafOfModulesOfCommRing.{v} S ⥤ SheafOfModulesOfCommRing.{v} R :=
  SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).map φ)

end Basic

section PushforwardPullback

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]

variable {F : C ⥤ D} [F.IsContinuous J K] {R : Sheaf K CommRingCat.{u}}
  {S : Sheaf J CommRingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat J K).obj R)

/-- The pushforward functor induced by a morphism of sheaves of commutative rings. -/
noncomputable abbrev pushforward :
    SheafOfModulesOfCommRing.{v} R ⥤ SheafOfModulesOfCommRing.{v} S :=
  SheafOfModules.pushforward (F := F)
    ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).map φ)

/-- The pullback functor induced by a morphism of sheaves of commutative rings. -/
noncomputable abbrev pullback [(pushforward.{v} φ).IsRightAdjoint] :
    SheafOfModulesOfCommRing.{v} S ⥤ SheafOfModulesOfCommRing.{v} R :=
  SheafOfModules.pullback (F := F)
    ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).map φ)

/-- The adjunction between pullback and pushforward for modules over sheaves of
commutative rings. -/
noncomputable abbrev pullbackPushforwardAdjunction
    [(pushforward.{v} φ).IsRightAdjoint] :
    pullback.{v} φ ⊣ pushforward.{v} φ :=
  SheafOfModules.pullbackPushforwardAdjunction _

end PushforwardPullback

end SheafOfModulesOfCommRing

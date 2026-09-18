/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
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

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory Functor Limits

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

/-- The forgetful functor to presheaves of modules is fully faithful. -/
abbrev fullyFaithfulForget (R : Sheaf J CommRingCat.{u}) : (forget.{v} R).FullyFaithful :=
  SheafOfModules.fullyFaithfulForget _

/-- Evaluation of sheaves of modules over a sheaf of commutative rings. -/
abbrev evaluation (R : Sheaf J CommRingCat.{u}) (X : Cᵒᵖ) :
    SheafOfModulesOfCommRing.{v} R ⥤ ModuleCat.{v} (R.obj.obj X) :=
  SheafOfModules.evaluation _ X

/-- The forgetful functor to sheaves of abelian groups. -/
noncomputable abbrev toSheaf (R : Sheaf J CommRingCat.{u}) :
    SheafOfModulesOfCommRing.{v} R ⥤ Sheaf J AddCommGrpCat.{v} :=
  SheafOfModules.toSheaf _

/-- Forget to sheaves of modules over the ring of sections at an initial object. -/
noncomputable abbrev forgetToSheafModuleCat (R : Sheaf J CommRingCat.{u})
    (X : Cᵒᵖ) (hX : IsInitial X) :
    SheafOfModulesOfCommRing.{v} R ⥤ Sheaf J (ModuleCat.{v} (R.obj.obj X)) :=
  SheafOfModules.forgetToSheafModuleCat _ X hX

/-- The free sheaf of modules of rank one over a sheaf of commutative rings. -/
noncomputable abbrev unit (R : Sheaf J CommRingCat.{u}) :
    SheafOfModulesOfCommRing.{u} R :=
  SheafOfModules.unit _

/-- Restriction of scalars along a morphism of sheaves of commutative rings. -/
noncomputable abbrev restrictScalars {S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    SheafOfModulesOfCommRing.{v} S ⥤ SheafOfModulesOfCommRing.{v} R :=
  SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).map φ)

section Sheafification

variable [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

set_option backward.isDefEq.respectTransparency false in
/-- Sheafification of modules over a sheaf of commutative rings. -/
noncomputable abbrev sheafification (R : Sheaf J CommRingCat.{u}) :
    PresheafOfModulesOfCommRing.{v} R.obj ⥤ SheafOfModulesOfCommRing.{v} R :=
  PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
/-- Sheafification is left adjoint to the forgetful functor to presheaves of modules. -/
noncomputable abbrev sheafificationAdjunction (R : Sheaf J CommRingCat.{u}) :
    sheafification.{v} R ⊣ forget R :=
  PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) (𝟙 _)

end Sheafification

/-- The free sheaf of modules on a type. -/
noncomputable abbrev free [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (I : Type u) :
    SheafOfModulesOfCommRing.{u} R :=
  SheafOfModules.free I

/-- Restrict a sheaf of modules to an over-category. -/
noncomputable abbrev overFunctor (R : Sheaf J CommRingCat.{u}) (X : C)
    [(J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})] :
    SheafOfModulesOfCommRing.{v} R ⥤ SheafOfModulesOfCommRing.{v} (R.over X) :=
  SheafOfModules.overFunctor _ X

/-- Restrict sheaves of modules along a morphism of objects of the site. -/
noncomputable abbrev overMap (R : Sheaf J CommRingCat.{u}) {X Y : C} (f : X ⟶ Y)
    [(J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [(J.over Y).HasSheafCompose (forget₂ CommRingCat RingCat.{u})] :
    SheafOfModulesOfCommRing.{v} (R.over Y) ⥤ SheafOfModulesOfCommRing.{v} (R.over X) :=
  SheafOfModules.overMap ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) f

/-- The property of being a quasicoherent sheaf of modules. -/
abbrev isQuasicoherent (R : Sheaf J CommRingCat.{u})
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ObjectProperty (SheafOfModulesOfCommRing.{u} R) :=
  SheafOfModules.isQuasicoherent _

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

set_option backward.isDefEq.respectTransparency false in
/-- Pushforward commutes with forgetting to sheaves of modules over a fixed ring. -/
noncomputable abbrev pushforwardCompForgetToSheafModuleCat
    (X : Cᵒᵖ) (hX : IsInitial X) (hX' : IsInitial (F.op.obj X)) :
    pushforward.{max u₂ v₂ v} φ ⋙ forgetToSheafModuleCat S X hX ≅
      forgetToSheafModuleCat R _ hX' ⋙
        sheafCompose K (ModuleCat.restrictScalars.{max u₂ v₂ v} (φ.hom.app X).hom) ⋙
          F.sheafPushforwardContinuous _ J K :=
  SheafOfModules.pushforwardCompForgetToSheafModuleCat.{v₁, v₂, u₁, u₂, u, v} _ X hX hX'

/-- Pushforward by the identity identifies with the identity functor. -/
noncomputable abbrev pushforwardId (S : Sheaf J CommRingCat.{u}) :
    pushforward.{v} (F := 𝟭 C) (𝟙 S) ≅ 𝟭 _ :=
  SheafOfModules.pushforwardId _

instance (S : Sheaf J CommRingCat.{u}) :
    (pushforward.{v} (F := 𝟭 C) (𝟙 S)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardId S).symm

/-- Pullback by the identity identifies with the identity functor. -/
noncomputable abbrev pullbackId (S : Sheaf J CommRingCat.{u}) :
    pullback.{v} (F := 𝟭 C) (𝟙 S) ≅ 𝟭 _ :=
  SheafOfModules.pullbackId _

section Composition

variable {D' : Type u₃} [Category.{v₃} D'] {K' : GrothendieckTopology D'}
  [K'.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  {G : D ⥤ D'} [G.IsContinuous K K'] {R' : Sheaf K' CommRingCat.{u}}
  (ψ : R ⟶ (G.sheafPushforwardContinuous CommRingCat K K').obj R')

/-- The composition of pushforwards identifies with pushforward along the composite. -/
noncomputable abbrev pushforwardComp :
    haveI := Functor.isContinuous_comp F G J K K'
    pushforward.{v} ψ ⋙ pushforward.{v} φ ≅
      pushforward.{v} (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous CommRingCat J K).map ψ) :=
  SheafOfModules.pushforwardComp _ _

variable [(F ⋙ G).IsContinuous J K']
  [(pushforward.{v} φ).IsRightAdjoint] [(pushforward.{v} ψ).IsRightAdjoint]

instance : (pushforward.{v} (F := F ⋙ G)
    (φ ≫ (F.sheafPushforwardContinuous CommRingCat J K).map ψ)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardComp φ ψ)

/-- The composition of pullbacks identifies with pullback along the composite. -/
noncomputable abbrev pullbackComp :
    pullback.{v} φ ⋙ pullback.{v} ψ ≅
      pullback.{v} (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous CommRingCat J K).map ψ) :=
  SheafOfModules.pullbackComp _ _

variable {D'' : Type u₄} [Category.{v₄} D''] {K'' : GrothendieckTopology D''}
  [K''.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  {G' : D' ⥤ D''} [G'.IsContinuous K' K''] {R'' : Sheaf K'' CommRingCat.{u}}
  [(G ⋙ G').IsContinuous K K''] [((F ⋙ G) ⋙ G').IsContinuous J K'']
  [(F ⋙ G ⋙ G').IsContinuous J K'']
  (ψ' : R' ⟶ (G'.sheafPushforwardContinuous CommRingCat K' K'').obj R'')
  [(pushforward.{v} ψ').IsRightAdjoint]

set_option backward.isDefEq.respectTransparency false in
/-- Associativity of the composition isomorphisms for pullback. -/
abbrev pullback_assoc :
    isoWhiskerLeft _ (pullbackComp.{v} ψ ψ') ≪≫
      pullbackComp.{v} (G := G ⋙ G') φ
        (ψ ≫ (G.sheafPushforwardContinuous CommRingCat K K').map ψ') =
    (associator _ _ _).symm ≪≫ isoWhiskerRight (pullbackComp.{v} φ ψ) _ ≪≫
      pullbackComp.{v} (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous CommRingCat J K).map ψ) ψ' :=
  SheafOfModules.pullback_assoc.{v} (F := F) (G := G) (G' := G')
    (J := J) (K := K) (K' := K') (K'' := K'')
    (S := (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj S)
    (R := (sheafCompose K (forget₂ CommRingCat RingCat.{u})).obj R)
    (R' := (sheafCompose K' (forget₂ CommRingCat RingCat.{u})).obj R')
    (R'' := (sheafCompose K'' (forget₂ CommRingCat RingCat.{u})).obj R'')
    ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).map φ)
    ((sheafCompose K (forget₂ CommRingCat RingCat.{u})).map ψ)
    ((sheafCompose K' (forget₂ CommRingCat RingCat.{u})).map ψ')

end Composition

variable [(pushforward.{v} φ).IsRightAdjoint]

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of pullback composition with an identity on the source site. -/
abbrev pullback_id_comp :
    pullbackComp.{v} (F := 𝟭 C) (𝟙 S) φ =
      isoWhiskerRight (pullbackId S) (pullback φ) ≪≫ Functor.leftUnitor _ :=
  SheafOfModules.pullback_id_comp.{v} (F := F) (J := J) (K := K)
    (S := (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj S)
    (R := (sheafCompose K (forget₂ CommRingCat RingCat.{u})).obj R)
    ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).map φ)

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of pullback composition with an identity on the target site. -/
abbrev pullback_comp_id :
    pullbackComp.{v} (G := 𝟭 D) φ (𝟙 R) =
      isoWhiskerLeft _ (pullbackId R) ≪≫ Functor.rightUnitor _ :=
  SheafOfModules.pullback_comp_id.{v} (F := F) (J := J) (K := K)
    (S := (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj S)
    (R := (sheafCompose K (forget₂ CommRingCat RingCat.{u})).obj R)
    ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).map φ)

end PushforwardPullback

section Quasicoherent

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat J K).obj R)

set_option backward.isDefEq.respectTransparency false in
/-- Pushforward along a left adjoint preserves quasicoherence when the structure sheaves
are isomorphic and their rank-one modules correspond. -/
abbrev isQuasicoherent_pushforward_of_isLeftAdjoint
    (η : (pushforward φ).obj (unit R) ≅ unit S) [F.IsLeftAdjoint] [IsIso φ]
    [∀ X, (Over.post (X := X) F).IsContinuous (J.over X) (K.over (F.obj X))]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModulesOfCommRing.{u} R} [SheafOfModules.IsQuasicoherent M] :
    SheafOfModules.IsQuasicoherent ((pushforward φ).obj M) :=
  SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint F
    (R := (sheafCompose K (forget₂ CommRingCat RingCat.{u})).obj R)
    (S := (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj S) (M := M)
    ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).map φ) η

end Quasicoherent

end SheafOfModulesOfCommRing

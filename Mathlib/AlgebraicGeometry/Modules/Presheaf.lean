/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The category of presheaves of modules over a scheme

In this file, given a scheme `X`, we define the category of presheaves
of modules over its presheaf of commutative rings. We also provide the morphism of
sheaves of commutative rings induced by a morphism of schemes.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X Y : Scheme.{u})

/-- The category of presheaves of modules over a scheme. -/
abbrev PresheafOfModules := PresheafOfModulesOfCommRing.{u} X.presheaf

variable {X Y} in
/-- The morphism of sheaves of commutative rings corresponding to a morphism of schemes. -/
def Hom.toCommRingCatSheafHom (f : X ⟶ Y) :
    Y.sheaf ⟶ ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      CommRingCat _ _).obj X.sheaf where
  hom := f.c

end AlgebraicGeometry.Scheme

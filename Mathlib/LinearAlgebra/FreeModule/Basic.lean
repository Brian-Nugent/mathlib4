/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Logic.Small.Basic

/-!
# Free modules

We introduce a class `Module.IsFree R M`, for `R` a `Semiring` and `M` an `R`-module and we provide
several basic instances for this class.

Use `Finsupp.linearCombination_id_surjective` to prove that any module is the quotient of a free
module.

## Main definition

* `Module.IsFree R M` : the class of free `R`-modules.
-/

@[expose] public section

assert_not_exists DirectSum Matrix TensorProduct

universe u v w z

variable {ι : Type*} (R : Type u) (M : Type v) (N : Type z)

namespace Module
section Basic

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- `Module.IsFree R M` is the statement that the `R`-module `M` is free. -/
class IsFree (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  exists_basis (R M) : Nonempty <| (I : Type v) × Basis I R M

lemma IsFree.exists_set [IsFree R M] : ∃ S : Set M, Nonempty (Basis S R M) :=
  let ⟨_I, b⟩ := exists_basis R M; ⟨Set.range b, ⟨b.reindexRange⟩⟩

theorem isFree_iff_set : IsFree R M ↔ ∃ S : Set M, Nonempty (Basis S R M) :=
  ⟨fun _ ↦ IsFree.exists_set .., fun ⟨S, hS⟩ ↦ ⟨nonempty_sigma.2 ⟨S, hS⟩⟩⟩

/-- If `M` fits in universe `w`, then freeness is equivalent to existence of a basis in that
universe.

Note that if `M` does not fit in `w`, the reverse direction of this implication is still true as
`Module.IsFree.of_basis`. -/
theorem isFree_def [Small.{w, v} M] : IsFree R M ↔ ∃ I : Type w, Nonempty (Basis I R M) where
  mp h :=
    ⟨Shrink (Set.range h.exists_basis.some.2),
      ⟨(Basis.reindexRange h.exists_basis.some.2).reindex (equivShrink _)⟩⟩
  mpr h := ⟨(nonempty_sigma.2 h).map fun ⟨_, b⟩ => ⟨Set.range b, b.reindexRange⟩⟩

variable {R M}

theorem IsFree.of_basis {ι : Type w} (b : Basis ι R M) : IsFree R M :=
  (isFree_def R M).2 ⟨Set.range b, ⟨b.reindexRange⟩⟩

end Basic

namespace IsFree

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M] [Module.IsFree R M]
variable [AddCommMonoid N] [Module R N]

/-- If `Module.IsFree R M` then `ChooseBasisIndex R M` is the `ι` which indexes the basis
  `ι → M`. Note that this is defined such that this type is finite if `R` is trivial. -/
def ChooseBasisIndex : Type _ :=
  ((Module.isFree_iff_set R M).mp ‹_›).choose

/-- There is no hope of computing this, but we add the instance anyway to avoid fumbling with
`open scoped Classical`. -/
noncomputable instance : DecidableEq (ChooseBasisIndex R M) := Classical.decEq _

/-- If `Module.IsFree R M` then `chooseBasis : ι → M` is the basis.
Here `ι = ChooseBasisIndex R M`. -/
noncomputable def chooseBasis : Basis (ChooseBasisIndex R M) R M :=
  ((Module.isFree_iff_set R M).mp ‹_›).choose_spec.some

/-- The universal property of free modules: giving a function `(ChooseBasisIndex R M) → N`, for `N`
an `R`-module, is the same as giving an `R`-linear map `M →ₗ[R] N`.

This definition is parameterized over an extra `Semiring S`,
such that `SMulCommClass R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `AddEquiv` by setting `S := ℕ`.
See library note [bundled maps over different rings]. -/
noncomputable def constr {S : Type z} [Semiring S] [Module S N] [SMulCommClass R S N] :
    (ChooseBasisIndex R M → N) ≃ₗ[S] M →ₗ[R] N :=
  Basis.constr (chooseBasis R M) S

instance (priority := 100) instIsTorsionFree : IsTorsionFree R M :=
  let ⟨⟨_, b⟩⟩ := exists_basis (R := R) (M := M)
  b.isTorsionFree

instance [Nontrivial M] : Nonempty (Module.IsFree.ChooseBasisIndex R M) :=
  (Module.IsFree.chooseBasis R M).index_nonempty

theorem infinite [Infinite R] [Nontrivial M] : Infinite M :=
  (Equiv.infinite_iff (chooseBasis R M).repr.toEquiv).mpr Finsupp.infinite_of_right

instance [Nontrivial M] : FaithfulSMul R M :=
  .of_injective _ (chooseBasis R M).repr.symm.injective

variable {R M N}

lemma of_equiv {R R' M M' : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M'] [Module R' M']
    {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e₂ : M ≃ₛₗ[σ] M') [Module.IsFree R M] :
    Module.IsFree R' M' := by
  let e₁ : R ≃+* R' := RingHomInvPair.toRingEquiv σ σ'
  let I := Module.IsFree.ChooseBasisIndex R M
  obtain ⟨e₃ : M ≃ₗ[R] I →₀ R⟩ := Module.IsFree.chooseBasis R M
  let e : M' ≃+ (I →₀ R') :=
    (e₂.symm.trans e₃).toAddEquiv.trans (Finsupp.mapRange.addEquiv (ι := I) e₁.toAddEquiv)
  have he (x) : e x = Finsupp.mapRange.addEquiv (ι := I) e₁.toAddEquiv (e₃ (e₂.symm x)) := rfl
  let e' : M' ≃ₗ[R'] (I →₀ R') :=
    { __ := e, map_smul' := fun m x ↦ Finsupp.ext fun i ↦ by simp [e₁, he, map_smulₛₗ] }
  exact of_basis (.ofRepr e')

/-- A variation of `of_equiv`: the assumption `Module.IsFree R P` here is explicit rather than an
instance. -/
theorem of_equiv' {P : Type v} [AddCommMonoid P] [Module R P] (_ : Module.IsFree R P)
    (e : P ≃ₗ[R] N) : Module.IsFree R N :=
  of_equiv e

lemma iff_of_equiv {R R' M M'} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M'] [Module R' M']
    {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e₂ : M ≃ₛₗ[σ] M') :
    Module.IsFree R M ↔ Module.IsFree R' M' :=
  ⟨fun _ ↦ of_equiv e₂, fun _ ↦ of_equiv e₂.symm⟩

@[deprecated (since := "2026-02-14")] alias of_ringEquiv := of_equiv
@[deprecated (since := "2026-02-14")] alias iff_of_ringEquiv := iff_of_equiv

instance Module.IsFree_shrink [Small.{w} M] : Module.IsFree R (Shrink.{w} M) :=
  Module.IsFree.of_equiv (Shrink.linearEquiv R M).symm

variable (R M N)

/-- The module structure provided by `Semiring.toModule` is free. -/
instance self : Module.IsFree R R :=
  of_basis (Basis.singleton Unit R)

instance ulift : IsFree R (ULift M) := of_equiv ULift.moduleEquiv.symm

instance (priority := 100) of_subsingleton [Subsingleton N] : Module.IsFree R N :=
  of_basis.{u, z, z} (Basis.empty N : Basis PEmpty R N)

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
lemma of_subsingleton' [Subsingleton R] : Module.IsFree R N :=
  letI := Module.subsingleton R N
  Module.IsFree.of_subsingleton R N

end Semiring

end IsFree

namespace Basis

open Finset

variable {S : Type*} [CommRing R] [Ring S] [Algebra R S]

variable {R} in
/-- If `B` is a basis of the `R`-algebra `S` such that `B i = 1` for some index `i`, then
each `r : R` gets represented as `s • B i` as an element of `S`. -/
theorem repr_algebraMap {ι : Type*} {B : Basis ι R S} {i : ι} (hBi : B i = 1) (r : R) :
    B.repr (algebraMap R S r) = Finsupp.single i r := by
  ext j; simp [Algebra.algebraMap_eq_smul_one, ← hBi]

end Basis

namespace End
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [IsFree R M]

theorem mem_center_iff {f : End R M} :
    f ∈ Set.center (End R M) ↔ ∃ (α : R) (hα : α ∈ Set.center R), f = smulLeft α hα := by
  simp only [Semigroup.mem_center_iff, LinearMap.ext_iff, mul_apply]
  refine ⟨fun h ↦ ?_, by simp_all⟩
  by_cases! Subsingleton M
  · exact ⟨0, by simp, fun _ ↦ Subsingleton.allEq _ _⟩
  let b := IsFree.chooseBasis R M
  let i := b.index_nonempty.some
  have H x : f x = b.repr (f (b i)) i • x := by simpa using (h ((b.coord i).smulRight x) (b i)).symm
  exact ⟨b.coord i <| f <| b i, fun r ↦ by simpa using congr(b.coord i $(H <| r • b i)), H⟩

theorem mem_submonoidCenter_iff {f : End R M} :
    f ∈ Submonoid.center (End R M) ↔ ∃ (α : R) (hα : α ∈ Submonoid.center R), f = smulLeft α hα :=
  mem_center_iff

theorem mem_subsemigroupCenter_iff {f : End R M} :
    f ∈ Subsemigroup.center (End R M) ↔
      ∃ (α : R) (hα : α ∈ Subsemigroup.center R), f = smulLeft α hα :=
  mem_center_iff

end Module.End

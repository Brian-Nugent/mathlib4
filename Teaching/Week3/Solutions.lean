import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Week 3: instructor solutions

This file accompanies `RingsIdealsHoms.lean`. Exercise numbers and statements
match the student file; the proofs here contain no `sorry`.
It is independent of the student file, so checking it does not assume any
of the student's unfinished proofs. Distribute the student file on its own.

These are sample solutions, not the only acceptable proofs. For kernel and
preimage exercises, ask students to explain how the homomorphism laws and
ideal closure properties justify the result, even if `simp` finds a shortcut.
-/

namespace Week3.Solutions

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem ex01_difference_of_squares (x y : R) :
    (x + y) * (x - y) = x ^ 2 - y ^ 2 := by
  ring

theorem ex02_linear_expression (I : Ideal R) (a x y : R)
    (hx : x ∈ I) (hy : y ∈ I) : a * x + y ∈ I := by
  have hax : a * x ∈ I := I.mul_mem_left a hx
  exact I.add_mem hax hy

theorem ex03_right_multiple (I : Ideal R) (x r : R) (hx : x ∈ I) :
    x * r ∈ I := by
  exact I.mul_mem_right r hx

theorem ex04_containment (I J K : Ideal R) (hIJ : I ≤ J) (hJK : J ≤ K)
    (x : R) (hx : x ∈ I) : x ∈ K := by
  have hxJ : x ∈ J := hIJ hx
  exact hJK hxJ

theorem ex05_contains_one (I : Ideal R) (h1 : (1 : R) ∈ I) (r : R) : r ∈ I := by
  have hr : r * 1 ∈ I := I.mul_mem_left r h1
  simpa using hr

theorem ex06_factor_membership (I : Ideal R) (x : R) (hx : x - 1 ∈ I) :
    x ^ 3 - x ∈ I := by
  have hfactor : x ^ 3 - x = (x ^ 2 + x) * (x - 1) := by
    ring
  rw [hfactor]
  exact I.mul_mem_left (x ^ 2 + x) hx

theorem ex07_multiple_of_three :
    (21 : ℤ) ∈ Ideal.span ({(3 : ℤ)} : Set ℤ) := by
  rw [Ideal.mem_span_singleton]
  refine ⟨7, ?_⟩
  norm_num

theorem ex08_map_expression (f : R →+* S) (x y : R) :
    f (x * (y - 1)) = f x * (f y - 1) := by
  rw [map_mul, map_sub, map_one]

theorem ex09_map_square (f : R →+* S) (x y : R) :
    f ((x - y) ^ 2) = (f x) ^ 2 - 2 * f x * f y + (f y) ^ 2 := by
  rw [map_pow, map_sub]
  ring

theorem ex10_sum_in_kernel (f : R →+* S) (x y : R) (hx : f x = -f y) :
    x + y ∈ RingHom.ker f := by
  rw [RingHom.mem_ker, map_add, hx]
  simp

theorem ex11_difference_in_kernel (f : R →+* S) (x y : R) :
    x - y ∈ RingHom.ker f ↔ f x = f y := by
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]

theorem ex12_kernel_comp (f : R →+* S) (g : S →+* T) :
    RingHom.ker f ≤ RingHom.ker (g.comp f) := by
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  change g (f x) = 0
  rw [hx, map_zero]

theorem ex13_kernel_id : RingHom.ker (RingHom.id R) = (⊥ : Ideal R) := by
  ext x
  simp [RingHom.mem_ker]

theorem ex14_preimage_multiple (f : R →+* S) (J : Ideal S) (r x : R)
    (hx : x ∈ J.comap f) : r * x ∈ J.comap f := by
  change f x ∈ J at hx
  change f (r * x) ∈ J
  rw [map_mul]
  exact J.mul_mem_left (f r) hx

end Week3.Solutions

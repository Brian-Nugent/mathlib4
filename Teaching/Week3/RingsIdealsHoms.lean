import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Week 3: commutative rings, ideals, and ring homomorphisms

This is an executable tutorial: open it in VS Code inside a mathlib project,
and put your cursor inside each proof to follow the goal in the Lean Infoview.
Read the explanations, step through the worked examples, then complete the
practice problems at the end. Each exercise has a `sorry` to replace.

Prerequisites: functions, propositions, `example`, `variable`, and basic tactics
such as `intro`, `exact`, and `rw`. No previous ring theory is assumed.

Goals:
* State and prove identities in an arbitrary commutative ring.
* Prove ideal membership by using closure properties.
* Use a ring homomorphism and its preservation laws.
* Connect ideals and homomorphisms through kernels.

Suggested pace: 15 minutes on rings, 20 on ideals, 15 on homomorphisms,
10 on kernels, and 25 on exercises. The last two exercises are extensions.

The imports provide ideal theory and two tactics. `norm_num` checks concrete
numerical calculations; `ring` proves polynomial identities.

Unicode input in the Lean editor: `\Z` gives ℤ, `\in` gives ∈,
`\to+*` gives →+*, `\bot` gives ⊥, and `\top` gives ⊤.
-/

namespace Week3

/-!
## 1. What is a commutative ring?

A commutative ring is a type with addition, multiplication, zero, one, and
negatives, satisfying the familiar arithmetic laws:

* Addition is associative and commutative, has identity 0, and has negatives.
* Multiplication is associative and commutative and has identity 1.
* Multiplication distributes over addition.

Integers ℤ are a commutative ring. So are rational numbers ℚ and real numbers ℝ.
Natural numbers ℕ are not a ring: for example, 1 has no additive inverse in ℕ.
We do not assume that nonzero elements have multiplicative inverses, so division
is not one of our ring operations. Also, arbitrary rings can have zero divisors:
from `a * b = 0` alone we cannot conclude `a = 0 ∨ b = 0`.

In Lean, `(R : Type*)` names a type, and `[CommRing R]` asks Lean to supply its
ring operations and their laws using typeclass inference. Curly braces in
`{R : Type*}` make R implicit: Lean can usually infer it from the elements used.

`section` groups declarations; its local variables stop being available at
`end`. Each declaration uses only the variables and instances it needs.
-/

section Rings

variable {R : Type*} [CommRing R]

-- Read this as: for elements a and b of any commutative ring, a+b = b+a.
example (a b : R) : a + b = b + a := by
  exact add_comm a b

-- A named distributive law. Hover over `mul_add` to inspect its statement.
example (a b c : R) : a * (b + c) = a * b + a * c := by
  rw [mul_add]

-- Subtraction is addition of a negative. `simp` knows a-a = 0 and a+0 = a.
example (a b : R) : a + (b - b) = a := by
  simp

/-
`ring` normalizes polynomial expressions and checks that the results agree.
Use it for algebraic identities involving +, -, *, natural-number powers, and
numerals. It does not by itself turn ideal membership into a polynomial goal.
The numeral 2 below is an element of R (namely 1+1), not a separate integer.
-/

example (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

-- The same kind of statement can be specialized to a concrete ring.
example : (3 : ℤ) * (4 + 2) = 18 := by
  norm_num

end Rings

/-!
## 2. Ideals: membership and closure

An ideal I of a commutative ring R is a subset of R with these properties:

* 0 belongs to I.
* If x and y belong to I, then x+y belongs to I.
* If x belongs to I, then -x belongs to I.
* If x belongs to I and r is ANY element of R, then r*x belongs to I.

The last property is called absorption. In particular, r does not have to
belong to I. Because multiplication commutes, x*r belongs to I as well.
Closure under negatives and addition also gives closure under subtraction.

Example: the even integers form an ideal of ℤ. They contain 0, sums and
negatives of even integers are even, and any integer times an even integer is
even. This ideal does not contain 1; ideals need not contain 1.

In Lean, `I : Ideal R` bundles the subset with proofs of its closure properties.
Write `x ∈ I` for membership. We use those stored proofs through dot notation.
-/

section Ideals

variable {R : Type*} [CommRing R]
variable (I J : Ideal R)

example : (0 : R) ∈ I := by
  exact I.zero_mem

example (x y : R) (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by
  exact I.add_mem hx hy

example (x : R) (hx : x ∈ I) : -x ∈ I := by
  exact I.neg_mem hx

example (x y : R) (hx : x ∈ I) (hy : y ∈ I) : x - y ∈ I := by
  exact I.sub_mem hx hy

-- `mul_mem_left` takes the arbitrary multiplier, then the membership proof.
example (r x : R) (hx : x ∈ I) : r * x ∈ I := by
  exact I.mul_mem_left r hx

example (r x : R) (hx : x ∈ I) : x * r ∈ I := by
  exact I.mul_mem_right r hx

-- Build a membership proof one closure rule at a time.
example (a b x y : R) (hx : x ∈ I) (hy : y ∈ I) : a * x + b * y ∈ I := by
  have hax : a * x ∈ I := I.mul_mem_left a hx
  have hby : b * y ∈ I := I.mul_mem_left b hy
  exact I.add_mem hax hby

/-
Combining algebra with membership:
1. Prove an identity using `ring`.
2. Rewrite the membership goal into a useful form.
3. Use a closure property of I.

Here we need only x-y ∈ I, not x ∈ I or y ∈ I separately.
-/
example (x y : R) (hxy : x - y ∈ I) : x ^ 2 - y ^ 2 ∈ I := by
  have hfactor : x ^ 2 - y ^ 2 = (x + y) * (x - y) := by
    ring
  rw [hfactor]
  exact I.mul_mem_left (x + y) hxy

/-
`I ≤ J` means ideal containment: every element of I belongs to J.
It is the order relation on ideals, not a comparison between ring elements.
A proof `hIJ : I ≤ J` can be applied to a membership proof.
-/
example (hIJ : I ≤ J) (x : R) (hx : x ∈ I) : x ∈ J := by
  exact hIJ hx

-- To prove containment, introduce an element and its membership hypothesis.
example : I ≤ I := by
  intro x hx
  exact hx

-- The smallest ideal ⊥ contains just 0; the largest ideal ⊤ contains everything.
example (x : R) : x ∈ (⊥ : Ideal R) ↔ x = 0 := by
  simp

example (x : R) : x ∈ (⊤ : Ideal R) := by
  simp

end Ideals

/-!
## 3. A concrete ideal: multiples of an integer

`Ideal.span A` is the smallest ideal containing the set A. When A is the
singleton set `{a}`, this is the principal ideal generated by a: its elements
are precisely the multiples of a.

The annotation `({(2 : ℤ)} : Set ℤ)` tells Lean that we mean the singleton
SET of integers containing 2. The resulting ideal consists of all even
integers, not just the element 2.
-/

def evenIntegers : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)

example : (2 : ℤ) ∈ evenIntegers := by
  exact Ideal.mem_span_singleton_self (2 : ℤ)

-- `change` replaces a goal by a definitionally equal one; here it unfolds our name.
example (n : ℤ) : n ∈ evenIntegers ↔ (2 : ℤ) ∣ n := by
  change n ∈ Ideal.span ({(2 : ℤ)} : Set ℤ) ↔ (2 : ℤ) ∣ n
  exact Ideal.mem_span_singleton

/-
`a ∣ b` means "a divides b": there is a c with b = a*c.
`rw [Ideal.mem_span_singleton]` turns membership in a principal ideal into
divisibility. `refine ⟨witness, ?_⟩` supplies a witness and leaves its equation
as a new goal.
-/
example : (10 : ℤ) ∈ evenIntegers := by
  change (10 : ℤ) ∈ Ideal.span ({(2 : ℤ)} : Set ℤ)
  rw [Ideal.mem_span_singleton]
  refine ⟨5, ?_⟩
  norm_num

/-!
## 4. Ring homomorphisms: functions that preserve the operations

A ring homomorphism f : R → S preserves addition and multiplication and sends
1 to 1. It also sends 0 to 0 and preserves negatives, subtraction, and powers.
Lean bundles the function and its preservation proofs into the type `R →+* S`.
This is stronger than an ordinary function `R → S`.

We still apply f just like a function: `f x`. Lean automatically uses the
underlying function of the bundled homomorphism.

Examples: the identity map R → R, the inclusion ℤ → ℚ, and evaluation of
integer polynomials at a fixed integer are ring homomorphisms. The function
ℤ → ℤ given by n ↦ n+1 is not: it does not preserve 0.
-/

section Homs

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable (f : R →+* S) (g : S →+* T)

example (x y : R) : f (x + y) = f x + f y := by
  exact f.map_add x y

example (x y : R) : f (x * y) = f x * f y := by
  exact f.map_mul x y

example : f (1 : R) = 1 := by
  exact f.map_one

example : f (0 : R) = 0 := by
  exact f.map_zero

-- `rw` makes each step visible. The resulting identity is in the target ring S.
example (x y : R) : f (x * (y + 1)) = f x * (f y + 1) := by
  rw [map_mul, map_add, map_one]

-- `simp` can apply several preservation rules at once.
example (x y : R) : f (x ^ 2 - y) = (f x) ^ 2 - f y := by
  simp

-- First push f through the operations, then do algebra in S.
example (x y : R) : f ((x + y) ^ 2) = (f x) ^ 2 + 2 * f x * f y + (f y) ^ 2 := by
  rw [map_pow, map_add]
  ring

/-
Identity and composition are already bundled ring homomorphisms.
`g.comp f` means first f, then g. Its type is R →+* T.
These evaluation rules hold by definition, so `rfl` proves them.
-/
example (x : R) : (RingHom.id R) x = x := by
  rfl

example (x : R) : (g.comp f) x = g (f x) := by
  rfl

end Homs

/-
A concrete bundled homomorphism: send an integer to the same rational number.
`Int.castRingHom` supplies both the function and its preservation proofs.
The notation `(n : ℚ)` below means the cast of the integer n into ℚ.
-/
def integersToRationals : ℤ →+* ℚ := Int.castRingHom ℚ

example (n : ℤ) : integersToRationals n = (n : ℚ) := by
  rfl

example : integersToRationals (3 : ℤ) = (3 : ℚ) := by
  norm_num [integersToRationals]

/-!
## 5. Kernels: an ideal attached to a homomorphism

The kernel of f : R →+* S is the set of elements sent to zero:

    x ∈ RingHom.ker f  ↔  f x = 0.

It is an ideal of the SOURCE ring R. Why? If f x = 0 and f y = 0, then
f (x+y) = f x + f y = 0. Also, f (r*x) = f r * f x = 0 for any r.
The preservation laws similarly handle zero and negatives.

Mathlib has already packaged this ideal as `RingHom.ker f`. We can either use
its ideal closure properties or unfold membership using `RingHom.mem_ker`.
-/

section Kernels

variable {R S : Type*} [CommRing R] [CommRing S]
variable (f : R →+* S)

-- `.mp` uses the forward direction of an ↔; `.mpr` uses the reverse direction.
example (x : R) (hx : x ∈ RingHom.ker f) : f x = 0 := by
  exact RingHom.mem_ker.mp hx

example (x : R) (hx : f x = 0) : x ∈ RingHom.ker f := by
  exact RingHom.mem_ker.mpr hx

-- View the kernel as an ideal and use its API directly.
example (x y : R) (hx : x ∈ RingHom.ker f) (hy : y ∈ RingHom.ker f) :
    x + y ∈ RingHom.ker f := by
  exact (RingHom.ker f).add_mem hx hy

-- Or inspect why closure holds using the homomorphism laws.
-- `at hx ⊢` means rewrite both the hypothesis hx and the current goal.
example (r x : R) (hx : x ∈ RingHom.ker f) : r * x ∈ RingHom.ker f := by
  rw [RingHom.mem_ker] at hx ⊢
  rw [map_mul, hx, mul_zero]

/-
Optional extension: the preimage of any ideal J of S is an ideal of R.
It is called `J.comap f`, and x belongs to it exactly when f x belongs to J.
The kernel is the special case of taking the preimage of the zero ideal.
-/
example (J : Ideal S) (x : R) : x ∈ J.comap f ↔ f x ∈ J := by
  rfl

example (J : Ideal S) (x y : R) (hx : x ∈ J.comap f) (hy : y ∈ J.comap f) :
    x + y ∈ J.comap f := by
  exact (J.comap f).add_mem hx hy

end Kernels

/-!
## Toolbox and common sticking points

* Polynomial equality: try `ring`.
* Concrete arithmetic: try `norm_num`.
* Ideal membership: look for `I.zero_mem`, `I.add_mem`, `I.neg_mem`,
  `I.sub_mem`, `I.mul_mem_left`, or `I.mul_mem_right`.
* Principal ideal membership: `rw [Ideal.mem_span_singleton]`.
* A homomorphism applied to an expression: use `map_add`, `map_mul`,
  `map_zero`, `map_one`, `map_neg`, `map_sub`, or `map_pow`.
* Kernel membership: `rw [RingHom.mem_ker]`.
* To simplify a hypothesis, use `rw [...] at hx` or `simp [...] at hx`.
* To see a lemma's full statement, hover over its name or write `#check`.

Watch the types: x is in R, f x is in S, and RingHom.ker f is an Ideal R.
`I : Ideal R` is an object; `hx : x ∈ I` is a proof of membership.
An ideal need not contain 1. If it does, absorption forces it to contain every
ring element (one of the exercises below).

`sorry` tells Lean to accept a missing proof temporarily. Its warning is
expected in the exercise sheet; a declaration containing `sorry` is unfinished.
-/

/-!
## 6. Practice problems

Replace each `sorry` with a proof. Problems 1–4 are warm-ups; 5–9 combine tools;
10–12 connect homomorphisms and ideals. Problems 13–14 are optional challenges.
All the statements hold for arbitrary commutative rings unless a concrete
ring is explicitly specified. Try writing the mathematical argument first.
-/

namespace Exercises

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

-- 1. Expand a product. Hint: `ring`.
theorem ex01_difference_of_squares (x y : R) :
    (x + y) * (x - y) = x ^ 2 - y ^ 2 := by
  sorry

-- 2. Combine multiplication and addition in an ideal.
-- Hint: first prove a*x ∈ I, then add y.
theorem ex02_linear_expression (I : Ideal R) (a x y : R)
    (hx : x ∈ I) (hy : y ∈ I) : a * x + y ∈ I := by
  sorry

-- 3. Multiplication on the right. Hint: `I.mul_mem_right`.
theorem ex03_right_multiple (I : Ideal R) (x r : R) (hx : x ∈ I) :
    x * r ∈ I := by
  sorry

-- 4. Membership survives containment. Hint: use hIJ, then hJK.
theorem ex04_containment (I J K : Ideal R) (hIJ : I ≤ J) (hJK : J ≤ K)
    (x : R) (hx : x ∈ I) : x ∈ K := by
  sorry

-- 5. An ideal containing 1 contains every element.
-- Hint: I.mul_mem_left r h1 proves r*1 ∈ I; finish with `simpa`.
-- `simpa using h` simplifies the type of h and the goal, then matches them.
theorem ex05_contains_one (I : Ideal R) (h1 : (1 : R) ∈ I) (r : R) : r ∈ I := by
  sorry

-- 6. Factor before using absorption.
-- Hint: use `ring` to prove x^3-x = (x^2+x)*(x-1), then rewrite.
theorem ex06_factor_membership (I : Ideal R) (x : R) (hx : x - 1 ∈ I) :
    x ^ 3 - x ∈ I := by
  sorry

-- 7. A principal ideal in ℤ.
-- Hint: rewrite with Ideal.mem_span_singleton and supply a divisibility witness.
theorem ex07_multiple_of_three :
    (21 : ℤ) ∈ Ideal.span ({(3 : ℤ)} : Set ℤ) := by
  sorry

-- 8. Push a homomorphism through a product and a difference.
-- Hint: map_mul, map_sub, map_one; alternatively, `simp`.
theorem ex08_map_expression (f : R →+* S) (x y : R) :
    f (x * (y - 1)) = f x * (f y - 1) := by
  sorry

-- 9. Use preservation laws, then algebra in the target ring.
-- Hint: `rw [map_pow, map_sub]`, then `ring`.
theorem ex09_map_square (f : R →+* S) (x y : R) :
    f ((x - y) ^ 2) = (f x) ^ 2 - 2 * f x * f y + (f y) ^ 2 := by
  sorry

-- 10. Turn an equality about f into kernel membership.
-- Hint: rewrite with RingHom.mem_ker, then map_add and hx.
theorem ex10_sum_in_kernel (f : R →+* S) (x y : R) (hx : f x = -f y) :
    x + y ∈ RingHom.ker f := by
  sorry

-- 11. Two elements have the same image exactly when their difference is in the kernel.
-- Hint: RingHom.mem_ker, map_sub, and `sub_eq_zero`.
theorem ex11_difference_in_kernel (f : R →+* S) (x y : R) :
    x - y ∈ RingHom.ker f ↔ f x = f y := by
  sorry

-- 12. Relate composition and kernels.
-- Hint: `intro x hx`; turn hx into f x = 0. For the goal, use
-- `change g (f x) = 0` after rewriting kernel membership, then use map_zero.
theorem ex12_kernel_comp (f : R →+* S) (g : S →+* T) :
    RingHom.ker f ≤ RingHom.ker (g.comp f) := by
  sorry

-- 13. Optional: equality of ideals is equality of membership conditions.
-- Hint: `ext x` reduces ideal equality to an ↔; then `simp [RingHom.mem_ker]`.
theorem ex13_kernel_id : RingHom.ker (RingHom.id R) = (⊥ : Ideal R) := by
  sorry

-- 14. Optional: absorption in a preimage ideal, using the homomorphism laws.
-- Hint: `change f x ∈ J at hx` and `change f (r*x) ∈ J`;
-- rewrite map_mul and use J.mul_mem_left.
theorem ex14_preimage_multiple (f : R →+* S) (J : Ideal S) (r x : R)
    (hx : x ∈ J.comap f) : r * x ∈ J.comap f := by
  sorry

end Exercises

end Week3

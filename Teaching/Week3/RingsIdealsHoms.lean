import Mathlib.RingTheory.Ideal.Maps

/-!
## 1. Commutative Rings

Given a type `(R : Type)`, `Ring R` is the type of ring structures on `R`. Types like `ℤ`, `ℝ` and
`ℂ` have a canonical ring structure on them and it would be a pain to have to enter `Int.instRing`
every time we want ot apply a theorem about rings to `ℤ`. Fortunately, Lean's typeclass system
solves this for us. When stating the variables for a theorem, hard brackets tell Lean,
"go find this variable, it will not be given explicitly or implicitly". So to say "let R be a ring"
in Lean, we write `(R : Type) [Ring R]`.

-/


section Rings

lemma ring_add_comm (R : Type) [Ring R] (a b : R) : a + b = b + a := by
  rw [add_comm]

-- Note that when we apply this to `ℤ`, Lean automatically fills in the ring structure `Ring ℤ`
#check ring_add_comm ℤ

-- Lean can also find instances of `Ring R` from other typeclasses, like `Field`
example (F : Type) [Field F] (a b : F) : a + b = b + a := by
  exact ring_add_comm F a b

-- The `ring` tactic is able many simple goals related to commutative rings, which are written
-- `CommRing R` instead of `Ring R`
example {R : Type} [CommRing R] (a b : R) : a + b - b = a := by
  ring

-- Try proving these yourself. For a challenge, don't use ring.
example {R : Type} [CommRing R] (a b : R) (h : a = b + 1) :
    a ^ 2 = b ^ 2 + 2 * b + 1 := by
  sorry

example {R : Type} [CommRing R] (x y : R) :
    (x + y) * (x - y) = x ^ 2 - y ^ 2 := by
  sorry

end Rings

/-!
## 2. Ring homomorphisms

Ring homomorphisms are defined as "bundled", meaning the function and the fact that it respects
addition/multiplication are packaged together in the type `RingHom`. If `R` and `S` are rings, to
say "let `f` be a ring hom from `R` to `S`", we write `(f : RingHom R S)`. This is usually written
with the fancy notation, `(f : R →+* S)` but note that this is just syntactic sugar. You can apply
`f` to an element of `R` just like any other function, no parethesis needed.

-/

section Homs

example (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (x y : R) : f (x + y) = f x + f y := by
  exact f.map_add x y

-- Writing `(R S : Type) [CommRing R] [CommRing S] (f : R →+* S)` before every theorem would get
-- very tedious, the keyword `variable` makes it so they are automatically inserted at the start
-- of each theorem.

variable (R S : Type) [CommRing R] [CommRing S] (f : R →+* S)

example (x y : R) : f (x * y) = f x * f y := by
  exact f.map_mul x y

-- `simp` is the simplify tactic. Think of it as repeatedly applying `rw` with all the most used
-- lemmas. To see which lemmas it applied, change it to `simp?` and look in the infoview.
-- This can often be a quick way of searching for useful lemmas.
example (x y : R) : f (x ^ 2 - y) = (f x) ^ 2 - f y := by
  simp

example (x y : R) : f ((x - y) ^ 2) = (f x) ^ 2 - 2 * f x * f y + (f y) ^ 2 := by
  sorry
/-
To define our own ring hom, replace the sorry below with `?_` then click the blue lightbulb and
select "Generate a skeleton for the structure under construction". Then you will be asked to provide
a function along proofs that it maps 1 to 1, repects multiplication, etc. The `intro` tactic will
be very helpful for this one.
-/

def identityRingHom : R →+* R := sorry

/- Hint:
def identityRingHom : R →+* R where
  toFun := by
    intro x
    exact x
  map_one' := sorry
  map_mul' := by
    intro x y
    rfl
  map_zero' := sorry
  map_add' := sorry
-/

/-
To prove that two ring homs are equal, we can use the `ext` tactic which applies "extentionality"
lemmas. `ext` is often useful when trying to prove two things are equal. Try and finish this proof,
the `unfold` tactic may be useful as well.
-/
example : RingHom.id R = identityRingHom R := by
  ext x
  sorry

end Homs

/-!
## 3. Ideals

Like homomorphisms, ideals have the subset of the ring and the ideal properties bundled together.
Now we can finally use our favorite symbol `∈`. It is a predicate, where `r ∈ I` is the proposition
that `r` (which has type `R`) is contained in `I` (which has type `Ideal R`).

-/

section Ideals

variable {R : Type} [CommRing R]
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

-- Lets define the kernel of a ring hom. (clicking each variable in the `intro` line while looking
-- at the infoview help you see what is happening)
variable {S : Type} [CommRing S] (f : R →+* S)

def kernel : Ideal R where
  carrier := {r : R | f r = 0}
  add_mem' := by
    intro a b h1 h2
    simp
    simp at h1 h2
    rw [h1, h2]
    ring
  zero_mem' := sorry
  smul_mem' := sorry

example (I : Ideal R) (h1 : (1 : R) ∈ I) (r : R) : r ∈ I := by
  sorry

/- The following statement is that the kernel of the identity is `0`. While putting `0` would
actually work here, `⊥` (which means the "bottom" element of an order type) is generally prefered.
`ext` will help when you need to prove two ideals are equal and `constructor` will split an iff into
two cases.
-/
example : RingHom.ker (RingHom.id R) = ⊥ := by
  sorry

/- For a very hard challenge, try proving this classic theorem. `constructor` will split the iff into
two cases and `ext` will help when you need to prove two ideals are equal. -/
example : Function.Injective f ↔ RingHom.ker f = ⊥ := by
  sorry

end Ideals

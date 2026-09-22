# Week 3: commutative rings, ideals, and ring homomorphisms

Give students **[RingsIdealsHoms.lean](RingsIdealsHoms.lean)**. It is a self-contained,
commented tutorial with worked proofs and 14 exercises ending in `sorry`.
Keep **[Solutions.lean](Solutions.lean)** as the instructor answer key.

Students need basic Lean syntax and tactics, but no previous ring theory.
The lesson introduces the mathematics before its Lean notation and uses even
integers as a concrete ideal. It covers ring identities, ideal closure and
containment, principal ideals, bundled homomorphisms, composition, and kernels.
Preimages of ideals and the last two exercises are optional extensions.

Allow about 85 minutes including practice. For a 50-minute class, use sections
1–4 in class and assign kernels and exercises as follow-up work. During worked
proofs, ask students to predict the next goal before stepping through the tactic.

Open the student file in VS Code with the Lean extension, inside this mathlib
project. Students using a separate course mathlib project can copy the file into
that project. The imports require mathlib, not just a bare Lean installation.

From this repository's root, check the files with:

```sh
lake env lean Teaching/Week3/RingsIdealsHoms.lean
lake env lean Teaching/Week3/Solutions.lean
```

The student file should produce exactly 14 `declaration uses sorry` warnings,
one per exercise, and no errors. The answer key should check without warnings
or missing proofs. It does not import the unfinished student exercises.

Prepared for this checkout's Lean `v4.34.0-rc2` and mathlib revision
`e061065a68d`. Earlier course checkouts may have different lemma names.

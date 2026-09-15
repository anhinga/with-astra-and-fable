# Aleph-one algebraicity of fixed points

**Status: verified in Lean 4.34.0-rc2 at lean.math.hhu.de on 2026-09-15.**

This project translates the proof in `aleph-one-algebraicity.tex` into Lean 4
using mathlib's standard `ScottContinuous`, `Set.Countable`, `Set.Finite`,
subtype order, and `IsLUB`. Lean accepted the complete proof and its axiom
checks with zero errors and zero warnings. Both conclusion theorems depend
on exactly `propext`, `Classical.choice`, and `Quot.sound`. Neither depends on
`sorryAx`, an added axiom, or an assumed intermediate lemma.

The mathematical argument needed no correction. The compiler fixes were a
finite-set helper invocation and three instance-binding style adjustments.

## Main statement

In namespace `AlephOneAlgebraicity`:

```lean
theorem fixedPoints_alephOne_algebraic (hf : ScottContinuous f)
    (A : FixedPoints f) :
    IsLUB {K : FixedPoints f | K ≤ A ∧ AlephOneCompact K} A
```

`FixedPoints f` is the subtype `{A : Set S // f A = A}`, ordered by inclusion.
The theorem is universe-polymorphic and imposes no cardinality restriction on
`S`. `CountablyDirected D` explicitly requires nonemptiness and a bound in
`D` for each countable subset of `D`. `AlephOneCompact` quantifies over such
families and over their least upper bounds when these exist.

Using `IsLUB` states exactly the supremum assertion in the fixed-point poset
without selecting a complete-lattice instance. The separate theorem
`fixedPoint_eq_union_compacts` expresses the conclusion as equality of sets.

## Correspondence with the supplied proof

| Mathematical step | Lean declaration |
| --- | --- |
| Preservation of directed unions | `scott_iUnion` |
| Finite witnesses from Scott continuity | `finite_witness` |
| Directed joins of fixed points are unions | `fixedUnion_fixed`, `fixedUnion_isLUB` |
| Countable witness-closed seed inside a fixed point | `countable_postfixed_seed` |
| Ascending iteration and its union | `iterates`, `omegaClosure` |
| The union of the iterates is fixed | `omegaClosure_fixed` |
| Leastness above the seed | `omegaClosure_least` |
| Countable generators imply aleph-one compactness | `omegaClosure_compact` |
| A compact approximation containing each token | `exists_compact_mem` |
| Supremum of all compact approximations | `fixedPoints_alephOne_algebraic` |

The seed lemma allows an arbitrary countable initial subset `C`, instead of
only a singleton. Consequently the stages are proved countable directly.
For the singleton construction in the original proof, the stronger assertion
that every stage is finite follows from the same finite-union argument, but
is not needed for this formalization. The resulting fixed point is never
assumed countable.

## Reproduce the check

For the online check, paste the entire `OnlineCheck.lean` file into
[the Lean editor](https://lean.math.hhu.de/) with **Latest Mathlib** selected.
It contains the exact main source followed by the statement checks, guarded
axiom reports, compiler-version output, and a final completion marker.
Success requires zero errors and zero warnings; the completion marker by
itself is insufficient because Lean can continue after a failed declaration.

For a local check, use the Lake project:

Install Lean's `elan` toolchain manager using the
[official Lean installation instructions](https://lean-lang.org/install/).
From this directory run:

```sh
lake update
lake exe cache get
lake build
lake env lean Check.lean
```

The local project pins Lean to `v4.34.0-rc2` and mathlib to commit
`85e3a25e006c35636f0e53b0e9296caca2685bc0`, the mathlib release tag
`v4.34.0-rc2`. Mathlib's manifest fixes its transitive dependencies.
The cache command downloads precompiled dependencies; it does not check this
project's new theorems. `lake build` is the required compilation step.
The verified environment was the online editor's installed mathlib; its exact
mathlib commit was not exposed by the UI. The local project uses the matching
mathlib release, but a local Lake build was not run in this workspace.

`Check.lean` uses `#guard_msgs` to require exactly the observed axiom reports.
An added dependency such as `sorryAx` or an assumed mathematical lemma causes
these checks to fail. The same guards passed in the online verification.

## Verification record

- `verification-output.txt` records the editor's final messages and a source
  identity check.
- `OnlineCheck.lean` is the exact text submitted and checked. Copying the
  editor content back and comparing it with this file confirmed byte-for-byte
  equality. Its SHA-256 is
  `87e8f30c94228024ce5b7ba3b0293210802376d7e8cabc67546ac3b7c54ac30b`.
- The editor reported eight informational messages, zero errors, and zero
  warnings, including the two axiom reports and `VERIFICATION COMPLETE`.
- The local compiler failed at startup with `error: failed to locate
  application`, so the successful verification used the authorized online
  editor. No local compilation success is claimed.

The transcript documents the observed run; it is not a proof certificate.
The Lean source is the reproducible mathematical artifact.

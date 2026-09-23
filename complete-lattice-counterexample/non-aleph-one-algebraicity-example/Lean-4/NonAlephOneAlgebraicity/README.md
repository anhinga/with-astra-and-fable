# Non-ℵ₁-algebraicity of the open-set lattice of (ω₁)^ℕ

The theorem and corollary in `non-aleph-one-algebraicity.tex` have been formalized
and checked in Lean 4.23.0 with Mathlib v4.23.0. The complete Lake project builds
successfully. There are no `sorry` or `admit` placeholders and no added axioms.

The final axiom audit for the chain construction, compactness classification,
and corollary reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean's standard classical foundations. In particular, the verification
uses the full axiom of choice, as permitted in the manuscript. It does not
formalize the separate metamathematical assertion that countable choice suffices.

## Correspondence with the manuscript

`OmegaOne` is a type with order type exactly ω₁, obtained from Mathlib's
`Ordinal.omega 1`. Its cardinality is formally proved to be ℵ₁. It is explicitly
given the **discrete topology**. `BaireSpace` is `ℕ → OmegaOne` with Mathlib's
product topology, and `OpenLattice` is its standard complete lattice of open sets.

`CountablyDirected D` means that D is nonempty and each countable subset of D
has an upper bound belonging to D. `AlephOneCompact` uses precisely these sets
and their lattice suprema.

The formal proof follows the manuscript's construction:

1. Find a finite-coordinate cylinder V inside a nonempty open set U.
2. Choose a coordinate j not fixed by V; changing that coordinate to any value
   in ω₁ preserves membership in V.
3. Define the open slices V_ξ and the open sets
   U_α = (U \ V) ∪ {x ∈ V | x(j) < α}.
4. Prove that this formula equals (U \ V) ∪ ⋃_{ξ<α} V_ξ.
5. Prove that the chain is strictly increasing, each member is strictly below
   U, and its supremum is U.
6. Use Mathlib's regularity theorem for ω₁ to bound every countable set of
   indices, and thereby prove that the chain's range is countably directed.

The manuscript has one indexing typo: the slice V_ξ fixes the indices
**I ∪ {j}**, not I ∩ {j}. The construction in Lean uses the intended union.
The unfinished sentence after the countable-upper-bound argument is completed
by the formal `countablyDirected_range` lemma. No substantive mathematical
change to the argument was needed.

All declarations are in the `NonAlephOneAlgebraicity` namespace:

| Declaration | Result |
|---|---|
| `exists_strict_chain` | The strictly increasing, countably directed ω₁-chain of proper open subsets with supremum U |
| `mk_range_strictMono` | Such a chain has exactly ℵ₁ distinct members |
| `not_alephOneCompact_of_ne_bot` | Every nonempty open set fails ℵ₁-compactness |
| `alephOneCompact_iff_eq_bot` | An open set is ℵ₁-compact exactly when it is empty |
| `sSup_compact_eq_bot` | Every supremum of ℵ₁-compact open sets is empty |
| `not_alephOneAlgebraic` | The open-set lattice is not ℵ₁-algebraic |

Here `AlephOneAlgebraic` means that every element is the supremum of the compact
elements below it. The stronger result `sSup_compact_eq_bot` also rules out the
definition requiring a countably directed family of compact approximants.

## Reproduce the verification

Install Lean using [elan](https://github.com/leanprover/elan), then extract this
project and run these commands from its directory:

```sh
lake exe cache get Mathlib.SetTheory.Cardinal.Regular Mathlib.Topology.Constructions Mathlib.Topology.Sets.Opens
lake build
```

The supplied `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin Lean,
Mathlib, and all transitive dependencies. Mathlib is pinned to commit
`37df177aaa770670452312393d4e84aaad56e7b6` (tag `v4.23.0`). A newer Mathlib
version is not required and was not tested.

To display the axiom audit directly:

```sh
lake env lean NonAlephOneAlgebraicity.lean
```

`verification.txt` records the compiler version, source hash, and successful
build output. The archive contains the source and project configuration;
dependencies and compiled artifacts are fetched or built locally.

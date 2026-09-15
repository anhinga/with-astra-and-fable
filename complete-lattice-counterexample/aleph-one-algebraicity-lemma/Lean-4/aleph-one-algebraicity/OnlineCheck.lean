import Mathlib

/-!
# Aleph-one algebraicity of fixed points of a Scott-continuous powerset map

Verified with Lean 4.34.0-rc2 in lean.math.hhu.de's mathlib environment.
The main theorems use only propext, Classical.choice, and Quot.sound.

Formalization of the argument in `aleph-one-algebraicity.tex`.
There is no countability assumption on the ambient type `S`.
All suprema in the main statement are expressed by `IsLUB` in the fixed-point
subtype, so no choice of a complete-lattice instance is needed.
-/

open Set

set_option autoImplicit false

universe u v

namespace AlephOneAlgebraicity

/-- Nonempty, with an upper bound in `D` for every countable subset of `D`.
Here countable includes finite and empty sets. -/
def CountablyDirected {P : Type u} [Preorder P] (D : Set P) : Prop :=
  D.Nonempty ∧ ∀ C : Set P, C ⊆ D → C.Countable →
    ∃ d ∈ D, ∀ c ∈ C, c ≤ d

/-- Compactness with respect to countably directed suprema that exist in `P`. -/
def AlephOneCompact {P : Type u} [Preorder P] (k : P) : Prop :=
  ∀ D : Set P, CountablyDirected D → ∀ x : P,
    IsLUB D x → k ≤ x → ∃ d ∈ D, k ≤ d

theorem CountablyDirected.directedOn {P : Type u} [Preorder P]
    {D : Set P} (hD : CountablyDirected D) : DirectedOn (· ≤ ·) D := by
  intro x hx y hy
  obtain ⟨z, hz, h⟩ := hD.2 {x, y}
    (by intro c hc; simp only [mem_insert_iff, mem_singleton_iff] at hc
        rcases hc with rfl | rfl <;> assumption)
    (by simp)
  exact ⟨z, hz, h x (by simp), h y (by simp)⟩

variable {S : Type u} {f : Set S → Set S}

/-- The fixed-point poset, ordered by inclusion through the subtype order. -/
abbrev FixedPoints (f : Set S → Set S) := {A : Set S // f A = A}

/-- Scott continuity, in mathlib's standard definition, preserves nonempty
directed indexed unions of subsets. -/
theorem scott_iUnion (hf : ScottContinuous f) {I : Type v} [Nonempty I]
    (V : I → Set S) (hV : Directed (· ⊆ ·) V) :
    f (⋃ i, V i) = ⋃ i, f (V i) := by
  classical
  have hdir : DirectedOn (· ≤ ·) (Set.range V) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := hV i j
    exact ⟨V k, ⟨k, rfl⟩, hik, hjk⟩
  have hlub : IsLUB (Set.range V) (⋃ i, V i) := by
    constructor
    · rintro _ ⟨i, rfl⟩
      exact subset_iUnion V i
    · intro Z hZ a ha
      obtain ⟨i, hi⟩ := mem_iUnion.mp ha
      exact hZ ⟨i, rfl⟩ hi
  have himage := hf (Set.range_nonempty V) hdir hlub
  apply le_antisymm
  · apply himage.2
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact subset_iUnion (fun i => f (V i)) i
  · intro a ha
    obtain ⟨i, hi⟩ := mem_iUnion.mp ha
    exact himage.1 ⟨V i, ⟨i, rfl⟩, rfl⟩ hi

/-- Every output token has a finite input witness. -/
theorem finite_witness (hf : ScottContinuous f) {A : Set S} {b : S}
    (hb : b ∈ f A) : ∃ U : Set S, U.Finite ∧ U ⊆ A ∧ b ∈ f U := by
  classical
  let I := {U : Set S // U.Finite ∧ U ⊆ A}
  let V : I → Set S := Subtype.val
  let : Nonempty I := ⟨⟨∅, finite_empty, empty_subset A⟩⟩
  have hdir : Directed (· ⊆ ·) V := by
    intro i j
    exact ⟨⟨i.val ∪ j.val, i.property.1.union j.property.1,
      union_subset i.property.2 j.property.2⟩,
      subset_union_left, subset_union_right⟩
  have hcover : (⋃ i, V i) = A := by
    apply Subset.antisymm
    · intro a ha
      obtain ⟨i, hi⟩ := mem_iUnion.mp ha
      exact i.property.2 hi
    · intro a ha
      exact mem_iUnion.mpr ⟨⟨{a}, finite_singleton a,
        singleton_subset_iff.mpr ha⟩, mem_singleton a⟩
  have heq := scott_iUnion hf V hdir
  rw [hcover] at heq
  rw [heq] at hb
  obtain ⟨i, hi⟩ := mem_iUnion.mp hb
  exact ⟨i.val, i.property.1, i.property.2, hi⟩

/-- The union of a family of fixed points, viewed as a subset of `S`. -/
def fixedUnion (D : Set (FixedPoints f)) : Set S := ⋃ d : D, d.val.val

theorem fixedUnion_fixed (hf : ScottContinuous f) {D : Set (FixedPoints f)}
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) :
    f (fixedUnion D) = fixedUnion D := by
  classical
  let : Nonempty D := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hV : Directed (· ⊆ ·) (fun d : D => d.val.val) := by
    intro i j
    obtain ⟨k, hk, hik, hjk⟩ := hdir i.val i.property j.val j.property
    exact ⟨⟨k, hk⟩, hik, hjk⟩
  unfold fixedUnion
  rw [scott_iUnion hf _ hV]
  congr 1
  funext d
  exact d.val.property

/-- Directed joins in the fixed-point poset are unions. -/
theorem fixedUnion_isLUB (hf : ScottContinuous f) {D : Set (FixedPoints f)}
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) :
    IsLUB D ⟨fixedUnion D, fixedUnion_fixed hf hne hdir⟩ := by
  constructor
  · intro d hd a ha
    exact mem_iUnion.mpr ⟨⟨d, hd⟩, ha⟩
  · intro z hz a ha
    obtain ⟨d, hd⟩ := mem_iUnion.mp ha
    exact hz d.property hd

/-- Close a countable seed under its chosen finite witnesses. Allowing a
countable initial seed slightly generalizes the singleton construction. -/
theorem countable_postfixed_seed (hf : ScottContinuous f)
    {A C : Set S} (hA : f A = A) (hC : C.Countable) (hCA : C ⊆ A) :
    ∃ B : Set S, B.Countable ∧ C ⊆ B ∧ B ⊆ A ∧ B ⊆ f B := by
  classical
  have hw : ∀ b : S, ∃ U : Set S,
      U.Finite ∧ U ⊆ A ∧ (b ∈ A → b ∈ f U) := by
    intro b
    by_cases hb : b ∈ A
    · obtain ⟨U, hUf, hUA, hbU⟩ := finite_witness hf (hA.symm ▸ hb)
      exact ⟨U, hUf, hUA, fun _ => hbU⟩
    · exact ⟨∅, finite_empty, empty_subset A, fun h => (hb h).elim⟩
  choose U hUf hUA hbU using hw
  let stages : ℕ → Set S := fun n =>
    Nat.rec C (fun _ B => B ∪ ⋃ b ∈ B, U b) n
  have stage_countable : ∀ n, (stages n).Countable := by
    intro n
    induction n with
    | zero => exact hC
    | succ n ih => exact ih.union (ih.biUnion (fun b _ => (hUf b).countable))
  have stage_subset : ∀ n, stages n ⊆ A := by
    intro n
    induction n with
    | zero => exact hCA
    | succ n ih =>
      intro a ha
      rcases ha with ha | ha
      · exact ih ha
      · obtain ⟨b, hb⟩ := mem_iUnion.mp ha
        obtain ⟨_, hab⟩ := mem_iUnion.mp hb
        exact hUA b hab
  let B : Set S := ⋃ n, stages n
  have hBA : B ⊆ A := by
    intro b hb
    obtain ⟨n, hn⟩ := mem_iUnion.mp hb
    exact stage_subset n hn
  refine ⟨B, countable_iUnion stage_countable, ?_, hBA, ?_⟩
  · intro c hc
    exact mem_iUnion.mpr ⟨0, hc⟩
  · intro b hb
    obtain ⟨n, hn⟩ := mem_iUnion.mp hb
    have hUB : U b ⊆ B := by
      intro c hc
      apply mem_iUnion.mpr
      refine ⟨n + 1, Or.inr ?_⟩
      exact mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hn, hc⟩⟩
    exact hf.monotone hUB (hbU b (hBA (mem_iUnion.mpr ⟨n, hn⟩)))

/-- The ascending iteration from a postfixed seed. -/
def iterates (f : Set S → Set S) (B : Set S) : ℕ → Set S
  | 0 => B
  | n + 1 => f (iterates f B n)

def omegaClosure (f : Set S → Set S) (B : Set S) : Set S :=
  ⋃ n, iterates f B n

theorem seed_subset_closure (B : Set S) : B ⊆ omegaClosure f B := by
  intro b hb
  exact mem_iUnion.mpr ⟨0, hb⟩

theorem iterates_monotone (hf : Monotone f) {B : Set S} (hB : B ⊆ f B) :
    Monotone (iterates f B) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact hB
  | succ n ih => exact hf ih

theorem omegaClosure_fixed (hf : ScottContinuous f) {B : Set S}
    (hB : B ⊆ f B) : f (omegaClosure f B) = omegaClosure f B := by
  have hm := iterates_monotone hf.monotone hB
  have hd : Directed (· ⊆ ·) (iterates f B) := by
    intro m n
    exact ⟨max m n, hm (le_max_left m n), hm (le_max_right m n)⟩
  unfold omegaClosure
  rw [scott_iUnion hf _ hd]
  apply Subset.antisymm
  · intro b hb
    obtain ⟨n, hn⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨n + 1, hn⟩
  · intro b hb
    obtain ⟨n, hn⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨n, hm (Nat.le_succ n) hn⟩

/-- Leastness actually holds among all prefixed supersets of the seed. -/
theorem omegaClosure_least (hf : Monotone f) {B A : Set S}
    (hBA : B ⊆ A) (hA : f A ⊆ A) : omegaClosure f B ⊆ A := by
  have h : ∀ n, iterates f B n ⊆ A := by
    intro n
    induction n with
    | zero => exact hBA
    | succ n ih => exact (hf ih).trans hA
  intro b hb
  obtain ⟨n, hn⟩ := mem_iUnion.mp hb
  exact h n hn

/-- A fixed point generated from a countable postfixed seed is aleph-one
compact. The resulting fixed point is not assumed countable. -/
theorem omegaClosure_compact (hf : ScottContinuous f) {B : Set S}
    (hBc : B.Countable) (hB : B ⊆ f B) :
    AlephOneCompact (⟨omegaClosure f B, omegaClosure_fixed hf hB⟩ : FixedPoints f) := by
  classical
  intro D hD x hx hKx
  have hU := fixedUnion_isLUB hf hD.1 hD.directedOn
  have hxU : x ≤ ⟨fixedUnion D, fixedUnion_fixed hf hD.1 hD.directedOn⟩ :=
    hx.2 hU.1
  have hBU : B ⊆ fixedUnion D :=
    (seed_subset_closure B).trans (hKx.trans hxU)
  have hchoose : ∀ b : B, ∃ d : FixedPoints f, d ∈ D ∧ b.val ∈ d.val := by
    intro b
    obtain ⟨d, hd⟩ := mem_iUnion.mp (hBU b.property)
    exact ⟨d.val, d.property, hd⟩
  choose d hd hbd using hchoose
  let : Countable B := hBc
  obtain ⟨z, hz, hbound⟩ := hD.2 (Set.range d)
    (by rintro _ ⟨b, rfl⟩; exact hd b) (countable_range d)
  refine ⟨z, hz, omegaClosure_least hf.monotone ?_ (le_of_eq z.property)⟩
  intro b hb
  exact hbound (d ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩ (hbd ⟨b, hb⟩)

/-- Every countable subset of a fixed point lies in an aleph-one-compact
fixed point below it. This includes the empty seed. -/
theorem countable_subset_compact (hf : ScottContinuous f) (A : FixedPoints f)
    {C : Set S} (hCc : C.Countable) (hCA : C ⊆ A.val) :
    ∃ K : FixedPoints f, K ≤ A ∧ AlephOneCompact K ∧ C ⊆ K.val := by
  obtain ⟨B, hBc, hCB, hBA, hB⟩ :=
    countable_postfixed_seed hf A.property hCc hCA
  exact ⟨⟨omegaClosure f B, omegaClosure_fixed hf hB⟩,
    omegaClosure_least hf.monotone hBA (le_of_eq A.property),
    omegaClosure_compact hf hBc hB,
    hCB.trans (seed_subset_closure B)⟩

/-- The token-by-token approximation claimed in the attached proof. -/
theorem exists_compact_mem (hf : ScottContinuous f) (A : FixedPoints f)
    {a : S} (ha : a ∈ A.val) :
    ∃ K : FixedPoints f, K ≤ A ∧ AlephOneCompact K ∧ a ∈ K.val := by
  obtain ⟨K, hKA, hK, haK⟩ := countable_subset_compact hf A
    (countable_singleton a) (singleton_subset_iff.mpr ha)
  exact ⟨K, hKA, hK, haK (mem_singleton a)⟩

/-- **Main lemma.** Every fixed point is the supremum, in the fixed-point
poset, of the aleph-one-compact fixed points below it. -/
theorem fixedPoints_alephOne_algebraic (hf : ScottContinuous f)
    (A : FixedPoints f) :
    IsLUB {K : FixedPoints f | K ≤ A ∧ AlephOneCompact K} A := by
  constructor
  · intro K hK
    exact hK.1
  · intro X hX a ha
    obtain ⟨K, hKA, hK, haK⟩ := exists_compact_mem hf A ha
    exact hX ⟨hKA, hK⟩ haK

/-- The same conclusion written as equality of subsets of `S`. -/
theorem fixedPoint_eq_union_compacts (hf : ScottContinuous f)
    (A : FixedPoints f) :
    A.val = ⋃ K : {K : FixedPoints f // K ≤ A ∧ AlephOneCompact K}, K.val.val := by
  apply Subset.antisymm
  · intro a ha
    obtain ⟨K, hKA, hK, haK⟩ := exists_compact_mem hf A ha
    exact mem_iUnion.mpr ⟨⟨K, hKA, hK⟩, haK⟩
  · intro a ha
    obtain ⟨K, haK⟩ := mem_iUnion.mp ha
    exact K.property.1 haK

end AlephOneAlgebraicity


/- Print the precise statements and check their transitive axiom dependencies.
   Run this file after a successful `lake build`.
   Each guard fails if the axiom report changes, including addition of sorryAx
   or an extra assumed mathematical lemma. -/

#check AlephOneAlgebraicity.CountablyDirected
#check AlephOneAlgebraicity.AlephOneCompact
#check AlephOneAlgebraicity.fixedPoints_alephOne_algebraic
#check AlephOneAlgebraicity.fixedPoint_eq_union_compacts

/-- info: 'AlephOneAlgebraicity.fixedPoints_alephOne_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlephOneAlgebraicity.fixedPoints_alephOne_algebraic

/-- info: 'AlephOneAlgebraicity.fixedPoint_eq_union_compacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlephOneAlgebraicity.fixedPoint_eq_union_compacts

#eval Lean.versionString
#print axioms AlephOneAlgebraicity.fixedPoints_alephOne_algebraic
#print axioms AlephOneAlgebraicity.fixedPoint_eq_union_compacts
#eval "VERIFICATION COMPLETE"

import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sets.Opens

set_option autoImplicit false

/-!
# The open-set lattice of the discrete product (ω₁)^ℕ

Formalization of `non-aleph-one-algebraicity.tex`.
The topology on each copy of ω₁ is explicitly discrete.
The construction follows the original strictly increasing ω₁-chain.

Checked with Lean 4.23.0 and Mathlib v4.23.0.
-/

noncomputable section

open Set TopologicalSpace
open scoped Ordinal Cardinal

namespace NonAlephOneAlgebraicity

universe u

/-- Nonempty, with an internal upper bound for every countable subset. -/
def CountablyDirected {P : Type u} [Preorder P] (D : Set P) : Prop :=
  D.Nonempty ∧ ∀ C : Set P, C ⊆ D → C.Countable →
    ∃ d ∈ D, ∀ c ∈ C, c ≤ d

/-- Compactness with respect to suprema of countably directed sets. -/
def AlephOneCompact {P : Type u} [CompleteLattice P] (k : P) : Prop :=
  ∀ D : Set P, CountablyDirected D → k ≤ sSup D → ∃ d ∈ D, k ≤ d

/-- Every element is the supremum of the ℵ₁-compact elements below it. -/
def AlephOneAlgebraic (P : Type u) [CompleteLattice P] : Prop :=
  ∀ x : P, x = sSup {k : P | AlephOneCompact k ∧ k ≤ x}

theorem bot_alephOneCompact {P : Type u} [CompleteLattice P] :
    AlephOneCompact (⊥ : P) := by
  intro D hD _
  obtain ⟨d, hd⟩ := hD.1
  exact ⟨d, hd, bot_le⟩

/-- A small type with exactly the order type of the first uncountable ordinal. -/
def OmegaOne : Type := (ω₁ : Ordinal.{0}).toType

theorem mk_omegaOne : Cardinal.mk OmegaOne = ℵ₁ := by
  simp [OmegaOne, Cardinal.mk_toType, Ordinal.card_omega]

instance : LinearOrder OmegaOne :=
  inferInstanceAs (LinearOrder (ω₁ : Ordinal.{0}).toType)

def ordinalEquiv : Set.Iio (ω₁ : Ordinal.{0}) ≃o OmegaOne :=
  Ordinal.enumIsoToType _

def rank (a : OmegaOne) : Ordinal.{0} := (ordinalEquiv.symm a).val

theorem rank_lt (a : OmegaOne) : rank a < (ω₁ : Ordinal.{0}) :=
  (ordinalEquiv.symm a).property

instance : Nonempty OmegaOne :=
  ⟨ordinalEquiv ⟨0, Ordinal.omega_pos 1⟩⟩

instance : TopologicalSpace OmegaOne := ⊥
instance : DiscreteTopology OmegaOne := ⟨rfl⟩

theorem exists_larger (a : OmegaOne) : ∃ b : OmegaOne, a < b := by
  let b : OmegaOne := ordinalEquiv
    ⟨Order.succ (rank a), (Cardinal.isSuccLimit_omega 1).succ_lt (rank_lt a)⟩
  refine ⟨b, ?_⟩
  apply ordinalEquiv.symm.lt_iff_lt.mp
  change (ordinalEquiv.symm a).val < (ordinalEquiv.symm b).val
  simp [b, rank]

/-- Regularity of ω₁, in exactly the form needed for countable directedness. -/
theorem countable_bounded (S : Set OmegaOne) (hS : S.Countable) :
    ∃ b : OmegaOne, ∀ a ∈ S, a ≤ b := by
  letI : Countable S := hS.to_subtype
  let o : Ordinal.{0} := ⨆ a : S, rank a.val
  have ho : o < (ω₁ : Ordinal.{0}) := by
    simpa only [Cardinal.ord_aleph] using
      (Ordinal.iSup_sequence_lt_omega1 (fun a : S => rank a.val)
        (fun a => by simpa only [Cardinal.ord_aleph] using rank_lt a.val))
  refine ⟨ordinalEquiv ⟨o, ho⟩, ?_⟩
  intro a ha
  apply ordinalEquiv.symm.le_iff_le.mp
  change (ordinalEquiv.symm a).val ≤
    (ordinalEquiv.symm (ordinalEquiv ⟨o, ho⟩)).val
  simpa only [OrderIso.symm_apply_apply] using
    (Ordinal.le_iSup (fun a : S => rank a.val) ⟨a, ha⟩)

/-- A strictly increasing ω₁-indexed family has countably directed range. -/
theorem countablyDirected_range {P : Type u} [PartialOrder P]
    (F : OmegaOne → P) (hF : StrictMono F) : CountablyDirected (range F) := by
  refine ⟨Set.range_nonempty F, ?_⟩
  intro C hC hcount
  obtain ⟨b, hb⟩ := countable_bounded (F ⁻¹' C) (hcount.preimage hF.injective)
  refine ⟨F b, mem_range_self b, ?_⟩
  intro c hc
  obtain ⟨a, rfl⟩ := hC hc
  exact hF.monotone (hb a hc)

abbrev BaireSpace := ℕ → OmegaOne
abbrev OpenLattice := Opens BaireSpace

/-- The strictly increasing chains below have exactly ℵ₁ distinct members. -/
theorem mk_range_strictMono (F : OmegaOne → OpenLattice) (hF : StrictMono F) :
    Cardinal.mk (range F) = ℵ₁ :=
  (Cardinal.mk_range_eq F hF.injective).trans mk_omegaOne

/-- A basic cylinder fixes the finitely many coordinates in `I`. -/
def cylinder (I : Finset ℕ) (x : BaireSpace) : OpenLattice :=
  ⟨(I : Set ℕ).pi (fun i => {x i}),
    isOpen_set_pi I.finite_toSet (fun _ _ => isOpen_discrete _)⟩

theorem mem_cylinder (I : Finset ℕ) (x y : BaireSpace) :
    y ∈ cylinder I x ↔ ∀ i ∈ I, y i = x i := by
  rfl

theorem cylinder_closed (I : Finset ℕ) (x : BaireSpace) :
    IsClosed (cylinder I x : Set BaireSpace) :=
  isClosed_set_pi (fun _ _ => isClosed_discrete _)

/-- Every nonempty open set contains a nonempty cylinder. -/
theorem exists_cylinder (U : OpenLattice) (hU : U ≠ ⊥) :
    ∃ (I : Finset ℕ) (x : BaireSpace), cylinder I x ≤ U := by
  obtain ⟨x, hx⟩ := U.ne_bot_iff_nonempty.mp hU
  obtain ⟨I, s, hs, hsub⟩ := isOpen_pi_iff.mp U.isOpen x hx
  refine ⟨I, x, ?_⟩
  intro y hy
  apply hsub
  intro i hi
  rw [(mem_cylinder I x y).mp hy i hi]
  exact (hs i hi).2

/-- A coordinate not fixed by a cylinder can take any ordinal value. -/
theorem update_mem_cylinder (I : Finset ℕ) (x : BaireSpace)
    (j : ℕ) (hj : j ∉ I) (a : OmegaOne) :
    Function.update x j a ∈ cylinder I x := by
  apply (mem_cylinder I x _).mpr
  intro i hi
  have hij : i ≠ j := by
    intro h
    exact hj (h ▸ hi)
  exact Function.update_of_ne hij a x

/-- The slice V_a = {y ∈ V | y(j) = a}; this adds j to the fixed indices. -/
def slice (V : OpenLattice) (j : ℕ) (a : OmegaOne) : OpenLattice :=
  ⟨(V : Set BaireSpace) ∩ {y | y j = a},
    V.isOpen.inter ((isOpen_discrete ({a} : Set OmegaOne)).preimage
      (continuous_apply j : Continuous (fun y : BaireSpace => y j)))⟩

/-- U_a = (U \ V) ∪ {y ∈ V | y(j) < a}. -/
def approximation (U V : OpenLattice) (hV : IsClosed (V : Set BaireSpace))
    (j : ℕ) (a : OmegaOne) : OpenLattice :=
  ⟨((U : Set BaireSpace) \ V) ∪ ((V : Set BaireSpace) ∩ {y | y j < a}),
    (U.isOpen.sdiff hV).union
      (V.isOpen.inter ((isOpen_discrete (Set.Iio a)).preimage
        (continuous_apply j : Continuous (fun y : BaireSpace => y j))))⟩

/-- The formula above is exactly the union-of-slices formula in the manuscript. -/
theorem approximation_eq_union_slices (U V : OpenLattice)
    (hV : IsClosed (V : Set BaireSpace)) (j : ℕ) (a : OmegaOne) :
    (approximation U V hV j a : Set BaireSpace) =
      ((U : Set BaireSpace) \ V) ∪ ⋃ b < a, (slice V j b : Set BaireSpace) := by
  ext y
  simp only [approximation, slice, Opens.coe_mk, mem_union, mem_inter_iff,
    mem_setOf_eq, mem_iUnion]
  constructor
  · rintro (h | ⟨hy, hlt⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y j, hlt, hy, rfl⟩
  · rintro (h | ⟨b, hba, hy, heq⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hy, heq.symm ▸ hba⟩

theorem approximation_le (U V : OpenLattice)
    (hV : IsClosed (V : Set BaireSpace)) (hVU : V ≤ U)
    (j : ℕ) (a : OmegaOne) : approximation U V hV j a ≤ U := by
  intro y hy
  rcases hy with h | h
  · exact h.1
  · exact hVU h.1

theorem approximation_monotone (U V : OpenLattice)
    (hV : IsClosed (V : Set BaireSpace)) (j : ℕ) :
    Monotone (approximation U V hV j) := by
  intro a b hab y hy
  rcases hy with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, lt_of_lt_of_le h.2 hab⟩

/-- Every nonempty U has the strictly increasing, countably directed chain
of proper open subsets with supremum U described in the manuscript. -/
theorem exists_strict_chain (U : OpenLattice) (hU : U ≠ ⊥) :
    ∃ F : OmegaOne → OpenLattice,
      StrictMono F ∧ CountablyDirected (range F) ∧
      sSup (range F) = U ∧ ∀ a, F a < U := by
  classical
  obtain ⟨I, x, hVU⟩ := exists_cylinder U hU
  obtain ⟨j, hj⟩ := I.exists_notMem
  let V := cylinder I x
  have hV : IsClosed (V : Set BaireSpace) := cylinder_closed I x
  let F := approximation U V hV j
  have hw (a : OmegaOne) : Function.update x j a ∈ V :=
    update_mem_cylinder I x j hj a
  have hmiss (a : OmegaOne) : Function.update x j a ∉ F a := by
    intro hy
    rcases hy with h | h
    · exact h.2 (hw a)
    · have : a < a := by simpa only [mem_setOf_eq, Function.update_self] using h.2
      exact lt_irrefl a this
  have hmono : StrictMono F := by
    intro a b hab
    apply lt_of_le_not_ge (approximation_monotone U V hV j hab.le)
    intro hba
    apply hmiss a
    apply hba
    exact Or.inr ⟨hw a, by simpa only [mem_setOf_eq, Function.update_self] using hab⟩
  refine ⟨F, hmono, countablyDirected_range F hmono, ?_, ?_⟩
  · apply le_antisymm
    · apply sSup_le
      rintro _ ⟨a, rfl⟩
      exact approximation_le U V hV hVU j a
    · intro y hy
      obtain ⟨a, ha⟩ := exists_larger (y j)
      apply Opens.mem_sSup.mpr
      refine ⟨F a, mem_range_self a, ?_⟩
      by_cases hyV : y ∈ V
      · exact Or.inr ⟨hyV, ha⟩
      · exact Or.inl ⟨hy, hyV⟩
  · intro a
    apply lt_of_le_not_ge (approximation_le U V hV hVU j a)
    intro hUF
    exact hmiss a (hUF (hVU (hw a)))

/-- Theorem: no nonempty open set is ℵ₁-compact. -/
theorem not_alephOneCompact_of_ne_bot (U : OpenLattice) (hU : U ≠ ⊥) :
    ¬ AlephOneCompact U := by
  obtain ⟨F, _, hdir, hsup, hproper⟩ := exists_strict_chain U hU
  intro hcompact
  obtain ⟨W, ⟨a, rfl⟩, hUW⟩ := hcompact (range F) hdir (by rw [hsup])
  exact (not_le_of_gt (hproper a)) hUW

/-- The empty set is the unique ℵ₁-compact element. -/
theorem alephOneCompact_iff_eq_bot (U : OpenLattice) :
    AlephOneCompact U ↔ U = ⊥ := by
  constructor
  · intro h
    by_contra hne
    exact not_alephOneCompact_of_ne_bot U hne h
  · rintro rfl
    exact bot_alephOneCompact

/-- Every supremum of ℵ₁-compact open sets is empty. -/
theorem sSup_compact_eq_bot (D : Set OpenLattice)
    (hD : ∀ U ∈ D, AlephOneCompact U) : sSup D = ⊥ := by
  apply bot_unique
  apply sSup_le
  intro U hU
  exact le_of_eq ((alephOneCompact_iff_eq_bot U).mp (hD U hU))

/-- Corollary: the open-set lattice is not ℵ₁-algebraic. -/
theorem not_alephOneAlgebraic : ¬ AlephOneAlgebraic OpenLattice := by
  intro h
  have htop : (⊤ : OpenLattice) = ⊥ :=
    (h ⊤).trans (sSup_compact_eq_bot _ (fun _ hU => hU.1))
  let x : BaireSpace := fun _ => Classical.choice (inferInstance : Nonempty OmegaOne)
  have hx : x ∈ (⊤ : OpenLattice) := Set.mem_univ x
  rw [htop] at hx
  exact hx

#print axioms exists_strict_chain
#print axioms alephOneCompact_iff_eq_bot
#print axioms not_alephOneAlgebraic

end NonAlephOneAlgebraicity

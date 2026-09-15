import AlephOneAlgebraicity

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

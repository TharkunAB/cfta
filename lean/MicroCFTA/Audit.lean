import Lean
import MicroCFTA.Language
import MicroCFTA.Probability
import MicroCFTA.Guards
import MicroCFTA.Lattice
import MicroCFTA.Integration
import MicroCFTA.Counterexamples
import MicroCFTA.Decoder
import MicroCFTA.Holds
import MicroCFTA.Minimization
import MicroCFTA.Sized
import MicroCFTA.Productivity
import MicroCFTA.SizeMass
import MicroCFTA.Sparse
import MicroCFTA.ZeroSize
import MicroCFTA.UnionFind
import MicroCFTA.LatticeRank
import MicroCFTA.Observation
import MicroCFTA.RecursiveSize
import MicroCFTA.Cache
import MicroCFTA.LatticePolynomial
import MicroCFTA.ObservationGraph
import MicroCFTA.Fragments
import MicroCFTA.MinimumSize

/-!
# Proof dependency audit

Check every theorem in this development. Fail the build if a theorem depends
on a placeholder, a native evaluation axiom, or a project-specific axiom.
The three permitted axioms are standard Lean foundations.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (`MicroCFTA).isPrefixOf name && info.isTheorem then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on forbidden axiom {axiomName}"
      checked := checked + 1
  if checked == 0 then
    throwError "No MicroCFTA theorems were checked"
  logInfo m!"Checked axiom dependencies of {checked} MicroCFTA theorems."

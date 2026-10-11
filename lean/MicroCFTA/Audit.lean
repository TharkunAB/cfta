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
import MicroCFTA.Faulhaber
import MicroCFTA.PolynomialSum
import MicroCFTA.EqualityTrie
import MicroCFTA.LatticeLinear
import MicroCFTA.LatticeNormalize
import MicroCFTA.LatticeBound
import MicroCFTA.LatticeEliminate
import MicroCFTA.PolynomialSupport
import MicroCFTA.SizedRank
import MicroCFTA.LatticeFeasible
import MicroCFTA.TablePosition
import MicroCFTA.EqualityNormalize
import MicroCFTA.LatticePiece
import MicroCFTA.LatticePieceNormalize
import MicroCFTA.LatticePipeline
import MicroCFTA.FiniteSum
import MicroCFTA.PlanVariants
import MicroCFTA.LatticeCount
import MicroCFTA.EqualitySaturation
import MicroCFTA.LatticeSigned
import MicroCFTA.LatticeFormula
import MicroCFTA.LatticeInput
import MicroCFTA.LatticeInterval
import MicroCFTA.LatticeLevels
import MicroCFTA.LatticeDecision
import MicroCFTA.EqualityTermination
import MicroCFTA.EqualityModel
import MicroCFTA.LatticeAPI
import MicroCFTA.LatticeCumulative
import MicroCFTA.Sampler

import MicroCFTA.CoreFormula
import MicroCFTA.CoreLattice
import MicroCFTA.DistinctRank
import MicroCFTA.Shrink
import MicroCFTA.Symbolic
import MicroCFTA.Construction
import MicroCFTA.LatticeSelect
import MicroCFTA.TermRepresentation
import MicroCFTA.SearchCost
import MicroCFTA.System
import MicroCFTA.SizeTransport
import MicroCFTA.LevelEnumeration
import MicroCFTA.PublicResult
import MicroCFTA.BoundDepth
import MicroCFTA.OpenUnion
import MicroCFTA.FullSyntax
import MicroCFTA.EnumerationState
import MicroCFTA.Generic
import MicroCFTA.Template
import MicroCFTA.Binding
import MicroCFTA.PruneSchedule
import MicroCFTA.MinimizeSchedule
import MicroCFTA.GeneratorCombinators
import MicroCFTA.RecipeCompile
import MicroCFTA.SymbolicDriver
import MicroCFTA.EpsilonUnion
import MicroCFTA.MassRetention
import MicroCFTA.TermOperations
import MicroCFTA.ChildBuilder
import MicroCFTA.FormulaSemantics
import MicroCFTA.FormulaSubstitution
import MicroCFTA.FormulaBinders
import MicroCFTA.FormulaCorrectness
import MicroCFTA.FormulaLowering
import MicroCFTA.FormulaSimplify
import MicroCFTA.FormulaOrder
import MicroCFTA.SamplerReplay
import MicroCFTA.FiniteSource
import MicroCFTA.RecursiveRecord
import MicroCFTA.ObservationMass
import MicroCFTA.SymbolicNormalization
import MicroCFTA.SymbolicCounting
import MicroCFTA.SymbolicSelection
import MicroCFTA.SymbolicProgress
import MicroCFTA.GuardedSampling
import MicroCFTA.SupportTerms
import MicroCFTA.SymbolicGraph
import MicroCFTA.SymbolicBounds
import MicroCFTA.SymbolicMeaning
import MicroCFTA.RecursionProbe
import MicroCFTA.FromTerms
import MicroCFTA.OccurrenceGuard
import MicroCFTA.GraphTrim
import MicroCFTA.GraphRewrite
import MicroCFTA.RootMetadata
import MicroCFTA.RecursiveSource
import MicroCFTA.MinimumWitness
import MicroCFTA.PublicRecursion
import MicroCFTA.EnumerationCorrectness
import MicroCFTA.GraphBudget
import MicroCFTA.NumberedTerms
import MicroCFTA.StateMap
import MicroCFTA.GroupedMinimum
import MicroCFTA.BinderLanguage
import MicroCFTA.AcceptanceDispatch
import MicroCFTA.SymbolicCounter
import MicroCFTA.SymbolicIndicators
import MicroCFTA.GroupedRecord
import MicroCFTA.BinderSubstitution
import MicroCFTA.KeyedProbability
import MicroCFTA.SymbolicVerified
import MicroCFTA.ArrayUnionFind
import MicroCFTA.GroupedChoice
import MicroCFTA.SymbolicWellFounded
import MicroCFTA.SymbolicNormalizationTotal
import MicroCFTA.EnumerationDriver
import MicroCFTA.EqualityArray
import MicroCFTA.KeyedMinimumWitness
import MicroCFTA.GroupedFlags
import MicroCFTA.ArrayBounds
import MicroCFTA.SymbolicCounterTotal
import MicroCFTA.EqualityIndex
import MicroCFTA.EqualityPartition
import MicroCFTA.AcceptanceEffects
import MicroCFTA.SymbolicComplete
import MicroCFTA.AcceptanceSoundness
import MicroCFTA.EqualitySource
import MicroCFTA.EnumerationSoundness
import MicroCFTA.EnumerationProgress
import MicroCFTA.PruneCorrectness
import MicroCFTA.LatticeRetry
import MicroCFTA.SymbolicSourceUnion
import MicroCFTA.SymbolicStructuralBudget
import MicroCFTA.SymbolicInternedView
import MicroCFTA.SymbolicSmartRows
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
    if (`MicroCFTA).isPrefixOf (privateToUserName name) && info.isTheorem then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on forbidden axiom {axiomName}"
      checked := checked + 1
  if checked == 0 then
    throwError "No MicroCFTA theorems were checked"
  logInfo m!"Checked axiom dependencies of {checked} MicroCFTA theorems."

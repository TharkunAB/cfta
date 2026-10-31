import MicroCFTA.SourceCurrentChildDispatchNonterminalCache

/-! Original equality dictionaries retain the entire literal dispatch result. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentChildDispatchDictionaryTransport
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationNativeBranchCompletion (CacheValid)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeKey Symbol Constraint
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}

open scoped Classical in
private noncomputable def canonicalEdge : DecidableEq Edge := inferInstance

open scoped Classical in
private noncomputable def canonicalNode : DecidableEq Node := inferInstance

open scoped Classical in
/-- Every legal original dictionary pair retains all raw, caller, query, core and cache data. -/
theorem run_dictionaries_eq (edgeEquality : DecidableEq Edge) (nodeEquality : DecidableEq Node)
    (caller : Caller width) (before : Cached) (queries : SourceEndpointMemo.Memos)
    (scs : List Suspended) (incoming : Node) (checkEmpty : Bool) (r n p h k : Nat) :
    (letI : DecidableEq Edge := edgeEquality
     letI : DecidableEq Node := nodeEquality
     SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs incoming caller before queries) =
      (letI : DecidableEq Edge := canonicalEdge
       letI : DecidableEq Node := canonicalNode
       SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs incoming caller before queries) := by
  cases Subsingleton.elim edgeEquality canonicalEdge
  cases Subsingleton.elim nodeEquality canonicalNode
  rfl

open scoped Classical in
/-- Actual original dictionaries retain the exact no-terminal caller, queries and valid optional cache. -/
theorem nonterminal_dispatch_valid (edgeEquality : DecidableEq Edge) (nodeEquality : DecidableEq Node)
    (caller : Caller width) (before : Cached) (queries : SourceEndpointMemo.Memos)
    (scs : List Suspended) (incoming : Node) (checkEmpty : Bool) (r n p h k : Nat)
    (valid : CacheValid caller before)
    (coherent : InternedRecordCoherence.Coherent caller.checked.native.machine.heap)
    (available : InternedProbeProvenance.Available caller.checked.native.machine.heap incoming)
    (closed : incoming.free = []) (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) :
    let actual :=
      (letI : DecidableEq Edge := edgeEquality
       letI : DecidableEq Node := nodeEquality
       SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs incoming caller before queries)
    match (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 with
    | [] => actual.1.2.1 = caller ∧ actual.1.2.2.1 = queries ∧
        ∀ after, actual.2 = some after → CacheValid actual.1.2.1 after
    | _ :: _ => True := by
  dsimp only
  simp only [run_dictionaries_eq edgeEquality nodeEquality caller before queries scs incoming checkEmpty r n p h k]
  exact SourceCurrentChildDispatchNonterminalCache.nonterminal_dispatch_valid caller before queries scs incoming
    checkEmpty r n p h k valid coherent available closed bounded

end MicroCFTA.SourceCurrentChildDispatchDictionaryTransport

import MicroCFTA.SourceCurrentStoredMuLiteralRows
import MicroCFTA.SourceCurrentStoredLiteralCalls

/-!
# Original source transitions for literal stored-substitution rows

Source descent follows original union members and original Mu bodies.
It does not descend through a generated result. Closed source values keep
their literal rows unchanged. Rebuilt ordinary rows retain actual ordered
child calls under the lexical environment at that source occurrence.
Rows supplied by external replacements have a separate origin.
-/
namespace MicroCFTA.SourceCurrentStoredLiteralRowLineage
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentStoredMuLexicalInputs (shadow)
open SourceCurrentLiteralRootParts (Row)
open SourceCurrentNativeMuPublication (History)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open InternedBinderProtocol (NodeKey Reference)

/-- An indexed original transition reached through original unions and Mu bodies. -/
inductive RowAt : Value Symbol Guard → EdgeValue Symbol Guard → Prop where
  /-- An ordinary source supplies its indexed original row. -/
  | node {entry} {rows : List (EdgeValue Symbol Guard)} {level free} {index : Nat} {row}
      (found : rows[index]? = some row) :
      RowAt (.node entry rows level free) row
  /-- An indexed original union member retains its source row occurrence. -/
  | union {entry} {members : List (Value Symbol Guard)} {level free} {index : Nat} {value row}
      (found : members[index]? = some value)
      (part : RowAt value row) : RowAt (.union entry members level free) row
  /-- The original stored body retains its source row occurrence. -/
  | mu {entry body depth ordinary row} (part : RowAt body row) : RowAt (.mu entry body depth ordinary) row

/-- An external reference reached through original unions and Mu bodies. -/
inductive ReferenceAt : Value Symbol Guard → Reference → Prop where
  /-- A source reference supplies its own name. -/
  | reference (name) : ReferenceAt (.reference name) name
  /-- An indexed original union member retains its reference occurrence. -/
  | union {entry} {members : List (Value Symbol Guard)} {level free} {index : Nat} {value name}
      (found : members[index]? = some value)
      (part : ReferenceAt value name) : ReferenceAt (.union entry members level free) name
  /-- A stored binder retains only references to other source names. -/
  | mu {entry : Interned NodeKey} {body depth ordinary name} (different : name ≠ .interned entry.identity)
      (part : ReferenceAt body name) : ReferenceAt (.mu entry body depth ordinary) name

/-- Literal rows retain a source path, lexical bindings, and actual ordinary child calls. -/
inductive Origin [DecidableEq (EdgeKey Symbol Guard)] :
    Environment Symbol Guard → Value Symbol Guard → EdgeValue Symbol Guard → Prop where
  /-- The closed shortcut returns the exact literal source row. -/
  | identity {environment} {source : Value Symbol Guard} {row} (closed : source.free = []) (part : Row source row) :
      Origin environment source row
  /-- An original ordinary row supplies its fields and ordered child execution. -/
  | node {environment entry} {rows : List (EdgeValue Symbol Guard)} {level free} {index : Nat}
      {original row : EdgeValue Symbol Guard} {before after}
      (found : rows[index]? = some original)
      (symbol : row.entry.key.symbol = original.entry.key.symbol)
      (guard : row.entry.key.constraint = original.entry.key.constraint)
      (called : Calls environment original.children before row.children after) :
      Origin environment (.node entry rows level free) row
  /-- An indexed original union member supplies the same row origin. -/
  | union {environment entry} {members : List (Value Symbol Guard)} {level free} {index : Nat} {original row}
      (found : members[index]? = some original) (part : Origin environment original row) :
      Origin environment (.union entry members level free) row
  /-- The original Mu body uses the actual current ordinary local reference. -/
  | mu {environment entry body depth ordinary currentDepth row}
      (part : Origin (shadow (.interned entry.identity)
        (.reference (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel currentDepth))) environment) body row) :
      Origin environment (.mu entry body depth ordinary) row
  /-- A source reference can supply a row from its actual replacement value. -/
  | replacement {environment name replacement row} (found : environment name = some replacement)
      (part : Row replacement row) : Origin environment (.reference name) row

private theorem literal_source (source : Value Symbol Guard) (row : EdgeValue Symbol Guard)
    (part : Row source row) : RowAt source row := by
  induction part with
  | node member =>
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact .node (index := index) found
  | union member _ ih =>
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact .union (index := index) found ih

/-- Every derived row has an original transition anchor or an explicit external replacement origin. -/
theorem anchor [DecidableEq (EdgeKey Symbol Guard)] {environment : Environment Symbol Guard}
    {source : Value Symbol Guard} {row : EdgeValue Symbol Guard} (origin : Origin environment source row) :
    (∃ original, RowAt source original ∧ row.entry.key.symbol = original.entry.key.symbol ∧
      row.entry.key.constraint = original.entry.key.constraint ∧ row.children.length = original.children.length ∧
      (row = original ∨ ∃ lexical before after, Calls lexical original.children before row.children after)) ∨
    (∃ name replacement, ReferenceAt source name ∧ environment name = some replacement ∧ Row replacement row) := by
  induction origin with
  | identity _ part => exact .inl ⟨_,literal_source _ _ part,rfl,rfl,rfl,Or.inl rfl⟩
  | node found symbol guard called => exact .inl ⟨_,.node found,symbol,guard,called.length,Or.inr ⟨_,_,_,called⟩⟩
  | union found _ ih =>
      rcases ih with ⟨original,part,symbol,guard,arity,children⟩ | ⟨name,replacement,part,mapped,literal⟩
      · exact .inl ⟨original,.union found part,symbol,guard,arity,children⟩
      · exact .inr ⟨name,replacement,.union found part,mapped,literal⟩
  | @mu environment entry body depth ordinary currentDepth row _ ih =>
      rcases ih with ⟨original,part,symbol,guard,arity,children⟩ | ⟨name,replacement,part,mapped,literal⟩
      · exact .inl ⟨original,.mu part,symbol,guard,arity,children⟩
      · by_cases same : name = .interned entry.identity
        · have equal : .reference (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel currentDepth)) = replacement := by
            simpa only [shadow,same,ite_true,Option.some.injEq] using mapped
          rw [← equal] at literal
          cases literal
        · have external : environment name = some replacement := by
            simpa only [shadow,same,ite_false] using mapped
          exact .inr ⟨name,replacement,.mu same part,external,literal⟩
  | replacement found part => exact .inr ⟨_,_,.reference _,found,part⟩

/-- Replacements with no selected literal row leave an original transition anchor with full fields and child calls. -/
theorem source_row [DecidableEq (EdgeKey Symbol Guard)] {environment : Environment Symbol Guard}
    {source : Value Symbol Guard} {row : EdgeValue Symbol Guard} (origin : Origin environment source row)
    (excluded : ∀ name replacement, environment name = some replacement → ¬ Row replacement row) :
    ∃ original, RowAt source original ∧ row.entry.key.symbol = original.entry.key.symbol ∧
      row.entry.key.constraint = original.entry.key.constraint ∧ row.children.length = original.children.length ∧
      (row = original ∨ ∃ lexical before after, Calls lexical original.children before row.children after) := by
  rcases anchor origin with original | ⟨name,replacement,_part,mapped,literal⟩
  · exact original
  · exact False.elim (excluded name replacement mapped literal)

end MicroCFTA.SourceCurrentStoredLiteralRowLineage

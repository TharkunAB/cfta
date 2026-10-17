import MicroCFTA.InternedValueMass
set_option linter.all true
namespace MicroCFTA.MassEvaluation
open Cache InternedConstructorTemplates InternedBinderProtocol
private def entry : Interned NodeKey := ⟨1000000000, .node []⟩
private def probe : Value Nat Bool := .node entry [.mk ⟨1000000000, ⟨1000000000, [], true⟩⟩ []] 1000000000 [.uninterned 1000000000]
#eval InternedValueMass.value (Symbol := Nat) (Guard := Bool) (.mu entry .empty (.reference .depth) (.reference (.uninterned 1000000000)))
#eval InternedValueMass.value (.mu entry .empty probe (.reference (.uninterned 1000000000)))
end MicroCFTA.MassEvaluation

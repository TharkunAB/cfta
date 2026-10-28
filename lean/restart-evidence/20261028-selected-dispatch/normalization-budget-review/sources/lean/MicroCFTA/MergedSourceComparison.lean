import MicroCFTA.MergedColdReaderFacts

/-!
# Ordered physical source comparison

The worker preserves the source's empty, identity, and ancestor branches.
It reads the narrow rows first. Each narrow row demands the wide rows,
then tries covers in order. Matching headers compare children from left
to right. Every short circuit retains the exact cache already produced.
-/
namespace MicroCFTA.MergedSourceComparison
open InternedConstructorTemplates
open InternedBinderProtocol (Reference NodeKey NodeRef)

/-- A source failure remains distinct from a completed Boolean answer. -/
inductive Fault where
  | unresolved (name : Reference)
  | pending (key : NodeKey)
  | identity (value : NodeRef)
  | exhausted

/-- Each ordered comparison stage returns its actual physical cache. -/
inductive Result (Symbol Guard Output : Type) where
  | done (value : Output) (state : State Symbol Guard)
  | failed (fault : Fault) (state : State Symbol Guard)

/-- Both success and failure retain the last source cache. -/
def Result.state : Result Symbol Guard Output → State Symbol Guard
  | .done _ state | .failed _ state => state

/-- Source sequencing passes only a successful value to the next effect. -/
def Result.bind (result : Result Symbol Guard First)
    (next : First → State Symbol Guard → Result Symbol Guard Output) : Result Symbol Guard Output :=
  match result with
  | .done value state => next value state
  | .failed fault state => .failed fault state

/-- The numeric ancestor identity agrees with the source's `nodeIdentity` on its defined cases. -/
def identity : Value Symbol Guard → Option Nat
  | .node entry .. | .union entry .. | .mu entry .. => some entry.identity
  | .reference (.interned identity) => some identity
  | _ => none

/-- Lift the physical source reader without erasing an error or exhausted bound. -/
def read [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) : Result Symbol Guard (List (EdgeValue Symbol Guard)) :=
  match MergedSourceExposure.nodeEdges fuel value state with
  | .done edges after => .done edges after
  | .unresolved name after => .failed (.unresolved name) after
  | .pending key after => .failed (.pending key) after
  | .exhausted after => .failed .exhausted after

/-- Ordered child conjunction uses the source's `zipWith` stopping behavior. -/
def children (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) :
    List (Value Symbol Guard) → List (Value Symbol Guard) → State Symbol Guard → Result Symbol Guard Bool
  | [], _, state | _, [], state => .done true state
  | wide :: wides, narrow :: narrows, state =>
      (compare wide narrow state).bind fun accepted after =>
        if accepted then children compare wides narrows after else .done false after

/-- Try wide edges in their original order and stop at the first successful cover. -/
def anyCover [DecidableEq Symbol] (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (narrow : EdgeValue Symbol Guard) : List (EdgeValue Symbol Guard) → State Symbol Guard → Result Symbol Guard Bool
  | [], state => .done false state
  | wide :: rest, state =>
      if wide.entry.key.symbol = narrow.entry.key.symbol ∧ wide.children.length = narrow.children.length ∧ clear wide.entry.key.constraint = true then
        (children compare wide.children narrow.children state).bind fun accepted after =>
          if accepted then .done true after else anyCover clear compare narrow rest after
      else anyCover clear compare narrow rest state

/-- Each demanded narrow edge reads and searches the wide alternatives before the next narrow edge. -/
def allRows [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (wide : Value Symbol Guard) : List (EdgeValue Symbol Guard) → State Symbol Guard → Result Symbol Guard Bool
  | [], state => .done true state
  | narrow :: rest, state =>
      (read fuel wide state).bind fun wides afterRead =>
        (anyCover clear compare narrow wides afterRead).bind fun accepted after =>
          if accepted then allRows fuel clear compare wide rest after else .done false after

/-- Follow the complete source comparison branch order and actual ordered cache effects. -/
def check [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (clear : Guard → Bool) :
    Nat → List (Nat × Nat) → Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool
  | fuel, above, wide, narrow, state =>
      if narrow.referenceOf = .empty then .done true state
      else if wide.referenceOf = .empty then .done false state
      else if wide.referenceOf = narrow.referenceOf then .done true state
      else match identity wide, identity narrow with
        | none, _ => .failed (.identity wide.referenceOf) state
        | _, none => .failed (.identity narrow.referenceOf) state
        | some wideId, some narrowId =>
            if (wideId, narrowId) ∈ above then .done true state
            else match fuel with
              | 0 => .failed .exhausted state
              | fuel + 1 =>
                  (read (fuel + 1) narrow state).bind fun narrows after =>
                    allRows (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above)) wide narrows after

end MicroCFTA.MergedSourceComparison

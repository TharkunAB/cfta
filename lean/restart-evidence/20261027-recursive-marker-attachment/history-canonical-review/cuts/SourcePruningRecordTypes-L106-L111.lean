theorem recordTypes_frame (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (input : Sum (Fragment Symbol) Nat)
    (before after : State Symbol Guard) (result : Bool × Metadata Typing)
    (total : UnionFind.Total before.representatives)
    (success : Success (recordTypes graph templates fuel metadata uv input) before result after) :
    Frame before after := by

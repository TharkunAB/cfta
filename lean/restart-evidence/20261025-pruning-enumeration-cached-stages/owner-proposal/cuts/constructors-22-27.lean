inductive Value (Symbol Guard : Type) where
  | empty
  | reference (name : Reference)
  | node (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference)
  | union (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
  | mu (entry : Interned NodeKey) (body depthShape ordinaryShape : Value Symbol Guard)

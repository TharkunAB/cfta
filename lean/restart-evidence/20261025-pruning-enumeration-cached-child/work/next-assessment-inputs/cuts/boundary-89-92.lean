def recursiveBoundary : Value Symbol Guard → Bool
  | .mu .. | .union .. => true
  | _ => false


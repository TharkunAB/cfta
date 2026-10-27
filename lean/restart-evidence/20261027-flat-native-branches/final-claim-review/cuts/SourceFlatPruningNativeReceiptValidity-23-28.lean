def Indexed : FlatReceipt width → Prop
  | .complete _ caller _ after | .rejected caller _ after =>
      EnumerationFlatNativeIndex.Correct caller.checked.native.machine.heap after
  | .stopped _ observation (some after) =>
      EnumerationFlatNativeIndex.Correct observation.2.1.checked.native.machine.heap after
  | _ => True

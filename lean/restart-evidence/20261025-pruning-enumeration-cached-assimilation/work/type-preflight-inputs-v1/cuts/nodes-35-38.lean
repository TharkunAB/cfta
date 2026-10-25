theorem available_readback (heap : State Symbol Guard) (value : Value Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : Available heap value) (closed : value.free = []) :
    ∃ node, encodeNode value = some node ∧ lookupNode heap node = some value := by

/-- The conjunction worker reads the actual constructor heap and equality-operation cache. -/
def physical (state : Checked width) : Physical := ⟨state.native.machine.heap, state.operations⟩

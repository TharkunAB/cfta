[2026-11-14 16:58 CET]

PROPOSED access patch. This patch is not needed to check the body-child module.
Root may check and apply it when it composes the simultaneous induction.
No private declaration is imported or assumed to have a public name.

Each hunk adds a thin public auxiliary theorem inside the owning namespace.
Its header is the existing private helper header with only its name changed.
Its proof calls that existing private helper with the same arguments.
Every existing declaration header and proof byte remains unchanged.
No existing full proof is copied into a new proof.
The explicit induction hypothesis stays on an auxiliary induction step.
It is not a premise on the original closed theorem.

SourceSynthesisCurrentUniverseAtomInductionSteps:
  existing PRIVATE: ordered_union_atoms_of_fuel_induction
  proposed public: ordered_union_atoms_induction_step
  exact current input SHA: 0de3c07a341ec24d0cc4efef765ac2bd228b3fd2c5c5db5b898d1d7684ceab7e

SourceSynthesisCurrentUniverseNodeAtomInductionSteps:
  existing PRIVATE: ordered_node_atoms_of_fuel_induction
  proposed public: ordered_node_atoms_induction_step
  exact current input SHA: 6186b3974cbf7db3039d404ea8c48db3c3ba2e36854fc837ce4b11666e01598a

# Constructor probe construction

`ConstructorProbeWitnesses` models the witness stage of
`Gen/Internal/Automaton.hs:undecodableConstructor`. The source chooses one
complete term per productive state before it builds root contexts.

The finite row inventory uses `Fin count`. Each row contains constructor
labels and ordered child states. Finite source state names can be indexed
in ascending table order. The model does not prove the `Map` implementation
or this reindexing operation. States without a stored row have an empty row.
As in the source probe function, annotations do not restrict structural
admission. This corresponds to the datatype grammar caller, not a guarded
automaton whose annotations must be checked during acceptance.

`arguments` traverses all child lookups in order. `firstWitness` retains the
first transition with all child witnesses available. `addWitness` preserves
an existing state witness. `passRows` uses the source right-fold order. A
later update in the same pass can therefore use a newly inserted witness.
This is the actual sequential pass, not simultaneous Boolean iteration.

`converge` uses the source stop test: the occupied map size does not change.
Its termination measure is the number of states without a witness. Each
recursive call decreases that number. `equal_size` derives equality of the
complete witness maps from map growth and equal sizes. Thus the stop test
produces an actual fixed point, not only equal cardinality.

`witnesses_sound` proves that every stored term is structurally admitted at
its state. `witnesses_exact` proves that the final map has a witness exactly
for states with a finite admitted term. This includes cyclic finite graphs.
The proof derives completeness from the fixed-point transition update and
induction on accepting runs. It does not assume a supplied witness list or
whole-program productivity law.

## Actual context worklist

`ConstructorProbeWorklist` models the source FIFO traversal. `latest` retains
the last candidate for each key in a single expansion, as `Map.fromList`
does. `fresh` removes all keys already present and returns the new keys in
ascending inventory order. `advance` retains earlier contexts. `reach`
appends the fresh keys to the end of the pending queue.

The termination measure first counts missing states, then queue length.
An expansion with a new state decreases the first component. An expansion
without a new state preserves the complete map and decreases queue length.
The proof does not assume an acyclic graph or a supplied traversal bound.

`reach_closed` derives closure of the final map under the actual expansion
entries. `reach_property` transports a local context property through each
selected candidate. `reach_runs` proves that a valid pending queue follows
the exact source branches. In particular, each `Map.!` read has a stored
context. The total model's missing-context fallback is unreachable from the
source initial queue.

## Root probes and coverage

`ConstructorProbeContexts` represents each generated source closure as a
finite stack of constructor frames. `plug` uses the exact indexed list
replacement. `steps` reads the computed witnesses, visits transitions in row
order, and visits child positions in their original order.

`steps_preserve` derives local context correctness from admitted witness
forests and an indexed child replacement. It supplies the local property
used by the worklist theorem. `contexts_sound` proves that every recorded
context takes admitted hole terms to admitted initial-state terms.
`contexts_exact` proves that the context map contains exactly the states on
productive root paths. The initial state itself is included even when its
language is empty, as in the source.

`probes` visits stored contexts in map order and all usable transitions in
row order. It uses the exact selected child witness tuple. `probes_sound`
proves that every emitted probe is admitted at the initial state.
`probes_cover` proves coverage of every productive transition on a root path.
`Uses` records a transition used at actual indexed positions in an accepting
term. `used_transition_probe` derives a generated probe for every such
occurrence. It does not assume a supplied whole-probe coverage law.

`contexts_keep_hole` proves that actual context construction retains the
supplied term. `probes_contain_label` then proves that the probed constructor
label occurs somewhere in the final root term.

## Codec detection and its limit

`firstRejected` models the source first rejected probe. `undecodable_witness`
proves that a reported constructor occurs in a structurally admitted root
term that the codec rejects. The report does not prove that this constructor
caused rejection. A different constructor in the same context can be the
cause. This is the source function's documented diagnostic meaning.

`LocallyRejected` is an explicit codec condition. It states that a particular
transition's constructor term is rejected in every admitted root context
and for every admitted child tuple. `undecodable_detects` proves that the
source check reports a failure when an actual root term uses such a
transition. The returned label can name an earlier rejected probe.

The adapter does not prove `LocallyRejected` for an arbitrary user codec.
Passing the generated finite probes only establishes decoding for those
probe terms. `checkCodec_generated` retains this exact boundary, and
`Generic.finite_probes_do_not_prove_codec_totality` remains the explicit
counterexample to arbitrary codec totality. Hash-bucket lookup, datatype
constructor restoration, and particular codec rejection propagation belong
to their separate adapters.

`example_probes` checks the executable functions by kernel evaluation. Its
graph has a productive cycle, two occurrences of the same child state, and
an unproductive cycle. The witness is the first available leaf. The duplicate
child keeps the last-position context. The unproductive cycle has no witness.
The resulting three probes retain the source ordering and duplicate terms.

Validation on 2026-10-12: `lake build MicroCFTA.ConstructorProbeContexts`
passes with 12 jobs. All 59 theorem axiom checks across the three modules
use only `propext` and `Quot.sound`. No source changes or Cabal runs were
added.

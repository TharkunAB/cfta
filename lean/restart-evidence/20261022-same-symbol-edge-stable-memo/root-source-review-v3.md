# First strict repair: root source review

Root read the complete 329-line source and the entire 162-line repair patch.
Selected SHA: 35a92ce3bd517baeeccf0df68acf5ed1c7f87eb98e351f59b649cf5fa6777e7b.
The repair adds one private cell-table overwrite equality. Its proof splits on the actual handle equality.
The miss inversion now uses lookup_miss and two actual yielded transitions through tail_done.
The finish helpers read the exact evaluating cells before they compare the resulting maps.
Literal lookup facts align the key shape. Case branches use the equalities produced by case analysis.
written_fields uses the same overwrite equality to prove the final cell interpretation.
The three deprecated canonical-key simp arguments are removed. No linter is disabled.
The context, documented Stable and public theorem header remain byte-identical.
The main semantic transport and canonical-key proof retain the same premises and actual after state.
The additional 17 lines address the concrete strict1 failures. The 329-line source stays below 350.
The 328-line preflight and its one-line type annotation correction remain separate retained drafts.
The candidate is uncompiled. Independent repair review is still required before strict2 activation.

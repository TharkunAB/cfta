# Indexed scan output block

Status: UNCOMPILED. No logical proof credit is claimed.

The public header was frozen before the proof. The theorem retains every field and conjunct from the existing indexed output origin. It adds a later output list and the equality of the full output list with earlier outputs, the complete producing-row output block, and later outputs.

The proof calls existing `scan_output_origin` and `scan_append`. A stopped producing row has no later outputs. A completed producing row retains all outputs from the actual sibling scan at that row's returned caller and query endpoint. This covers a stopped sibling suffix as well as a complete suffix. It does not remove duplicates or replace list occurrence by membership. Every row receives the same captured cache `before`.

The module imports only the existing origin and append modules. It does not import the large resource owner. The generic Output and Reason universes match the existing scan API. The algorithm, supplied budgets and result constructors are unchanged. No future output, resource, invariant or model premise is added.

The scope is a finite actual scan and its output block. This does not establish callback ancestry for a whole eager execution or a joint assignment for historical obligations.

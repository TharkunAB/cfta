# Stack-indexed token masks

Pre³ moves LR(1) parser work into transitions that match the input and a
prefix of the parser stack.
It can combine consecutive transitions and share a test across tokens.
This experiment applies those ideas to two serializations of one bounded
tree language. The three routes walk a vocabulary trie byte by byte, scan
composed token effects, or index those effects by their required stack
prefix. [Pre³ §3](https://aclanthology.org/2025.acl-long.551/)

The grammar has atoms `a`, `b`, and parenthesized expressions. A binary
operator takes an expression on the left and an atom on the right. Infix
operators share a precedence and associate to the left. Each atom leaf,
operator, and pair of parentheses costs one AST node. Prefix notation puts
the operator before both children and retains the parentheses.

## Budget and exactness

A composed effect replaces one required stack prefix with another. The
remaining stack needs one node for each pending atom or expression.
Delimiters and optional operators need zero more nodes. The mask checks
the token cost plus the change in this minimum against the current slack.
For the six byte rules, the cost already spent plus the required minimum
never decreases. The final budget check therefore covers every
intermediate byte. EOS has its own condition and requires a complete
expression.

At size 7 an independent AST enumerator finds 1,286 terms per notation.
All three routes agree with its full masks for 3,271 infix and 3,885 prefix
queries, including invalid prefixes and EOS. All three routes also agree
on the 246 timing prefixes. The exhaustive masks agree with the earlier
CFTA text-mask spike, XGrammar 0.2.8, and the public Pre³ driver.
[LightLLM at fa852748](https://github.com/ModelTC/LightLLM/tree/fa852748dcc9b9ca10710509a0b80220c0b9deb8/format_out/grammer)

The budget matters even when a parser can finish the syntax. At size 7
after `(((`, the token `((((` would leave seven opening groups and a pending
atom. It takes at least eight AST nodes to finish. A recursive grammar
alone permits that token. In an earlier run of the public Pre³ driver at
infix size 23, grammar compilation took 12.055 CPU seconds for a
size-indexed grammar and 2.00 CPU ms when the driver compiled the recursive
grammar and checked the node budget separately. The two routes returned
the same masks on the timing fixture.

## CPU cost

CPython 3.12.3 on a Ryzen 9 7950X under WSL2. The fixture retains the 102
vocabulary IDs whose spellings use only the grammar's six bytes, plus EOS.
Each warm batch returns sorted token IDs for 17, 41, or 65 prepared
prefixes. Values are median process CPU microseconds per query over three
processes, each with 2,000 warm batches.

| Notation | Bound | Byte trie | Effect scan | Stack index |
| --- | ---: | ---: | ---: | ---: |
| Infix | 7 | 8.29 | 1.54 | 0.73 |
| Infix | 15 | 8.19 | 1.44 | 0.73 |
| Infix | 23 | 8.55 | 1.50 | 0.79 |
| Prefix | 7 | 13.40 | 14.77 | 0.86 |
| Prefix | 15 | 18.08 | 15.86 | 1.12 |
| Prefix | 23 | 20.85 | 16.44 | 1.34 |

At bound 15, building the indexes took 0.59 ms for the infix byte trie
and 0.24 ms for the infix stack index. The prefix figures were 0.54 and
2.08 ms. Infix has 28 effect groups and prefix has 351. The stack index
visits only the groups for prefixes of the current stack. All routes
peaked around 20–21 MiB of process RSS, which includes Python and the
fixture. For 300 batches at bound 15, Cachegrind counted 2,145M, 642M,
and 404M instructions for the infix routes in table order. Prefix used
4,435M, 4,775M, and 513M instructions. These include process startup,
preparation, and the mask queries.

The earlier CFTA text-mask spike had warm masks of 1.08 µs per query for
infix and 3.27 µs for prefix at bound 15. Its first batch took 6.325 CPU
seconds for infix and 20.75 CPU ms for prefix. Those runs used GHC and
CFTA's text cursor. The Python comparison isolates syntax mask construction
and querying. It gives a possible use for a low-cost syntax prefilter when
CFTA must plan a new infix walk.

## Scope for CFTA

The serialized grammar must cover the syntax of every CFTA completion
within the relevant bound. Its mask can then reject an impossible
continuation before CFTA checks the remaining ones. For example, the
structural grammar offers both `a` and `b` after `a+`. An equal-child
constraint in CFTA permits only `a` at that point. CFTA supplies that
constraint check, the counts and weights of the accepted terms, and
their ranks. The experiment covers this structural grammar and these
token spellings.

## Prefilter in front of the CFTA cursor

The follow-up uses the text and vocabulary masks from the local
`spike/pre3-text-mask` checkout at `4fd22c59e4`. Its language requires both
children of `+` to be equal. The syntax index ignores that equality. The
filtered route asks the CFTA text cursor about each token that the index
offers. The cursor still rejects invalid tokens. For example, after `a+`
the syntax index offers both `a` and `b`, and CFTA offers only `a`.

At size 7 the full vocabulary trie and the filtered route returned exactly
the same offered IDs on 3,271 infix and 3,885 prefix queries. A separate
size-15 prefix batch of 41 queries returned the same rows in three routes.
In two matched runs starting fresh processes, the trie took 20.27 and
20.74 s wall time. Scanning every token directly with CFTA took 16.34 and
17.18 s. Building and running the Python index, passing the candidate
file, and checking it with CFTA took 12.84 and 13.70 s.

| Notation and bound | CFTA trie (µs) | CFTA after filtering (µs) | Syntax index (µs) | Sum (µs) |
| --- | ---: | ---: | ---: | ---: |
| Infix 7 | 0.69 | 0.17 | 0.75 | 0.92 |
| Prefix 7 | 1.15 | 0.27 | 0.89 | 1.16 |
| Prefix 15 | 1.52 | 0.42 | 1.13 | 1.56 |

These are median warm process CPU microseconds per query from three
processes and 2,000 batches each. The sum excludes transfer overhead and
estimates the compute cost of filtering on every query. The benefit on
this fixture is in the first batch of the larger prefix workload. The
size-15 infix trie run was stopped after 91 s near its 3 GiB heap limit.
The fixture measures offered token IDs, including EOS, for this grammar.

Run the cursor test from a Nix shell for the local text-mask checkout.
Use the pinned tokenizer JSON described below. Add `bench` to repeat the
warm measurements.

```sh
spike=/path/to/prefilter/cfta-generator/spikes/pre3
bash "$spike/cursor-prefilter.sh" "$PWD" /path/to/tokenizer.json /tmp/cfta-cursor-results
```

The text-mask checkout supplies `Data.CFTA.Mask.Text` and
`Data.CFTA.Mask.Vocabulary`. The Python comparison below only requires
the stack-index spike checkout.

## Run the checks

Download the pinned Qwen tokenizer JSON. Its SHA-256 is
`c0382117ea329cdf097041132f6d735924b697924d6f6fc3945713e96ce87539`.
[Tokenizer revision 8123ea2e](https://huggingface.co/Qwen/Qwen2.5-Coder-0.5B/blob/8123ea2e9354afb7ffcc6c8641d1b2f5ecf18301/tokenizer.json)

The scripts use the Python 3.12 standard library. Run from the workspace
root using the repository's memory cap for tests and measurements.

```sh
spike=cfta-generator/spikes/pre3
data=$(mktemp -d)
uv run --no-project --python 3.12 python "$spike/fixture.py" tokenizer.json "$data"
for notation in infix prefix; do
    uv run --no-project --python 3.12 python "$spike/mask.py" "$notation" 7 \
        "$data/vocab.tsv" "$data/$notation-exhaustive.txt" verify
    for route in bytewise composed indexed; do
        uv run --no-project --python 3.12 python "$spike/mask.py" "$notation" 15 \
            "$data/vocab.tsv" "$data/$notation-15.txt" "$route" --repeats 2000
    done
done
```

# 5. A template exclusion keeps its own table of refined nodes

## Context

`exclude` refines a node against template parts, and it goes down into the
children as deep as the templates reach. Specftacular's `compileTemplates`
applies an exclusion at each node of a program graph. So a child that many
edges reach was refined again for each edge, with the same parts each time.
At HugeLists 6-p4 with `--type-depth 2`, compiling the templates into the
parts of the search space took 37 % of phase 4, against 5 % for the
enumeration of the programs.

## Decision

`refine` keeps one table for each application of its first two arguments.
The key is the node and the two lists of parts, which hash by their catalog
identifier. `exclude` applies `refine` once for all the nodes, so the table
lives as long as the exclusion, and no longer.

## Why

- The walk is a pure function of the node and the parts, so the table
  cannot change a result.
- On the head of #67, HugeLists 6-p4 with `--type-depth 2` allocates 18.6 %
  less and runs 17 % faster (MUT), with byte-identical output. The eight
  benchmark cells keep their checksums and instruction counts.
- The global intern and memo tables never evict
  (`Data.CFTA.Interned.Memo`). A table for each exclusion is garbage when
  the exclusion is.

## Discussion points

- One table for each template list, shared by the parts of a bucket:
  measured, no gain (allocation −0.01 %). The parts share few nodes.
- A global table would keep the result of every exclusion for the life of
  the process.

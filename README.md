# causallib

Formalizing causal inference structures in Lean 4.

## Structure

`CausalLib/DirectedGraph.lean` defines general finite directed graphs and their
bounded reachability queries and proofs. Self-loops are forbidden, but longer
directed cycles are allowed. This module depends only on Mathlib.

`CausalLib/DAG.lean` imports that foundation. `CausalLib.DAG` extends
`DirectedGraph`, inheriting `adj` and `no_self_loop` and adding an acyclicity
proof. `G.toDirectedGraph` exposes a DAG's underlying directed graph.

`CausalLib/ADMG.lean` defines finite acyclic directed mixed graphs. `ADMG`
extends `DAG`, exposing its directed part through `G.toDAG`, and adds symmetric,
loop-free Boolean `bidirected` adjacency. Bows are allowed: a pair may carry
both a directed and a bidirected edge. Only directed cycles are prohibited.

Import the library with:

```lean
import CausalLib
```

## Constructing a DAG

```lean
open CausalLib

def chain : DAG (Fin 3) where
  adj a b := decide ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2))
  no_self_loop := by decide
  acyclic := by decide
```

The existing queries remain available in `CausalLib.DAG`:

- `hasEdge`, `inNeighbors`, `outNeighbors`, `neighbors`, `inDegree`, `outDegree`
- `parents`, `children`, `roots`, `leaves` (also `sources`, `sinks`)
- `reachableN`, `reachable`, `canReach`, `ancestors`, `descendants`
- `isAncestor`, `isDescendant`

Reachability follows one or more directed edges. `canReach_self` expresses
acyclicity using the public reachability query.

The neighborhood, degree, source/sink, and reachability queries are implemented
in `CausalLib.DirectedGraph`; the corresponding DAG queries and general
reachability lemmas forward to that implementation. DAG constructors retain
the flat syntax shown above.

## Simple-path d-separation

- `IsPath` requires an adjacency chain in either direction and `List.Nodup`.
- `isCollider`, `segmentBlocked`, and `pathBlocked` implement blocking at
  interior vertices. A collider opens when it or a descendant is conditioned on.
- `dSep`, `dConnected`, and `dSepSet` quantify over simple paths.
- Endpoints do not block paths. The singleton path makes every vertex
  d-connected to itself, including when it is in the conditioning set.
- Symmetry, decomposition, weak union, contraction, and intersection are proved
  directly over simple paths in `dSep_full_graphoid`. Weak union uses
  `active_path_lemma`, which splices a simple prefix with a directed descendant
  path while handling overlaps. `contraction_path` and `intersection_path`
  construct shorter simple prefixes.
- All proofs are complete, with no `sorry` dependencies.

## ADMG marked simple paths

```lean
open CausalLib

def mixed : ADMG (Fin 3) where
  adj a b := decide ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2))
  no_self_loop := by decide
  acyclic := by decide
  bidirected a b := decide ((a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1))
  bid_no_loop := by decide
  bid_symm := by decide

example : mixed.IsPath [0, 1, 2] [.dirFwd, .bidir] := by decide
example : mixed.pathBlocked ∅ [0, 1, 2] [.dirFwd, .bidir] = true := by decide
example : mixed.pathBlocked ∅ [0, 1, 2] [.dirFwd, .dirFwd] = false := by decide
```

`ADMG.Mark` records the chosen edge at each step: `dirFwd`, `dirBack`, or
`bidir`, relative to traversal. `Mark.valid`, `Mark.flip`, `Mark.intoLeft`, and
`Mark.intoRight` validate edges and expose their orientation. `reverseMarks`
reverses the list and flips each mark.

`IsPath G vertices marks` combines aligned edge validation (`ValidSteps`)
with `vertices.Nodup`. Empty and singleton paths have no marks; mismatched
lists and repeated vertices are rejected. Both `dSep` and `dConnected`
quantify over vertices **and** marks, so the two paths in the bow example
above have different collider status. This mixed-graph separation is also
called m-separation; the API retains the requested `dSep` naming.

`directed`/`hasEdge`, `hasBidirectedEdge`, `adjacent`, `parents`, `children`,
`spouses`, `ancestors`, and `descendants` provide graph queries. Ancestors,
descendants, and collider activation follow directed edges only. As in DAGs,
endpoints never block a path, and singleton paths connect a vertex to itself.

`ADMG.dSepSet_symm`, `dSepSet_decomp`, `dSepSet_weak_union`,
`dSepSet_contraction`, and `dSepSet_intersection` prove all five graphoid
axioms without disjointness assumptions. They are collected in
`dSep_semigraphoid` and `dSep_full_graphoid`. The proofs operate directly on
marked simple paths: reverse/flip for symmetry, shorten prefixes for
contraction and intersection, and splice a directed descendant path for weak
union. Overlaps are resolved by shortening the continuation while preserving
simplicity and marks.

`DAG.toADMG` embeds a DAG with no bidirected edges. The theorems
`DAG.toADMG_dSep_iff`, `DAG.toADMG_dSepSet_iff`, and
`DAG.toADMG_dConnected_iff` establish agreement with the original DAG API.

## Build

With Lean installed, run:

```bash
lake build
lake env lean CausalLibTest/DAG.lean
lake env lean CausalLibTest/ADMG.lean
```

The Lean version and Mathlib dependency are pinned by `lean-toolchain` and
`lake-manifest.json`.

The regression checks cover cycle detection, DAG construction and queries,
overlapping reroutes, and simple-prefix shortening. They also audit the graphoid
proofs to require direct simple-path helpers and approved separation declarations. The ADMG
suite additionally covers chains, forks, mixed and bidirected colliders,
directed-descendant activation, bows, reversal, malformed paths, repeated
vertices, empty endpoint sets, and the DAG embedding. Its dependency audit
requires the direct simple-path helpers and rejects project axioms, unfinished
proofs, and reuse of DAG separation theorems.

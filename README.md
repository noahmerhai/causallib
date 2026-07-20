# causallib

Formalizing causal inference structures in Lean 4.

## Overview

Three graph structures, building from general to specific:

| File | Structure | Key property |
|---|---|---|
| `CausalLib/DirectedGraph.lean` | `DirectedGraph` | Asymmetric neighborhoods, cycles allowed |
| `CausalLib/DAG.lean` | `DAG` | Directed acyclic graph; d-separation is a graphoid (fully proved) |
| `CausalLib/ADMG.lean` | `ADMG` | General acyclic directed mixed graph (bows allowed); mark-annotated walks, separation, graphoid axioms at the walk level |
| `CausalLib/WalkToPath.lean` | — | Walk-to-path excision; all five graphoid axioms on the textbook path-based `dSep` |

## Structure

```
causallib/
├── lakefile.toml
├── CausalLib.lean
├── CausalLib/
│   ├── DirectedGraph.lean   -- General directed graph
│   ├── DAG.lean             -- DAG + d-separation + graphoid axioms
│   ├── ADMG.lean            -- ADMG + d-separation + graphoid axioms + DAG embedding
│   └── WalkToPath.lean      -- walk→path excision; graphoid axioms on path-based dSep
├── weak_union_dsep.tex      -- Paper proof of Weak Union via the Active Path Lemma
└── README.md
```

## Setup

```bash
lake update
lake build
```

Requires Lean 4 and Mathlib4. Install via:
```bash
curl https://elan.lean-lang.org/elan-init.sh | bash
lake update && lake build
```

## Definitions

### DirectedGraph
- `hasEdge`, `outNeighbors`, `inNeighbors`, `sources`, `sinks`
- `reachable` (depth-bounded, computable)
- `hasCycle`, `isAcyclic`
- `addEdge`, `removeEdge`, `transpose`

### DAG
- Lifts `DirectedGraph` queries: `parents`, `children`, `roots`, `leaves`
- `ancestors`, `descendants`
- `IsWalk` — undirected walks as adjacency chains
- `isCollider`, `segmentBlocked`, `pathBlocked`
- `dSep` / `dSepSet` — d-separation as a `Prop`, quantified over walks
- `active_path_lemma` — Verma & Pearl's Active Path Lemma (transcribes `weak_union_dsep.tex`)
- **Graphoid axioms, all proved with no sorries**: `dSep_semigraphoid`
  (Symmetry, Decomposition, Weak Union, Contraction) plus `dSepSet_intersection`

### ADMG
A **general** ADMG: directed and bidirected edges, directed part acyclic, with
**no bow-freeness assumption** — a pair of vertices may carry both a directed
and a bidirected edge (a "bow").

- `Mark` (`dirFwd` / `dirBack` / `bidir`) — every walk step records which
  *specific* edge it traverses. This is what makes collider detection
  unambiguous even across a bow, without needing to forbid bows outright:
  a bare vertex-adjacency check can't tell two parallel edges apart, but a
  walk that names its marks can. `Mark.valid` checks a mark against the
  graph; `isCollider m1 m2` and `segmentBlocked` are defined purely from
  marks.
- `IsWalk` / `IsPath` — a walk is a `(vertices, marks)` pair in lock-step;
  a path additionally requires `vertices.Nodup` (no repeated vertex — the
  literal, textbook meaning of "path").
- `dSep` / `dSepSet` — **d-separation quantified over genuine simple paths**,
  matching the textbook definition exactly.
- `dSepWalk` / `dSepSetWalk` — an auxiliary, **walk**-quantified relation
  (repeats allowed; the same style DAG.lean itself uses). Weak Union,
  Contraction and Intersection are proved here first, via `chainBuild`,
  `active_path_lemma`, `contraction_walk`, `intersection_walk` — none of it
  needing bow-freeness (see `Mark` above).
- `DAG.toADMG` — embeds any DAG as a bidirected-edge-free ADMG
- `DAG.toADMG_dSepWalk_iff` — `dSepWalk` on the embedding is exactly
  DAG.lean's own (walk-quantified) `dSep`

### WalkToPath
Closes the walk-to-path gap, landing **all five graphoid axioms on the
textbook path-based `dSep`** — no sorry, no new axioms.

- `DirectedGraph.reachableN_subset_card` — the depth bound `Fintype.card V`
  in `reachable` is *saturating* (pigeonhole on the nondecreasing frontier),
  which yields `ADMG.descendants_trans`, transitivity of `descendants`
- `excise_preserves_active` — a walk repeating a vertex can be cut down to a
  strictly shorter **active** walk with the same endpoints
- `seam_unblocked` — the crux. Excising the loop `v :: B ++ [v]` merges the
  two triples at `v` into one new "seam" triple. If the seam is a collider
  that neither original triple already opens, the loop must leave `v`
  forward and re-enter `v` forward, forcing a collider strictly inside the
  loop; that collider is a descendant of `v` and is open, so `v ∈ An(Z)` and
  the seam is open too. This is exactly where the *graph-level* descendant
  test in `segmentBlocked` (rather than a walk-reaching one) is load-bearing.
- `active_walk_contains_active_path` — minimal-witness argument: a
  minimum-length active walk cannot repeat a vertex
- `dSep_iff_dSepWalk` / `dSepSet_iff_dSepSetWalk` — the equivalence
- `dSepSet_weak_union_path`, `dSepSet_contraction_path`,
  `dSepSet_intersection_path`, and the capstone `dSep_full_graphoid`

## Roadmap

- [x] Prove `dSep_symm`
- [x] Prove the graphoid axioms for d-separation (DAG)
- [x] Generalize ADMG to allow bows (no bow-freeness assumption), via
      mark-annotated walks
- [x] Define ADMG separation over genuine simple paths; prove Symmetry and
      Decomposition directly for it
- [x] Prove Weak Union, Contraction, Intersection for the walk-quantified
      `dSepWalk`; embed DAGs and prove the walk-level relations agree
- [x] Prove the walk-to-simple-path shortcutting theorem and lift all five
      graphoid axioms from `dSepWalk` onto the textbook `dSep`
- [ ] Connect to `Mathlib.Combinatorics.SimpleGraph`
- [ ] Define probability measures and prove the backdoor adjustment theorem

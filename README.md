# causallib

Formalizing causal inference structures in Lean 4.

## Overview

Three graph structures, building from general to specific:

| File | Structure | Key property |
|---|---|---|
| `CausalLib/DirectedGraph.lean` | `DirectedGraph` | Asymmetric neighborhoods, cycles allowed |
| `CausalLib/DAG.lean` | `DAG` | Directed acyclic graph; d-separation is a graphoid (fully proved) |
| `CausalLib/ADMG.lean` | `ADMG` | General acyclic directed mixed graph (bows allowed); separation graphoid axioms fully proved at the walk level |

## Structure

```
causallib/
├── lakefile.toml
├── CausalLib.lean
├── CausalLib/
│   ├── DirectedGraph.lean   -- General directed graph
│   ├── DAG.lean             -- DAG + d-separation + graphoid axioms
│   └── ADMG.lean            -- ADMG + d-separation + graphoid axioms + DAG embedding
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
  matching the textbook definition exactly. **Symmetry and Decomposition are
  proved directly for this relation**, with no sorry.
- `dSepWalk` / `dSepSetWalk` — an auxiliary, **walk**-quantified relation
  (repeats allowed; the same style DAG.lean itself uses). **Weak Union,
  Contraction and Intersection are proved for this relation**, via
  `chainBuild`, `active_path_lemma`, `contraction_walk`, `intersection_walk`
  — all with no sorry, and none of it needs bow-freeness (see `Mark` above).
  `dSep_of_dSepWalk` transfers walk-level separation down to path-level
  separation for free.
  **Why the deep axioms stop at `dSepWalk`, not `dSep`:** upgrading them to
  the simple-path relation needs a genuine "every active walk contains an
  active simple path" shortcutting theorem. It's true and provable in
  principle, but the gluing construction inside the Active Path Lemma can
  revisit an earlier path vertex when a bidirected edge lets a directed
  chain double back to it, and repairing that needs a forbidden-set-avoiding
  reachability search — real additional work, not included here. This gap
  is documented in code on `dSepWalk`.
- `DAG.toADMG` — embeds any DAG as a bidirected-edge-free ADMG
- `DAG.toADMG_dSepWalk_iff` — `dSepWalk` on the embedding is exactly
  DAG.lean's own (walk-quantified) `dSep`

## Roadmap

- [x] Prove `dSep_symm`
- [x] Prove the graphoid axioms for d-separation (DAG)
- [x] Generalize ADMG to allow bows (no bow-freeness assumption), via
      mark-annotated walks
- [x] Define ADMG separation over genuine simple paths; prove Symmetry and
      Decomposition directly for it
- [x] Prove Weak Union, Contraction, Intersection for the walk-quantified
      `dSepWalk`; embed DAGs and prove the walk-level relations agree
- [ ] Prove the walk-to-simple-path shortcutting theorem needed to lift
      Weak Union / Contraction / Intersection from `dSepWalk` to `dSep`
- [ ] Connect to `Mathlib.Combinatorics.SimpleGraph`
- [ ] Define probability measures and prove the backdoor adjustment theorem

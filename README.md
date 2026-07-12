# causallib

Formalizing causal inference structures in Lean 4.

## Overview

Four graph structures, building from general to specific:

| File | Structure | Key property |
|---|---|---|
| `CausalLib/DirectedGraph.lean` | `DirectedGraph` | Asymmetric neighborhoods, cycles allowed |
| `CausalLib/DAG.lean` | `DAG` | Directed acyclic graph; d-separation is a graphoid (fully proved) |
| `CausalLib/ADMG.lean` | `ADMG` | Acyclic directed mixed graph (bow-free); m-separation is a graphoid (fully proved) |
| `CausalLib/MAG.lean` | `MAG` | Mixed acyclic graph; m-separation (in progress) |

## Structure

```
causallib/
├── lakefile.toml
├── CausalLib.lean
├── CausalLib/
│   ├── DirectedGraph.lean   -- General directed graph
│   ├── DAG.lean             -- DAG + d-separation + graphoid axioms
│   ├── ADMG.lean            -- ADMG + m-separation + graphoid axioms + DAG embedding
│   └── MAG.lean             -- MAG + m-separation (has one remaining sorry)
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
- Directed + bidirected edges; directed part acyclic; **bow-free**
  (no pair carries both a directed and a bidirected edge — required for
  walk-based m-separation to be sound; with a bow, Weak Union fails)
- `parents`, `children`, `spouses`, `ancestors`, `descendants`
- Mixed-graph `isCollider` (arrowheads on both sides), `segmentBlocked` with the
  standard collider-opening rule (collider ∈ An(Z), via descendants)
- `mSep` / `mSepSet` — m-separation as a `Prop`, quantified over walks
- **Graphoid axioms, all proved with no sorries**: `mSep_semigraphoid`
  plus `mSepSet_intersection`
- `DAG.toADMG` — embeds any DAG as an ADMG with no bidirected edges
- `DAG.toADMG_mSep_iff` — m-separation on the embedding is exactly d-separation
  (the ADMG development conservatively extends DAG.lean)

### MAG
- `parents`, `children`, `spouses` (bidirected neighbors)
- `ancestors`, `descendants` (directed edges only)
- Extended `isCollider` covering directed + bidirected edge combinations
- `mSep` / `dSep` — m-separation as a `Prop`
- `mSep_symm` (modulo one `sorry` in `pathBlocked_reverse`)

## Roadmap

- [x] Prove `dSep_symm`
- [x] Prove the graphoid axioms for d-separation (DAG)
- [x] Prove the graphoid axioms for m-separation (bow-free ADMG)
- [x] Embed DAGs into ADMGs and prove the separation relations agree
- [ ] Repair MAG.lean: walk-quantified `mSep`, descendant-based collider opening,
      remove the `pathBlocked_reverse` sorry (all available to port from ADMG.lean)
- [ ] Add ancestrality/maximality to MAG and relate it to ADMG
- [ ] Connect to `Mathlib.Combinatorics.SimpleGraph`
- [ ] Define probability measures and prove the backdoor adjustment theorem

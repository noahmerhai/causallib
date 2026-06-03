# causallib

Formalizing causal inference structures in Lean 4.

## Overview

Three foundational graph structures, building from general to specific:

| File | Structure | Key property |
|---|---|---|
| `CausalLib/DirectedGraph.lean` | `DirectedGraph` | Asymmetric neighborhoods, cycles allowed |
| `CausalLib/DAG.lean` | `DAG` | Directed acyclic graph, d-separation |
| `CausalLib/MAG.lean` | `MAG` | Mixed acyclic graph (directed + bidirected edges), m-separation |

## Structure

```
causallib/
├── lakefile.toml
├── CausalLib/
│   ├── DirectedGraph.lean   -- §1: General directed graph
│   ├── DAG.lean             -- §2: DAG + d-separation + backdoor criterion
│   └── MAG.lean             -- §3: MAG + m-separation + DAG→MAG embedding
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
lake new causallib
# copy files, then:
lake update && lake build
```

## Definitions

### DirectedGraph
- `hasEdge`, `outNeighbors`, `inNeighbors`
- `reachable` (depth-bounded, computable)
- `hasCycle`, `isAcyclic`
- `addEdge`, `removeEdge`, `transpose`

### DAG
- Lifts all `DirectedGraph` queries
- `ancestors`, `descendants`
- `mutilate` (do-operator), `mutilateSet`
- `isCollider`, `segmentBlocked`, `pathBlocked`
- `dSep` — d-separation as a `Prop`
- `backdoorCriterion`

### MAG
- `parents`, `children`, `spouses` (bidirected neighbors)
- `ancestors`, `descendants` (directed edges only)
- Extended `isCollider` covering directed + bidirected edge combinations
- `mSep` / `dSep` — m-separation as a `Prop`
- `ofDAG` — embeds any DAG as a MAG with no bidirected edges
- `dSep_ofDAG_iff` — DAG d-sep equals MAG m-sep under embedding

## Roadmap

- [ ] Prove `dSep_symm` and `mSep_symm`
- [ ] Prove graphoid axioms for m-separation
- [ ] Prove `dSep_ofDAG_iff` fully (remove `sorry`)
- [ ] Connect to `Mathlib.Combinatorics.SimpleGraph`
- [ ] Define probability measures on MAGs
- [ ] Prove the backdoor adjustment theorem

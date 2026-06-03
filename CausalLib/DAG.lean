-- ─────────────────────────────────────────────────────────────────────────────
-- DAG.lean
-- Directed Acyclic Graph — extends DirectedGraph, enforces acyclicity.
-- d-Separation defined here.
-- ─────────────────────────────────────────────────────────────────────────────

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import CausalLib.DirectedGraph

namespace CausalLib

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ─────────────────────────────────────────────────────────────────────────────
-- §1. DAG
-- ─────────────────────────────────────────────────────────────────────────────

/-- A Directed Acyclic Graph (DAG) over vertex type V.
    Extends DirectedGraph with an acyclicity proof:
    no node can reach itself by following directed edges. -/
structure DAG (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The underlying directed graph -/
  graph   : DirectedGraph V
  /-- Acyclicity: no node can reach itself -/
  acyclic : ∀ v : V, graph.canReach v v = false

namespace DAG

-- ─────────────────────────────────────────────────────────────────────────────
-- §2. Lifting DirectedGraph queries
-- ─────────────────────────────────────────────────────────────────────────────

/-- Direct edge u → v -/
def hasEdge (G : DAG V) (u v : V) : Bool :=
  G.graph.hasEdge u v

/-- Parents of v: nodes with a direct edge INTO v -/
def parents (G : DAG V) (v : V) : Finset V :=
  G.graph.inNeighbors v

/-- Children of v: nodes v has a direct edge TO -/
def children (G : DAG V) (v : V) : Finset V :=
  G.graph.outNeighbors v

/-- Root nodes (no parents) -/
def roots (G : DAG V) : Finset V :=
  G.graph.sources

/-- Leaf nodes (no children) -/
def leaves (G : DAG V) : Finset V :=
  G.graph.sinks

-- ─────────────────────────────────────────────────────────────────────────────
-- §3. Ancestors and Descendants
-- ─────────────────────────────────────────────────────────────────────────────

/-- Ancestors of v: all nodes that can reach v following directed edges -/
def ancestors (G : DAG V) (v : V) : Finset V :=
  G.graph.transpose.reachable v

/-- Descendants of v: all nodes reachable from v -/
def descendants (G : DAG V) (v : V) : Finset V :=
  G.graph.reachable v

/-- Is u an ancestor of v? -/
def isAncestor (G : DAG V) (u v : V) : Bool :=
  u ∈ G.ancestors v

/-- Is u a descendant of v? -/
def isDescendant (G : DAG V) (u v : V) : Bool :=
  u ∈ G.descendants v

-- ─────────────────────────────────────────────────────────────────────────────
-- §4. d-Separation
-- ─────────────────────────────────────────────────────────────────────────────

-- In a DAG, a "path" for d-separation is an UNDIRECTED path —
-- we may traverse edges in either direction.  The blocking rules
-- depend on the ORIENTATION of each edge at each interior node.

/-- On the path segment (prev, curr, next), is curr a COLLIDER?
    curr is a collider when BOTH neighbors have edges pointing INTO curr:
      prev → curr ← next
    Colliders block the path by default and open it when
    curr (or a descendant of curr) is in the conditioning set Z. -/
def isCollider (G : DAG V) (prev curr next : V) : Bool :=
  G.hasEdge prev curr && G.hasEdge next curr

/-- Is the 3-node segment (prev, curr, next) BLOCKED by conditioning set Z?
    - Non-collider (chain or fork): blocked when curr ∈ Z
    - Collider:                     blocked when curr ∉ Z
                                    AND no descendant of curr is in Z -/
def segmentBlocked (G : DAG V) (Z : Finset V) (prev curr next : V) : Bool :=
  if G.isCollider prev curr next then
    !(curr ∈ Z || (G.descendants curr ∩ Z).Nonempty)
  else
    curr ∈ Z

/-- A path (undirected sequence of nodes) is BLOCKED by Z when at least
    one interior 3-node segment is blocked.
    Paths of length 0, 1, or 2 have no interior node, so never blocked. -/
def pathBlocked (G : DAG V) (Z : Finset V) : List V → Bool
  | []                           => false
  | [_]                          => false
  | [_, _]                       => false
  | prev :: curr :: next :: rest =>
      G.segmentBlocked Z prev curr next ||
      G.pathBlocked Z (curr :: next :: rest)

/-- X and Y are D-SEPARATED by Z in G (written X ⊥_G Y | Z) iff
    every undirected path between X and Y is blocked by Z. -/
def dSep (G : DAG V) (X Y : V) (Z : Finset V) : Prop :=
  ∀ path : List V,
    path.head?    = some X →
    path.getLast? = some Y →
    G.pathBlocked Z path = true

/-- X and Y are D-CONNECTED given Z —
    there exists an active (unblocked) path between them. -/
def dConnected (G : DAG V) (X Y : V) (Z : Finset V) : Prop :=
  ∃ path : List V,
    path.head?    = some X ∧
    path.getLast? = some Y ∧
    G.pathBlocked Z path = false

end DAG
end CausalLib

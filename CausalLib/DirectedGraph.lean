-- ─────────────────────────────────────────────────────────────────────────────
-- DirectedGraph.lean
-- A general directed graph — asymmetric neighborhoods, cycles allowed.
-- ─────────────────────────────────────────────────────────────────────────────

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace CausalLib

-- ─────────────────────────────────────────────────────────────────────────────
-- §1. DirectedGraph
-- ─────────────────────────────────────────────────────────────────────────────

/-- A directed graph over a finite vertex type V.
    Represented by an adjacency relation: `adj u v` means there is a
    directed edge u → v.  Neighborhoods are asymmetric (u → v does NOT
    imply v → u), and cycles are permitted. -/
structure DirectedGraph (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Directed adjacency: `adj u v = true` iff there is an edge u → v -/
  adj         : V → V → Bool
  /-- No self-loops: a node may not have an edge to itself -/
  no_self_loop : ∀ v : V, adj v v = false

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace DirectedGraph

-- ─────────────────────────────────────────────────────────────────────────────
-- §2. Basic queries
-- ─────────────────────────────────────────────────────────────────────────────

/-- Does the edge u → v exist? -/
def hasEdge (G : DirectedGraph V) (u v : V) : Bool :=
  G.adj u v

/-- Out-neighbors of v: nodes that v points TO -/
def outNeighbors (G : DirectedGraph V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => G.adj v u)

/-- In-neighbors of v: nodes that point TO v -/
def inNeighbors (G : DirectedGraph V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => G.adj u v)

/-- All neighbors of v (union of in and out) -/
def neighbors (G : DirectedGraph V) (v : V) : Finset V :=
  G.inNeighbors v ∪ G.outNeighbors v

/-- Out-degree: number of outgoing edges from v -/
def outDegree (G : DirectedGraph V) (v : V) : ℕ :=
  (G.outNeighbors v).card

/-- In-degree: number of incoming edges to v -/
def inDegree (G : DirectedGraph V) (v : V) : ℕ :=
  (G.inNeighbors v).card

/-- Source nodes: no incoming edges -/
def sources (G : DirectedGraph V) : Finset V :=
  Finset.univ.filter (fun v => G.inNeighbors v = ∅)

/-- Sink nodes: no outgoing edges -/
def sinks (G : DirectedGraph V) : Finset V :=
  Finset.univ.filter (fun v => G.outNeighbors v = ∅)

-- ─────────────────────────────────────────────────────────────────────────────
-- §3. Reachability (depth-bounded, computable)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Nodes reachable from v by following directed edges, up to n steps.
    We bound by Fintype.card V steps; any simple path has length < |V|.
    Note: because cycles are allowed, unbounded traversal would not terminate.
    The bound ensures we find all nodes reachable via simple paths. -/
def reachableN (G : DirectedGraph V) : ℕ → V → Finset V
  | 0,     _ => ∅
  | n + 1, v =>
      G.outNeighbors v ∪
      Finset.biUnion (G.outNeighbors v) (fun u => G.reachableN n u)

/-- All nodes reachable from v (over simple paths of length < |V|) -/
def reachable (G : DirectedGraph V) (v : V) : Finset V :=
  G.reachableN (Fintype.card V) v

/-- Can we reach u from v? -/
def canReach (G : DirectedGraph V) (v u : V) : Bool :=
  u ∈ G.reachable v

-- ─────────────────────────────────────────────────────────────────────────────
-- §4. Cycle detection
-- ─────────────────────────────────────────────────────────────────────────────

/-- A node v is on a cycle if v can reach itself -/
def onCycle (G : DirectedGraph V) (v : V) : Bool :=
  G.canReach v v

/-- The graph contains at least one cycle -/
def hasCycle (G : DirectedGraph V) : Bool :=
  decide (∃ v : V, G.onCycle v = true)

/-- Is the graph acyclic? -/
def isAcyclic (G : DirectedGraph V) : Bool :=
  !G.hasCycle

-- ─────────────────────────────────────────────────────────────────────────────
-- §5. Graph operations
-- ─────────────────────────────────────────────────────────────────────────────

/-- Add a directed edge u → v.
    No cycle check — this is DirectedGraph, cycles are allowed. -/
def addEdge (G : DirectedGraph V) (u v : V) (h : u ≠ v) :
    DirectedGraph V where
  adj a b :=
    if a = u ∧ b = v then true
    else G.adj a b
  no_self_loop w := by
    split_ifs with h'
    · exact absurd (h'.1.symm.trans h'.2) h
    · exact G.no_self_loop w

/-- Remove a directed edge u → v -/
def removeEdge (G : DirectedGraph V) (u v : V) : DirectedGraph V where
  adj a b :=
    if a = u ∧ b = v then false
    else G.adj a b
  no_self_loop w := by
    split_ifs
    · rfl
    · exact G.no_self_loop w

/-- Reverse all edges: build the transposed graph -/
def transpose (G : DirectedGraph V) : DirectedGraph V where
  adj u v := G.adj v u
  no_self_loop v := G.no_self_loop v

-- ─────────────────────────────────────────────────────────────────────────────
-- §6. Basic lemmas
-- ─────────────────────────────────────────────────────────────────────────────

/-- Self-loops are always absent -/
lemma no_self_edge (G : DirectedGraph V) (v : V) :
    G.hasEdge v v = false :=
  G.no_self_loop v

/-- Asymmetry is NOT guaranteed — this is a general directed graph.
    A concrete graph can have both u → v and v → u. -/
example : ∃ G : DirectedGraph (Fin 2),
    G.hasEdge 0 1 = true ∧ G.hasEdge 1 0 = true :=
  ⟨{ adj := fun u v => decide (u ≠ v),
     no_self_loop := fun v => by simp },
   by native_decide,
   by native_decide⟩

/-- v is a source iff in-degree is 0 -/
lemma source_iff_indegree_zero (G : DirectedGraph V) (v : V) :
    v ∈ G.sources ↔ G.inDegree v = 0 := by
  simp [sources, inDegree, inNeighbors, Finset.card_eq_zero]

end DirectedGraph
end CausalLib

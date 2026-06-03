-- ─────────────────────────────────────────────────────────────────────────────
-- MAG.lean
-- Mixed Acyclic Graph (MAG) — directed AND bidirected edges, acyclic.
-- m-Separation (the MAG analogue of d-separation) defined here.
-- ─────────────────────────────────────────────────────────────────────────────

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import CausalLib.DirectedGraph
import CausalLib.DAG

namespace CausalLib

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ─────────────────────────────────────────────────────────────────────────────
-- §1. MAG structure
-- ─────────────────────────────────────────────────────────────────────────────

/-- A Mixed Acyclic Graph (MAG) over vertex type V.
    Contains two kinds of edges:
      Directed edges (→):   `directed u v = true` means u → v
      Bidirected edges (↔): `bidirected u v = true` means u ↔ v (symmetric)

    Acyclicity is enforced over directed edges only — the directed part
    must be a DAG.  Bidirected edges represent hidden common causes and
    do not participate in directed cycles. -/
structure MAG (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Directed edges -/
  directed    : V → V → Bool
  /-- Bidirected edges (must be symmetric) -/
  bidirected  : V → V → Bool
  /-- No self-loops on directed edges -/
  dir_no_loop : ∀ v : V, directed v v = false
  /-- No self-loops on bidirected edges -/
  bid_no_loop : ∀ v : V, bidirected v v = false
  /-- Bidirected edges are symmetric -/
  bid_symm    : ∀ u v : V, bidirected u v = bidirected v u
  /-- The directed part is acyclic -/
  dir_acyclic : ∀ v : V,
    (DirectedGraph.mk directed dir_no_loop).canReach v v = false

namespace MAG

-- ─────────────────────────────────────────────────────────────────────────────
-- §2. Edge queries
-- ─────────────────────────────────────────────────────────────────────────────

/-- Is there a directed edge u → v? -/
def hasDirected (G : MAG V) (u v : V) : Bool :=
  G.directed u v

/-- Is there a bidirected edge u ↔ v? -/
def hasBidirected (G : MAG V) (u v : V) : Bool :=
  G.bidirected u v

/-- Is there ANY edge between u and v (directed or bidirected)? -/
def hasEdge (G : MAG V) (u v : V) : Bool :=
  G.directed u v || G.directed v u || G.bidirected u v

/-- Parents of v: nodes with a directed edge INTO v -/
def parents (G : MAG V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => G.directed u v)

/-- Children of v: nodes v has a directed edge TO -/
def children (G : MAG V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => G.directed v u)

/-- Spouses of v: nodes connected to v by a bidirected edge -/
def spouses (G : MAG V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => G.bidirected u v)

-- ─────────────────────────────────────────────────────────────────────────────
-- §3. Ancestors and Descendants (via directed edges only)
-- ─────────────────────────────────────────────────────────────────────────────

/-- The directed part of G as a DirectedGraph -/
def directedPart (G : MAG V) : DirectedGraph V :=
  DirectedGraph.mk G.directed G.dir_no_loop

/-- Ancestors via directed edges only -/
def ancestors (G : MAG V) (v : V) : Finset V :=
  G.directedPart.transpose.reachable v

/-- Descendants via directed edges only -/
def descendants (G : MAG V) (v : V) : Finset V :=
  G.directedPart.reachable v

/-- Is u an ancestor of v (via directed edges)? -/
def isAncestor (G : MAG V) (u v : V) : Bool :=
  u ∈ G.ancestors v

-- ─────────────────────────────────────────────────────────────────────────────
-- §4. m-Separation
-- ─────────────────────────────────────────────────────────────────────────────

-- In a MAG, a node is a collider when BOTH edge marks at that node are
-- arrowheads.  This covers directed and bidirected edge combinations:
--   prev → curr ← next    prev ↔ curr ← next
--   prev → curr ↔ next    prev ↔ curr ↔ next

/-- Is curr a COLLIDER on the path segment (prev, curr, next)?
    Both the prev-side and next-side must have arrowheads pointing into curr. -/
def isCollider (G : MAG V) (prev curr next : V) : Bool :=
  let prev_into_curr := G.directed prev curr || G.bidirected prev curr
  let next_into_curr := G.directed next curr || G.bidirected next curr
  prev_into_curr && next_into_curr

/-- Is the 3-node segment (prev, curr, next) BLOCKED by Z?
    - Non-collider: blocked when curr ∈ Z
    - Collider:     blocked when neither curr nor any ancestor of curr is in Z -/
def segmentBlocked (G : MAG V) (Z : Finset V) (prev curr next : V) : Bool :=
  if G.isCollider prev curr next then
    !(curr ∈ Z || (G.ancestors curr ∩ Z).Nonempty)
  else
    curr ∈ Z

/-- A path is BLOCKED by Z when at least one interior segment is blocked. -/
def pathBlocked (G : MAG V) (Z : Finset V) : List V → Bool
  | []                           => false
  | [_]                          => false
  | [_, _]                       => false
  | prev :: curr :: next :: rest =>
      G.segmentBlocked Z prev curr next ||
      G.pathBlocked Z (curr :: next :: rest)

/-- X and Y are M-SEPARATED by Z in MAG G iff every path between
    X and Y is blocked by Z.  This is the MAG analogue of d-separation. -/
def mSep (G : MAG V) (X Y : V) (Z : Finset V) : Prop :=
  ∀ path : List V,
    path.head?    = some X →
    path.getLast? = some Y →
    G.pathBlocked Z path = true

/-- Alias: d-separation in a MAG is m-separation -/
abbrev dSep (G : MAG V) (X Y : V) (Z : Finset V) : Prop :=
  G.mSep X Y Z

-- ─────────────────────────────────────────────────────────────────────────────
-- §5. Basic lemmas
-- ─────────────────────────────────────────────────────────────────────────────

/-- Bidirected edges are symmetric by construction -/
lemma bid_symmetric (G : MAG V) (u v : V) :
    G.hasBidirected u v = G.hasBidirected v u := by
  simp [hasBidirected, G.bid_symm u v]

/-- No self-loops on directed edges -/
lemma no_self_directed (G : MAG V) (v : V) :
    G.hasDirected v v = false :=
  G.dir_no_loop v

/-- No self-loops on bidirected edges -/
lemma no_self_bidirected (G : MAG V) (v : V) :
    G.hasBidirected v v = false :=
  G.bid_no_loop v

/-- Spouses are symmetric: v ∈ spouses u ↔ u ∈ spouses v -/
lemma spouses_symm (G : MAG V) (u v : V) :
    u ∈ G.spouses v ↔ v ∈ G.spouses u := by
  simp [spouses, G.bid_symm]

end MAG
end CausalLib

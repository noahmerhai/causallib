-- ─────────────────────────────────────────────────────────────────────────────
-- DAG.lean
-- Directed Acyclic Graph — extends DirectedGraph, enforces acyclicity.
-- d-Separation defined here.
-- ─────────────────────────────────────────────────────────────────────────────

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Chain
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
-- §3b. Walks
-- ─────────────────────────────────────────────────────────────────────────────

-- A "path" for d-separation is an UNDIRECTED walk: consecutive nodes must be
-- adjacent (an edge in EITHER direction).  Quantifying d-separation over walks —
-- rather than over arbitrary node lists — is what makes it the standard,
-- non-degenerate notion: without the adjacency requirement the 2-element list
-- [x, y] would be an (unblocked) "path" between every pair, so no two nodes would
-- ever be d-separated.

/-- Two nodes are adjacent if there is a DAG edge between them in EITHER
    direction (a walk may traverse the edge either way). -/
def Adj (G : DAG V) (a b : V) : Prop :=
  G.hasEdge a b = true ∨ G.hasEdge b a = true

lemma Adj_symm (G : DAG V) {a b : V} (h : G.Adj a b) : G.Adj b a := h.symm

/-- A walk: every pair of consecutive nodes is adjacent. -/
def IsWalk (G : DAG V) (l : List V) : Prop := l.IsChain G.Adj

@[simp] lemma isWalk_nil (G : DAG V) : G.IsWalk ([] : List V) := List.isChain_nil
@[simp] lemma isWalk_singleton (G : DAG V) (a : V) : G.IsWalk [a] := List.isChain_singleton a

lemma isWalk_cons₂ (G : DAG V) (a b : V) (l : List V) :
    G.IsWalk (a :: b :: l) ↔ G.Adj a b ∧ G.IsWalk (b :: l) := List.isChain_cons_cons

/-- Reversing a walk is still a walk (adjacency is symmetric). -/
lemma isWalk_reverse (G : DAG V) (l : List V) : G.IsWalk l.reverse ↔ G.IsWalk l := by
  unfold IsWalk
  rw [List.isChain_reverse]
  exact ⟨fun h => h.imp (fun _ _ => Or.symm), fun h => h.imp (fun _ _ => Or.symm)⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- §4. d-Separation
-- ─────────────────────────────────────────────────────────────────────────────

-- The blocking rules depend on the ORIENTATION of each edge at each interior
-- node, via `isCollider` / `segmentBlocked` below.

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
    every undirected WALK between X and Y is blocked by Z. -/
def dSep (G : DAG V) (X Y : V) (Z : Finset V) : Prop :=
  ∀ path : List V,
    G.IsWalk path →
    path.head?    = some X →
    path.getLast? = some Y →
    G.pathBlocked Z path = true

/-- X and Y are D-CONNECTED given Z —
    there exists an active (unblocked) WALK between them. -/
def dConnected (G : DAG V) (X Y : V) (Z : Finset V) : Prop :=
  ∃ path : List V,
    G.IsWalk path ∧
    path.head?    = some X ∧
    path.getLast? = some Y ∧
    G.pathBlocked Z path = false

-- ─────────────────────────────────────────────────────────────────────────────
-- §4b. Edge / reachability helper lemmas (for the active-path argument)
-- ─────────────────────────────────────────────────────────────────────────────

/-- An edge gives adjacency. -/
lemma adj_of_hasEdge (G : DAG V) {a b : V} (h : G.hasEdge a b = true) : G.Adj a b :=
  Or.inl h

/-- Membership in out-neighbours is exactly having a forward edge. -/
lemma mem_outNeighbors (G : DAG V) (v u : V) :
    u ∈ G.graph.outNeighbors v ↔ G.hasEdge v u = true := by
  simp [DirectedGraph.outNeighbors, hasEdge, DirectedGraph.hasEdge]

/-- One-step unfolding of bounded reachability. -/
lemma mem_reachableN_succ (G : DAG V) (n : ℕ) (v w : V) :
    w ∈ G.graph.reachableN (n + 1) v ↔
      w ∈ G.graph.outNeighbors v ∨
        ∃ u ∈ G.graph.outNeighbors v, w ∈ G.graph.reachableN n u := by
  simp only [DirectedGraph.reachableN, Finset.mem_union, Finset.mem_biUnion]

/-- Bounded reachability is monotone: one more step reaches at least as much. -/
lemma reachableN_subset_succ (G : DAG V) (n : ℕ) (v : V) :
    G.graph.reachableN n v ⊆ G.graph.reachableN (n + 1) v := by
  induction n generalizing v with
  | zero => simp [DirectedGraph.reachableN]
  | succ m ih =>
      intro w hw
      rw [mem_reachableN_succ] at hw ⊢
      rcases hw with h | ⟨u, hu, hwu⟩
      · exact Or.inl h
      · exact Or.inr ⟨u, hu, ih u hwu⟩

/-- Bounded reachability is monotone in the step bound. -/
lemma reachableN_mono (G : DAG V) {n m : ℕ} (h : n ≤ m) (v : V) :
    G.graph.reachableN n v ⊆ G.graph.reachableN m v := by
  induction h with
  | refl => exact fun _ hx => hx
  | step _ ih => exact fun x hx => reachableN_subset_succ G _ v (ih hx)

/-- An edge lands in the descendant set. -/
lemma hasEdge_mem_descendants (G : DAG V) {a b : V} (h : G.hasEdge a b = true) :
    b ∈ G.descendants a := by
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
  have h1 : b ∈ G.graph.reachableN 1 a := by
    rw [mem_reachableN_succ]; exact Or.inl ((mem_outNeighbors G a b).mpr h)
  exact reachableN_mono G hcard a h1

/-- Acyclicity rules out 2-cycles: an edge has no reverse edge. -/
lemma no_2cycle (G : DAG V) {a b : V} (hab : G.hasEdge a b = true) :
    G.hasEdge b a = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  have hne : a ≠ b := by
    rintro rfl
    rw [hasEdge, DirectedGraph.hasEdge, G.graph.no_self_loop a] at hab
    exact absurd hab (by simp)
  have hcard : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨a, b, hne⟩
  have hb1 : b ∈ G.graph.reachableN 1 a := by
    rw [mem_reachableN_succ]; exact Or.inl ((mem_outNeighbors G a b).mpr hab)
  have ha1 : a ∈ G.graph.reachableN 1 b := by
    rw [mem_reachableN_succ]; exact Or.inl ((mem_outNeighbors G b a).mpr h)
  have ha2 : a ∈ G.graph.reachableN 2 a := by
    rw [mem_reachableN_succ]
    exact Or.inr ⟨b, (mem_outNeighbors G a b).mpr hab, ha1⟩
  have hreach : a ∈ G.descendants a := reachableN_mono G hcard a ha2
  have : G.graph.canReach a a = true := by
    simp only [DirectedGraph.canReach, descendants, DirectedGraph.reachable] at hreach ⊢
    exact decide_eq_true hreach
  rw [G.acyclic a] at this
  exact absurd this (by simp)

/-- A forward edge out of `c` makes `c` a non-collider (chain) on the segment,
    so the segment is unblocked exactly when `c ∉ Z`. -/
lemma segmentBlocked_chain (G : DAG V) (Z : Finset V) (p c n : V)
    (h : G.hasEdge c n = true) (hc : c ∉ Z) :
    G.segmentBlocked Z p c n = false := by
  have hcoll : G.isCollider p c n = false := by
    unfold isCollider; rw [no_2cycle G h, Bool.and_false]
  unfold segmentBlocked
  split
  · rename_i hh; rw [hcoll] at hh; simp at hh
  · exact decide_eq_false hc

/-- **chainBuild.** Given a descendant `w` of `q` (reachable within `n` steps) all
    of whose reachable nodes avoid `Z`, with `q ∉ Z` and an edge `p → q`, the
    directed chain `p, q, …, w` is an unblocked walk ending at `w`.

    This realises the directed path `σ : V_k → … → w` of Case (b) of the
    Active Path Lemma, already glued to its predecessor `p = V_{k-1}`. -/
lemma chainBuild (G : DAG V) (Z : Finset V) :
    ∀ (n : ℕ) (q w p : V),
      w ∈ G.graph.reachableN n q →
      (∀ u ∈ G.graph.reachableN n q, u ∉ Z) →
      G.hasEdge p q = true →
      q ∉ Z →
      ∃ rt : List V, G.IsWalk (p :: q :: rt) ∧
        (p :: q :: rt).getLast? = some w ∧
        G.pathBlocked Z (p :: q :: rt) = false := by
  intro n
  induction n with
  | zero => intro q w p hw _ _ _; simp [DirectedGraph.reachableN] at hw
  | succ m ih =>
      intro q w p hw hZ hpq hq
      rw [mem_reachableN_succ] at hw
      rcases hw with hwq | ⟨u, hu, hwu⟩
      · -- edge q → w directly; chain p, q, w
        have hqw : G.hasEdge q w = true := (mem_outNeighbors G q w).mp hwq
        refine ⟨[w], ?_, ?_, ?_⟩
        · rw [isWalk_cons₂]
          exact ⟨adj_of_hasEdge G hpq, by
            rw [isWalk_cons₂]; exact ⟨adj_of_hasEdge G hqw, isWalk_singleton G w⟩⟩
        · rfl
        · show (G.segmentBlocked Z p q w || G.pathBlocked Z [q, w]) = false
          rw [Bool.or_eq_false_iff]
          exact ⟨segmentBlocked_chain G Z p q w hqw hq, rfl⟩
      · -- edge q → u, then recurse from u to w
        have hqu : G.hasEdge q u = true := (mem_outNeighbors G q u).mp hu
        have huZ : u ∉ Z := hZ u (by rw [mem_reachableN_succ]; exact Or.inl hu)
        have hsub : G.graph.reachableN m u ⊆ G.graph.reachableN (m + 1) q := by
          intro x hx; rw [mem_reachableN_succ]; exact Or.inr ⟨u, hu, hx⟩
        obtain ⟨rt, hwalk, hlast, hblk⟩ :=
          ih u w q hwu (fun x hx => hZ x (hsub hx)) hqu huZ
        refine ⟨u :: rt, ?_, ?_, ?_⟩
        · rw [isWalk_cons₂]; exact ⟨adj_of_hasEdge G hpq, hwalk⟩
        · rw [List.getLast?_cons_cons]; exact hlast
        · show (G.segmentBlocked Z p q u || G.pathBlocked Z (q :: u :: rt)) = false
          rw [Bool.or_eq_false_iff]
          exact ⟨segmentBlocked_chain G Z p q u hqu hq, hblk⟩

-- ── Reflexive-descendant analysis of segments ───────────────────────────────

/-- `v` itself, or a descendant of `v`, lies in `S` ("a reflexive descendant of
    `v` is in `S`").  This is the collider-opening condition. -/
def hasReflDescIn (G : DAG V) (v : V) (S : Finset V) : Prop :=
  v ∈ S ∨ (G.descendants v ∩ S).Nonempty

instance (G : DAG V) (v : V) (S : Finset V) : Decidable (G.hasReflDescIn v S) := by
  unfold hasReflDescIn; infer_instance

lemma hasReflDescIn_union (G : DAG V) (v : V) (Z W : Finset V) :
    G.hasReflDescIn v (Z ∪ W) ↔ G.hasReflDescIn v Z ∨ G.hasReflDescIn v W := by
  unfold hasReflDescIn
  constructor
  · rintro (hv | ⟨x, hx⟩)
    · rcases Finset.mem_union.mp hv with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    · rw [Finset.mem_inter] at hx
      rcases Finset.mem_union.mp hx.2 with h | h
      · exact Or.inl (Or.inr ⟨x, Finset.mem_inter.mpr ⟨hx.1, h⟩⟩)
      · exact Or.inr (Or.inr ⟨x, Finset.mem_inter.mpr ⟨hx.1, h⟩⟩)
  · rintro ((h | ⟨x, hx⟩) | (h | ⟨x, hx⟩))
    · exact Or.inl (Finset.mem_union.mpr (Or.inl h))
    · rw [Finset.mem_inter] at hx
      exact Or.inr ⟨x, Finset.mem_inter.mpr ⟨hx.1, Finset.mem_union.mpr (Or.inl hx.2)⟩⟩
    · exact Or.inl (Finset.mem_union.mpr (Or.inr h))
    · rw [Finset.mem_inter] at hx
      exact Or.inr ⟨x, Finset.mem_inter.mpr ⟨hx.1, Finset.mem_union.mpr (Or.inr hx.2)⟩⟩

/-- At a collider, the segment is unblocked exactly when the collider has a
    reflexive descendant in the conditioning set. -/
lemma collider_seg_false_iff (G : DAG V) (Z : Finset V) (p c n : V)
    (h : G.isCollider p c n = true) :
    G.segmentBlocked Z p c n = false ↔ G.hasReflDescIn c Z := by
  unfold segmentBlocked hasReflDescIn
  rw [if_pos h, Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]

/-- At a non-collider, the segment is unblocked exactly when the node avoids the
    conditioning set. -/
lemma noncollider_seg_false_iff (G : DAG V) (Z : Finset V) (p c n : V)
    (h : G.isCollider p c n = false) :
    G.segmentBlocked Z p c n = false ↔ c ∉ Z := by
  unfold segmentBlocked
  rw [if_neg (by rw [h]; simp), decide_eq_false_iff_not]

-- ── Verma's Active Path Lemma ────────────────────────────────────────────────

/-- **Active Path Lemma** (Verma & Pearl).  If there is an active walk from
    (the head of) `π` to a node `y ∈ Y` given `Z ∪ W`, then there is an active
    walk with the SAME head to some node `b ∈ Y ∪ W` given `Z`.

    The proof transcribes weak_union_dsep.tex.  Scanning from the head, let the
    gluing node be the first internal node `V_k` that is either (a) in `W`, or
    (b) a collider with a reflexive descendant in `W` but none in `Z`.  We
    recurse past every earlier internal node (which is then active given `Z`
    too), and on reaching `V_k` we stop: case (a) truncates the walk at `V_k`;
    case (b) glues on the directed path to a `W`-descendant via `chainBuild`,
    turning `V_k` into a chain non-collider.  The extra conclusions
    (`head?` and the first-two-nodes are preserved) are what allow the head to be
    re-attached in the recursive step. -/
theorem active_path_lemma (G : DAG V) (Y W Z : Finset V) :
    ∀ (π : List V) (y : V), G.IsWalk π → π.getLast? = some y → y ∈ Y →
      G.pathBlocked (Z ∪ W) π = false →
      ∃ (π' : List V) (b : V), G.IsWalk π' ∧ π'.getLast? = some b ∧ b ∈ Y ∪ W ∧
        G.pathBlocked Z π' = false ∧ π'.head? = π.head? ∧
        (∀ a c t, π = a :: c :: t → ∃ t', π' = a :: c :: t') := by
  intro π
  match π with
  | [] =>
      intro y _ hl _ _; simp at hl
  | [v] =>
      intro y _ hl hy _
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      exact ⟨[v], v, isWalk_singleton G v, rfl,
        Finset.mem_union.mpr (Or.inl hy), rfl, rfl, by intro a c t h; simp at h⟩
  | [v, v2] =>
      intro y hw hl hy _
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      refine ⟨[v, v2], v2, hw, rfl, Finset.mem_union.mpr (Or.inl hy), rfl, rfl, ?_⟩
      intro a c t h; exact ⟨t, h⟩
  | v :: v2 :: v3 :: rest =>
      intro y hw hl hy hb
      rw [isWalk_cons₂] at hw
      obtain ⟨hadj, hwtail⟩ := hw
      have hb2 : (G.segmentBlocked (Z ∪ W) v v2 v3 ||
          G.pathBlocked (Z ∪ W) (v2 :: v3 :: rest)) = false := hb
      obtain ⟨hseg, htail⟩ := Bool.or_eq_false_iff.mp hb2
      rw [List.getLast?_cons_cons] at hl
      by_cases ha : v2 ∈ W
      · -- Case (a): V_k = v2 ∈ W; truncate to [v, v2].
        refine ⟨[v, v2], v2, (isWalk_cons₂ G v v2 []).mpr ⟨hadj, isWalk_singleton G v2⟩, rfl,
          Finset.mem_union.mpr (Or.inr ha), rfl, rfl, ?_⟩
        intro a c t h
        obtain ⟨rfl, hr⟩ := List.cons.inj h
        obtain ⟨rfl, _⟩ := List.cons.inj hr
        exact ⟨[], rfl⟩
      · by_cases hbcase :
          G.isCollider v v2 v3 = true ∧ G.hasReflDescIn v2 W ∧ ¬ G.hasReflDescIn v2 Z
        · -- Case (b): glue the directed path to a W-descendant.
          obtain ⟨hcoll, hWdesc, hnoZ⟩ := hbcase
          have hv2Z : v2 ∉ Z := fun h => hnoZ (Or.inl h)
          have hallZ : ∀ u ∈ G.descendants v2, u ∉ Z := by
            intro u hu huZ
            exact hnoZ (Or.inr ⟨u, Finset.mem_inter.mpr ⟨hu, huZ⟩⟩)
          obtain ⟨w, hw_desc, hwW⟩ : ∃ w, w ∈ G.descendants v2 ∧ w ∈ W := by
            rcases hWdesc with h | ⟨x, hx⟩
            · exact absurd h ha
            · rw [Finset.mem_inter] at hx; exact ⟨x, hx.1, hx.2⟩
          have hedge : G.hasEdge v v2 = true := by
            unfold isCollider at hcoll; rw [Bool.and_eq_true] at hcoll; exact hcoll.1
          obtain ⟨rt, hwalk, hlast2, hblk2⟩ :=
            chainBuild G Z (Fintype.card V) v2 w v hw_desc hallZ hedge hv2Z
          refine ⟨v :: v2 :: rt, w, hwalk, hlast2,
            Finset.mem_union.mpr (Or.inr hwW), hblk2, rfl, ?_⟩
          intro a c t h
          obtain ⟨rfl, hr⟩ := List.cons.inj h
          obtain ⟨rfl, _⟩ := List.cons.inj hr
          exact ⟨rt, rfl⟩
        · -- Neither (a) nor (b): v2 is active given Z; recurse on the tail.
          have hsegZ : G.segmentBlocked Z v v2 v3 = false := by
            by_cases hcoll : G.isCollider v v2 v3 = true
            · rw [collider_seg_false_iff G Z v v2 v3 hcoll]
              have hU : G.hasReflDescIn v2 (Z ∪ W) :=
                (collider_seg_false_iff G (Z ∪ W) v v2 v3 hcoll).mp hseg
              rw [hasReflDescIn_union] at hU
              rcases hU with hUZ | hUW
              · exact hUZ
              · by_contra hnz; exact hbcase ⟨hcoll, hUW, hnz⟩
            · have hcf : G.isCollider v v2 v3 = false := by simpa using hcoll
              rw [noncollider_seg_false_iff G Z v v2 v3 hcf]
              have hv2 : v2 ∉ Z ∪ W :=
                (noncollider_seg_false_iff G (Z ∪ W) v v2 v3 hcf).mp hseg
              exact fun h => hv2 (Finset.mem_union.mpr (Or.inl h))
          obtain ⟨π'', b, hw'', hlast'', hb'', hblk'', hhead'', hpre''⟩ :=
            active_path_lemma G Y W Z (v2 :: v3 :: rest) y hwtail hl hy htail
          obtain ⟨t', hπ''eq⟩ := hpre'' v2 v3 rest rfl
          refine ⟨v :: π'', b, ?_, ?_, hb'', ?_, rfl, ?_⟩
          · unfold IsWalk
            rw [List.isChain_cons]
            refine ⟨?_, hw''⟩
            intro z hz
            rw [hhead''] at hz
            simp only [List.head?_cons, Option.mem_some_iff] at hz
            subst hz; exact hadj
          · rw [hπ''eq, List.getLast?_cons_cons, ← hπ''eq]; exact hlast''
          · rw [hπ''eq]
            show (G.segmentBlocked Z v v2 v3 || G.pathBlocked Z (v2 :: v3 :: t')) = false
            rw [Bool.or_eq_false_iff]
            refine ⟨hsegZ, ?_⟩; rw [← hπ''eq]; exact hblk''
          · intro a c t h
            obtain ⟨rfl, hr⟩ := List.cons.inj h
            obtain ⟨rfl, _⟩ := List.cons.inj hr
            exact ⟨v3 :: t', by rw [hπ''eq]⟩
  termination_by π => π.length
  decreasing_by simp_wf

/-- **Contraction helper.**  Scanning an active walk given `Z` from the head: it
    is either still active given `Z ∪ Y`, or its first non-collider in `Y` cuts
    off a prefix that is an active walk from the same head to a node of `Y` given
    `Z`.  (Enlarging the conditioning set from `Z` to `Z ∪ Y` can only newly
    block a non-collider that lies in `Y`; colliders stay open.) -/
theorem contraction_walk (G : DAG V) (Y Z : Finset V) :
    ∀ (π : List V), G.IsWalk π → G.pathBlocked Z π = false →
      G.pathBlocked (Z ∪ Y) π = false ∨
      (∃ (π' : List V) (y' : V), G.IsWalk π' ∧ π'.head? = π.head? ∧
        π'.getLast? = some y' ∧ y' ∈ Y ∧ G.pathBlocked Z π' = false ∧
        (∀ a c t, π = a :: c :: t → ∃ t', π' = a :: c :: t') ∧
        π'.length < π.length) := by
  intro π
  match π with
  | [] => intro _ _; exact Or.inl rfl
  | [v] => intro _ _; exact Or.inl rfl
  | [v, v2] => intro _ _; exact Or.inl rfl
  | v :: v2 :: v3 :: rest =>
      intro hw hb
      rw [isWalk_cons₂] at hw
      obtain ⟨hadj, hwtail⟩ := hw
      have hb2 : (G.segmentBlocked Z v v2 v3 || G.pathBlocked Z (v2 :: v3 :: rest)) = false := hb
      obtain ⟨hseg, htail⟩ := Bool.or_eq_false_iff.mp hb2
      by_cases hfound : v2 ∈ Y ∧ G.isCollider v v2 v3 = false
      · -- First non-collider in Y: cut the prefix [v, v2].
        refine Or.inr ⟨[v, v2], v2, (isWalk_cons₂ G v v2 []).mpr ⟨hadj, isWalk_singleton G v2⟩,
          rfl, rfl, hfound.1, rfl, ?_, ?_⟩
        · intro a c t h
          obtain ⟨rfl, hr⟩ := List.cons.inj h
          obtain ⟨rfl, _⟩ := List.cons.inj hr
          exact ⟨[], rfl⟩
        · simp only [List.length_cons, List.length_nil]; omega
      · -- v2 remains unblocked under Z ∪ Y; recurse on the tail.
        have hsegZY : G.segmentBlocked (Z ∪ Y) v v2 v3 = false := by
          by_cases hcoll : G.isCollider v v2 v3 = true
          · rw [collider_seg_false_iff G (Z ∪ Y) v v2 v3 hcoll, hasReflDescIn_union]
            exact Or.inl ((collider_seg_false_iff G Z v v2 v3 hcoll).mp hseg)
          · have hcf : G.isCollider v v2 v3 = false := by simpa using hcoll
            rw [noncollider_seg_false_iff G (Z ∪ Y) v v2 v3 hcf]
            have hv2Z : v2 ∉ Z := (noncollider_seg_false_iff G Z v v2 v3 hcf).mp hseg
            have hv2Y : v2 ∉ Y := fun h => hfound ⟨h, hcf⟩
            exact fun h => (Finset.mem_union.mp h).elim hv2Z hv2Y
        rcases contraction_walk G Y Z (v2 :: v3 :: rest) hwtail htail with
          hZY | ⟨π'', y', hw'', hhead'', hlast'', hyY, hblk'', hpre'', hlen''⟩
        · refine Or.inl ?_
          show (G.segmentBlocked (Z ∪ Y) v v2 v3 || G.pathBlocked (Z ∪ Y) (v2 :: v3 :: rest)) = false
          rw [Bool.or_eq_false_iff]; exact ⟨hsegZY, hZY⟩
        · obtain ⟨t', hπ''eq⟩ := hpre'' v2 v3 rest rfl
          refine Or.inr ⟨v :: π'', y', ?_, rfl, ?_, hyY, ?_, ?_, ?_⟩
          · unfold IsWalk
            rw [List.isChain_cons]
            refine ⟨?_, hw''⟩
            intro z hz; rw [hhead''] at hz
            simp only [List.head?_cons, Option.mem_some_iff] at hz
            subst hz; exact hadj
          · rw [hπ''eq, List.getLast?_cons_cons, ← hπ''eq]; exact hlast''
          · rw [hπ''eq]
            show (G.segmentBlocked Z v v2 v3 || G.pathBlocked Z (v2 :: v3 :: t')) = false
            rw [Bool.or_eq_false_iff]; refine ⟨hseg, ?_⟩; rw [← hπ''eq]; exact hblk''
          · intro a c t h
            obtain ⟨rfl, hr⟩ := List.cons.inj h
            obtain ⟨rfl, _⟩ := List.cons.inj hr
            exact ⟨v3 :: t', by rw [hπ''eq]⟩
          · simp only [List.length_cons] at hlen'' ⊢; omega
  termination_by π => π.length
  decreasing_by simp_wf

/-- **Intersection helper.**  An active walk given `Z` ending in `Y ∪ W` can be
    re-routed (by alternately applying `contraction_walk` to `W` and to `Y`) into
    either an active walk to `Y` given `Z ∪ W`, or an active walk to `W` given
    `Z ∪ Y`, with the same head.  The alternation terminates because each
    `contraction_walk` cut produces a strictly shorter walk. -/
theorem intersection_walk (G : DAG V) (Y W Z : Finset V) :
    ∀ (π : List V) (t : V), G.IsWalk π → G.pathBlocked Z π = false →
      π.getLast? = some t → t ∈ Y ∪ W →
      (∃ (πa : List V) (a : V), G.IsWalk πa ∧ πa.head? = π.head? ∧
          πa.getLast? = some a ∧ a ∈ Y ∧ G.pathBlocked (Z ∪ W) πa = false) ∨
      (∃ (πb : List V) (b : V), G.IsWalk πb ∧ πb.head? = π.head? ∧
          πb.getLast? = some b ∧ b ∈ W ∧ G.pathBlocked (Z ∪ Y) πb = false) := by
  intro π t hwalk hactive hlast htYW
  rcases Finset.mem_union.mp htYW with hY | hW
  · -- last node in Y: try to keep it active given Z ∪ W (enlarge by W).
    rcases contraction_walk G W Z π hwalk hactive with
      hZW | ⟨π', w', hw', hhead', hlast', hw'W, hblk', _, hlen'⟩
    · exact Or.inl ⟨π, t, hwalk, rfl, hlast, hY, hZW⟩
    · rcases intersection_walk G Y W Z π' w' hw' hblk' hlast'
          (Finset.mem_union.mpr (Or.inr hw'W)) with
        ⟨πa, a, hwa, hha, hla, haY, hba⟩ | ⟨πb, b, hwb, hhb, hlb, hbW, hbb⟩
      · exact Or.inl ⟨πa, a, hwa, hha.trans hhead', hla, haY, hba⟩
      · exact Or.inr ⟨πb, b, hwb, hhb.trans hhead', hlb, hbW, hbb⟩
  · -- last node in W: try to keep it active given Z ∪ Y (enlarge by Y).
    rcases contraction_walk G Y Z π hwalk hactive with
      hZY | ⟨π', y', hw', hhead', hlast', hy'Y, hblk', _, hlen'⟩
    · exact Or.inr ⟨π, t, hwalk, rfl, hlast, hW, hZY⟩
    · rcases intersection_walk G Y W Z π' y' hw' hblk' hlast'
          (Finset.mem_union.mpr (Or.inl hy'Y)) with
        ⟨πa, a, hwa, hha, hla, haY, hba⟩ | ⟨πb, b, hwb, hhb, hlb, hbW, hbb⟩
      · exact Or.inl ⟨πa, a, hwa, hha.trans hhead', hla, haY, hba⟩
      · exact Or.inr ⟨πb, b, hwb, hhb.trans hhead', hlb, hbW, hbb⟩
  termination_by π => π.length
  decreasing_by all_goals omega

-- ─────────────────────────────────────────────────────────────────────────────
-- §5. Graphoid axioms for d-separation
-- ─────────────────────────────────────────────────────────────────────────────

-- isCollider is symmetric: the && of two Bool values is commutative.
private lemma isCollider_symm (G : DAG V) (prev curr next : V) :
    G.isCollider prev curr next = G.isCollider next curr prev := by
  simp [isCollider, Bool.and_comm]

-- segmentBlocked depends on isCollider and curr only, so it inherits symmetry.
private lemma segmentBlocked_symm (G : DAG V) (Z : Finset V) (prev curr next : V) :
    G.segmentBlocked Z prev curr next = G.segmentBlocked Z next curr prev := by
  simp [segmentBlocked, isCollider_symm]

-- A uniform one-step unfolding of `pathBlocked` valid for ALL tails `l`
-- (the raw definition only fires on a literal three-element prefix).
private lemma pathBlocked_cons_cons (G : DAG V) (Z : Finset V) (a b : V) (l : List V) :
    G.pathBlocked Z (a :: b :: l)
      = ((l.head?.elim false (fun n => G.segmentBlocked Z a b n)) || G.pathBlocked Z (b :: l)) := by
  cases l <;> rfl

-- One-step unfolding peeling a single head from an arbitrary list.
private lemma pathBlocked_cons (G : DAG V) (Z : Finset V) (a : V) (L : List V) :
    G.pathBlocked Z (a :: L)
      = ((L.head?.elim false
            (fun b => L.tail.head?.elim false (fun n => G.segmentBlocked Z a b n)))
          || G.pathBlocked Z L) := by
  cases L with
  | nil => rfl
  | cons b L' => cases L' <;> rfl

-- Appending a node to a walk that already ends in two known nodes `c, b`
-- only adds the boundary segment `(c, b, x)`.
private lemma pathBlocked_snoc (G : DAG V) (Z : Finset V) :
    ∀ (pre : List V) (c b x : V),
      G.pathBlocked Z (pre ++ [c, b, x])
        = (G.pathBlocked Z (pre ++ [c, b]) || G.segmentBlocked Z c b x) := by
  intro pre
  induction pre with
  | nil => intro c b x; simp [pathBlocked]
  | cons p pre ih =>
      intro c b x
      simp only [List.cons_append]
      rw [pathBlocked_cons (a := p) (L := pre ++ [c, b, x]),
          pathBlocked_cons (a := p) (L := pre ++ [c, b]), ih]
      have h1 : (pre ++ [c, b, x]).head? = (pre ++ [c, b]).head? := by cases pre <;> rfl
      have h2 : (pre ++ [c, b, x]).tail.head? = (pre ++ [c, b]).tail.head? := by
        cases pre with
        | nil => rfl
        | cons q pre' => cases pre' <;> rfl
      rw [h1, h2, Bool.or_assoc]

-- Reversing a walk preserves blocking: the multiset of consecutive triples is
-- reversed and each triple is flipped, and `segmentBlocked` is flip-symmetric.
private lemma pathBlocked_reverse (G : DAG V) (Z : Finset V) (path : List V) :
    G.pathBlocked Z path.reverse = G.pathBlocked Z path := by
  induction path with
  | nil => rfl
  | cons a t iht =>
    match t, iht with
    | [], _ => rfl
    | [b], _ => rfl
    | b :: h :: t'', iht =>
        have hrev : (a :: b :: h :: t'').reverse = t''.reverse ++ [h, b, a] := by
          simp [List.reverse_cons]
        have hrev2 : t''.reverse ++ [h, b] = (b :: h :: t'').reverse := by
          simp [List.reverse_cons]
        rw [hrev, pathBlocked_snoc, hrev2, iht,
            pathBlocked_cons_cons (a := a) (b := b) (l := h :: t'')]
        simp only [List.head?_cons, Option.elim_some]
        rw [segmentBlocked_symm G Z a b h, Bool.or_comm]

/-- d-Separation is symmetric: X ⊥ Y | Z → Y ⊥ X | Z -/
theorem dSep_symm (G : DAG V) (X Y : V) (Z : Finset V)
    (h : dSep G X Y Z) : dSep G Y X Z := by
  intro path hwalk hhead hlast
  rw [← pathBlocked_reverse G Z path]
  apply h
  · exact (isWalk_reverse G path).mpr hwalk
  · rwa [List.head?_reverse]
  · rwa [List.getLast?_reverse]

-- ─────────────────────────────────────────────────────────────────────────────
-- §6. Set-level d-separation and semi-graphoid axioms
-- ─────────────────────────────────────────────────────────────────────────────

/-- X ⊥ Y | Z for sets: every pair of members is d-separated. -/
def dSepSet (G : DAG V) (X Y Z : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, G.dSep x y Z

/-- Symmetry: X ⊥ Y | Z ↔ Y ⊥ X | Z -/
theorem dSepSet_symm (G : DAG V) (X Y Z : Finset V) :
    G.dSepSet X Y Z ↔ G.dSepSet Y X Z := by
  simp only [dSepSet]
  constructor
  · intro h y hy x hx
    exact dSep_symm G x y Z (h x hx y hy)
  · intro h x hx y hy
    exact dSep_symm G y x Z (h y hy x hx)

/-- Decomposition: X ⊥ Y ∪ W | Z → X ⊥ Y | Z ∧ X ⊥ W | Z
    Purely structural: projects from union membership. -/
theorem dSepSet_decomp (G : DAG V) (X Y W Z : Finset V) :
    G.dSepSet X (Y ∪ W) Z → G.dSepSet X Y Z ∧ G.dSepSet X W Z := by
  intro h
  exact ⟨fun x hx y hy => h x hx y (Finset.mem_union.mpr (.inl hy)),
         fun x hx w hw => h x hx w (Finset.mem_union.mpr (.inr hw))⟩

/-- One direction of Weak Union, proved by the contrapositive through the
    Active Path Lemma: an active walk from `X` to `Y` given `Z ∪ W` yields an
    active walk from `X` to `Y ∪ W` given `Z`, contradicting `X ⊥ Y ∪ W | Z`. -/
private lemma weak_union_half (G : DAG V) (X Y W Z : Finset V)
    (h : G.dSepSet X (Y ∪ W) Z) : G.dSepSet X Y (Z ∪ W) := by
  intro x hx y hy π hwalk hhead hlast
  by_contra hne
  rw [Bool.not_eq_true] at hne
  obtain ⟨π', b, hw', hlast', hb', hblk', hhead', _⟩ :=
    active_path_lemma G Y W Z π y hwalk hlast hy hne
  have hxb : G.dSep x b Z := h x hx b hb'
  have hcontra : G.pathBlocked Z π' = true := hxb π' hw' (by rw [hhead', hhead]) hlast'
  rw [hblk'] at hcontra
  exact absurd hcontra (by simp)

/-- **Weak Union** for d-separation: X ⊥ Y ∪ W | Z → X ⊥ Y | Z ∪ W ∧ X ⊥ W | Z ∪ Y.
    Proved directly from the d-separation definition via Verma's Active Path
    Lemma (`active_path_lemma`), transcribing weak_union_dsep.tex.  Both conjuncts
    follow from `weak_union_half`, the second by swapping the roles of Y and W. -/
theorem dSepSet_weak_union (G : DAG V) (X Y W Z : Finset V) :
    G.dSepSet X (Y ∪ W) Z →
    G.dSepSet X Y (Z ∪ W) ∧ G.dSepSet X W (Z ∪ Y) := by
  intro h
  refine ⟨weak_union_half G X Y W Z h, ?_⟩
  have h' : G.dSepSet X (W ∪ Y) Z := by rw [Finset.union_comm]; exact h
  exact weak_union_half G X W Y Z h'

/-- **Contraction**: X ⊥ Y | Z ∧ X ⊥ W | Z ∪ Y → X ⊥ Y ∪ W | Z.
    The Y-branch closes directly from `h1`.  For the W-branch, an active walk
    `x → w` given `Z` is, by `contraction_walk`, either active given `Z ∪ Y`
    (contradicting `h2`) or has an active prefix `x → y' ∈ Y` given `Z`
    (contradicting `h1`); hence no such walk exists. -/
theorem dSepSet_contraction (G : DAG V) (X Y W Z : Finset V) :
    G.dSepSet X Y Z → G.dSepSet X W (Z ∪ Y) → G.dSepSet X (Y ∪ W) Z := by
  intro h1 h2 x hx yw hyw
  rcases Finset.mem_union.mp hyw with hy | hw
  · exact h1 x hx yw hy
  · intro π hwalk hhead hlast
    by_contra hne
    rw [Bool.not_eq_true] at hne
    rcases contraction_walk G Y Z π hwalk hne with
      hZY | ⟨π', y', hw', hhead', hlast', hyY, hblk', _, _⟩
    · have hc : G.pathBlocked (Z ∪ Y) π = true := h2 x hx yw hw π hwalk hhead hlast
      rw [hZY] at hc; exact absurd hc (by simp)
    · have hc : G.pathBlocked Z π' = true :=
        h1 x hx y' hyY π' hw' (by rw [hhead', hhead]) hlast'
      rw [hblk'] at hc; exact absurd hc (by simp)

/-- d-Separation satisfies all four semi-graphoid axioms — Symmetry,
    Decomposition, Weak Union, and Contraction — all now fully proved. -/
theorem dSep_semigraphoid (G : DAG V) :
    (∀ X Y Z : Finset V, G.dSepSet X Y Z ↔ G.dSepSet Y X Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X (Y ∪ W) Z → G.dSepSet X Y Z ∧ G.dSepSet X W Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X (Y ∪ W) Z →
        G.dSepSet X Y (Z ∪ W) ∧ G.dSepSet X W (Z ∪ Y)) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X Y Z → G.dSepSet X W (Z ∪ Y) →
        G.dSepSet X (Y ∪ W) Z) :=
  ⟨fun X Y Z     => dSepSet_symm G X Y Z,
   fun X Y W Z h => dSepSet_decomp G X Y W Z h,
   fun X Y W Z h => dSepSet_weak_union G X Y W Z h,
   fun X Y W Z h1 h2 => dSepSet_contraction G X Y W Z h1 h2⟩

/-- **Intersection**: X ⊥ Y | Z ∪ W ∧ X ⊥ W | Z ∪ Y → X ⊥ Y ∪ W | Z.

    Unlike *probabilistic* independence (which needs strict positivity for
    Intersection), the graphical d-separation relation satisfies Intersection
    unconditionally — d-separation is a (compositional) graphoid.  An active walk
    `x → (Y ∪ W)` given `Z` is re-routed by `intersection_walk` into an active
    walk to `Y` given `Z ∪ W` or to `W` given `Z ∪ Y`, contradicting one of the
    hypotheses; hence no such walk exists.

    (This replaces an earlier `dSep_not_intersection_general`, whose claimed
    counterexample was incorrect: it conflated probabilistic independence with the
    graphical criterion.) -/
theorem dSepSet_intersection (G : DAG V) (X Y W Z : Finset V) :
    G.dSepSet X Y (Z ∪ W) → G.dSepSet X W (Z ∪ Y) → G.dSepSet X (Y ∪ W) Z := by
  intro h1 h2 x hx yw hyw π hwalk hhead hlast
  by_contra hne
  rw [Bool.not_eq_true] at hne
  rcases intersection_walk G Y W Z π yw hwalk hne hlast hyw with
    ⟨πa, a, hwa, hheada, hlasta, haY, hblka⟩ | ⟨πb, b, hwb, hheadb, hlastb, hbW, hblkb⟩
  · have hc : G.pathBlocked (Z ∪ W) πa = true :=
      h1 x hx a haY πa hwa (by rw [hheada, hhead]) hlasta
    rw [hblka] at hc; exact absurd hc (by simp)
  · have hc : G.pathBlocked (Z ∪ Y) πb = true :=
      h2 x hx b hbW πb hwb (by rw [hheadb, hhead]) hlastb
    rw [hblkb] at hc; exact absurd hc (by simp)

end DAG
end CausalLib

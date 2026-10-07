-- Finite DAGs, simple-path d-separation, and graphoid axioms.

import CausalLib.DirectedGraph
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Chain

namespace CausalLib

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite directed graph with no nonempty directed cycle.
    Adjacency and the no-self-loop invariant are inherited from `DirectedGraph`. -/
structure DAG (V : Type*) [Fintype V] [DecidableEq V] extends DirectedGraph V where
  /-- No vertex can reach itself by following directed edges. -/
  acyclic : ∀ v : V, toDirectedGraph.canReach v v = false

namespace DAG

-- Keep the DAG query API while sharing its implementation with DirectedGraph.

/-- The `DirectedGraph.hasEdge` query on the underlying graph. -/
abbrev hasEdge (G : DAG V) (u v : V) : Bool :=
  G.toDirectedGraph.hasEdge u v

/-- The `DirectedGraph.outNeighbors` query on the underlying graph. -/
abbrev outNeighbors (G : DAG V) (v : V) : Finset V :=
  G.toDirectedGraph.outNeighbors v

/-- The `DirectedGraph.inNeighbors` query on the underlying graph. -/
abbrev inNeighbors (G : DAG V) (v : V) : Finset V :=
  G.toDirectedGraph.inNeighbors v

/-- The `DirectedGraph.neighbors` query on the underlying graph. -/
abbrev neighbors (G : DAG V) (v : V) : Finset V :=
  G.toDirectedGraph.neighbors v

/-- The `DirectedGraph.outDegree` query on the underlying graph. -/
abbrev outDegree (G : DAG V) (v : V) : ℕ :=
  G.toDirectedGraph.outDegree v

/-- The `DirectedGraph.inDegree` query on the underlying graph. -/
abbrev inDegree (G : DAG V) (v : V) : ℕ :=
  G.toDirectedGraph.inDegree v

/-- The `DirectedGraph.sources` query on the underlying graph. -/
abbrev sources (G : DAG V) : Finset V :=
  G.toDirectedGraph.sources

/-- The `DirectedGraph.sinks` query on the underlying graph. -/
abbrev sinks (G : DAG V) : Finset V :=
  G.toDirectedGraph.sinks

/-- The `DirectedGraph.reachableN` query on the underlying graph. -/
abbrev reachableN (G : DAG V) : ℕ → V → Finset V :=
  G.toDirectedGraph.reachableN

/-- The `DirectedGraph.reachable` query on the underlying graph. -/
abbrev reachable (G : DAG V) (v : V) : Finset V :=
  G.toDirectedGraph.reachable v

/-- The `DirectedGraph.canReach` query on the underlying graph. -/
abbrev canReach (G : DAG V) (v u : V) : Bool :=
  G.toDirectedGraph.canReach v u

/-- The stored acyclicity invariant in terms of the public reachability query. -/
lemma canReach_self (G : DAG V) (v : V) : G.canReach v v = false := G.acyclic v

-- Reachability lemmas specialized to DAGs, preserving their existing signatures.

lemma mem_outNeighbors_iff (H : DAG V) (v u : V) :
    u ∈ H.outNeighbors v ↔ H.adj v u = true :=
  DirectedGraph.mem_outNeighbors_iff H.toDirectedGraph v u

lemma mem_reachableN_succ_iff (H : DAG V) (n : ℕ) (v w : V) :
    w ∈ H.reachableN (n + 1) v ↔
      w ∈ H.outNeighbors v ∨ ∃ u ∈ H.outNeighbors v, w ∈ H.reachableN n u :=
  DirectedGraph.mem_reachableN_succ_iff H.toDirectedGraph n v w

@[simp] lemma reachableN_zero (H : DAG V) (v : V) :
    H.reachableN 0 v = ∅ :=
  DirectedGraph.reachableN_zero H.toDirectedGraph v

lemma reachableN_one (H : DAG V) (v : V) :
    H.reachableN 1 v = H.outNeighbors v :=
  DirectedGraph.reachableN_one H.toDirectedGraph v

lemma reachableN_subset_succ (H : DAG V) (n : ℕ) (v : V) :
    H.reachableN n v ⊆ H.reachableN (n + 1) v :=
  DirectedGraph.reachableN_subset_succ H.toDirectedGraph n v

lemma reachableN_mono (H : DAG V) {n m : ℕ} (h : n ≤ m) (v : V) :
    H.reachableN n v ⊆ H.reachableN m v :=
  DirectedGraph.reachableN_mono H.toDirectedGraph h v

lemma reachableN_step (H : DAG V) :
    ∀ (n : ℕ) (v w u : V), w ∈ H.reachableN n v → u ∈ H.outNeighbors w →
      u ∈ H.reachableN (n + 1) v :=
  DirectedGraph.reachableN_step H.toDirectedGraph

lemma reachableN_trans (H : DAG V) :
    ∀ (m n : ℕ) (a b c : V), b ∈ H.reachableN n a → c ∈ H.reachableN m b →
      c ∈ H.reachableN (n + m) a :=
  DirectedGraph.reachableN_trans H.toDirectedGraph

lemma reachableN_alt (H : DAG V) (n : ℕ) (hn : 1 ≤ n) (v : V) :
    H.reachableN (n + 1) v
      = H.reachableN n v ∪ (H.reachableN n v).biUnion H.outNeighbors :=
  DirectedGraph.reachableN_alt H.toDirectedGraph n hn v

lemma reachableN_stable (H : DAG V) (v : V) (n : ℕ) (hn : 1 ≤ n)
    (h : H.reachableN (n + 1) v = H.reachableN n v) :
    ∀ k, H.reachableN (n + k) v = H.reachableN n v :=
  DirectedGraph.reachableN_stable H.toDirectedGraph v n hn h

lemma reachableN_subset_card (H : DAG V) (v : V) :
    ∀ m, H.reachableN m v ⊆ H.reachableN (Fintype.card V) v :=
  DirectedGraph.reachableN_subset_card H.toDirectedGraph v

-- ─────────────────────────────────────────────────────────────────────────────
-- Causal graph queries
-- ─────────────────────────────────────────────────────────────────────────────

/-- Parents of v: nodes with a direct edge INTO v -/
def parents (G : DAG V) (v : V) : Finset V :=
  G.inNeighbors v

/-- Children of v: nodes v has a direct edge TO -/
def children (G : DAG V) (v : V) : Finset V :=
  G.outNeighbors v

/-- Root nodes (no parents) -/
def roots (G : DAG V) : Finset V :=
  G.sources

/-- Leaf nodes (no children) -/
def leaves (G : DAG V) : Finset V :=
  G.sinks

-- ─────────────────────────────────────────────────────────────────────────────
-- §3. Ancestors and Descendants
-- ─────────────────────────────────────────────────────────────────────────────

/-- Ancestors of v: all nodes that can reach v following directed edges -/
def ancestors (G : DAG V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => G.canReach u v)

/-- Descendants of v: all nodes reachable from v -/
def descendants (G : DAG V) (v : V) : Finset V :=
  G.reachable v

/-- Is u an ancestor of v? -/
def isAncestor (G : DAG V) (u v : V) : Bool :=
  u ∈ G.ancestors v

/-- Is u a descendant of v? -/
def isDescendant (G : DAG V) (u v : V) : Bool :=
  u ∈ G.descendants v

-- ─────────────────────────────────────────────────────────────────────────────
-- §3b. Simple paths
-- ─────────────────────────────────────────────────────────────────────────────

-- Paths follow edges in either direction and have no repeated vertices.

/-- Two nodes are adjacent if there is a DAG edge between them in EITHER
    direction (a path may traverse the edge either way). -/
def Adj (G : DAG V) (a b : V) : Prop :=
  G.hasEdge a b = true ∨ G.hasEdge b a = true

lemma Adj_symm (G : DAG V) {a b : V} (h : G.Adj a b) : G.Adj b a := h.symm

/-- A simple path follows edges in either direction and never repeats a vertex. -/
def IsPath (G : DAG V) (l : List V) : Prop := l.IsChain G.Adj ∧ l.Nodup

@[simp] lemma isPath_nil (G : DAG V) : G.IsPath ([] : List V) :=
  ⟨List.isChain_nil, List.nodup_nil⟩

@[simp] lemma isPath_singleton (G : DAG V) (a : V) : G.IsPath [a] :=
  ⟨List.isChain_singleton a, List.nodup_singleton a⟩

lemma isPath_reverse (G : DAG V) (l : List V) : G.IsPath l.reverse ↔ G.IsPath l := by
  simp only [IsPath, List.isChain_reverse, List.nodup_reverse]
  constructor
  · rintro ⟨hc, hn⟩; exact ⟨hc.imp (fun _ _ h => h.symm), hn⟩
  · rintro ⟨hc, hn⟩; exact ⟨hc.imp (fun _ _ h => h.symm), hn⟩

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

/-- A vertex list is blocked when an interior triple is blocked.
    Lists with at most two vertices have no interior node and are unblocked.
    Adjacency and simplicity are checked by `IsPath`. -/
def pathBlocked (G : DAG V) (Z : Finset V) : List V → Bool
  | []                           => false
  | [_]                          => false
  | [_, _]                       => false
  | prev :: curr :: next :: rest =>
      G.segmentBlocked Z prev curr next ||
      G.pathBlocked Z (curr :: next :: rest)

/-- Every simple path from `X` to `Y` has an interior node blocked by `Z`.
    Endpoints are not tested for blocking. In particular, the singleton path
    makes a vertex d-connected to itself, even when it belongs to `Z`. -/
def dSep (G : DAG V) (X Y : V) (Z : Finset V) : Prop :=
  ∀ path : List V, G.IsPath path →
    path.head? = some X → path.getLast? = some Y → G.pathBlocked Z path = true

/-- There exists an active simple path from `X` to `Y` given `Z`. -/
def dConnected (G : DAG V) (X Y : V) (Z : Finset V) : Prop :=
  ∃ path : List V, G.IsPath path ∧
    path.head? = some X ∧ path.getLast? = some Y ∧ G.pathBlocked Z path = false

/-- Set-level d-separation: every pair of members is d-separated. -/
def dSepSet (G : DAG V) (X Y Z : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, G.dSep x y Z

-- ─────────────────────────────────────────────────────────────────────────────
-- §4b. Edge / reachability helper lemmas (for the active-path argument)
-- ─────────────────────────────────────────────────────────────────────────────

/-- An edge gives adjacency. -/
lemma adj_of_hasEdge (G : DAG V) {a b : V} (h : G.hasEdge a b = true) : G.Adj a b :=
  Or.inl h

/-- Membership in out-neighbours is exactly having a forward edge. -/
lemma mem_outNeighbors (G : DAG V) (v u : V) :
    u ∈ G.outNeighbors v ↔ G.hasEdge v u = true := by
  exact DirectedGraph.mem_outNeighbors_iff G.toDirectedGraph v u

/-- One-step unfolding of bounded reachability. -/
lemma mem_reachableN_succ (G : DAG V) (n : ℕ) (v w : V) :
    w ∈ G.reachableN (n + 1) v ↔
      w ∈ G.outNeighbors v ∨
        ∃ u ∈ G.outNeighbors v, w ∈ G.reachableN n u := by
  exact DirectedGraph.mem_reachableN_succ_iff G.toDirectedGraph n v w

/-- An edge lands in the descendant set. -/
lemma hasEdge_mem_descendants (G : DAG V) {a b : V} (h : G.hasEdge a b = true) :
    b ∈ G.descendants a := by
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
  have h1 : b ∈ G.reachableN 1 a := by
    rw [mem_reachableN_succ]; exact Or.inl ((mem_outNeighbors G a b).mpr h)
  exact reachableN_mono G hcard a h1

/-- Acyclicity rules out 2-cycles: an edge has no reverse edge. -/
lemma no_2cycle (G : DAG V) {a b : V} (hab : G.hasEdge a b = true) :
    G.hasEdge b a = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  have hne : a ≠ b := by
    rintro rfl
    rw [hasEdge, DirectedGraph.hasEdge, G.no_self_loop a] at hab
    exact absurd hab (by simp)
  have hcard : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨a, b, hne⟩
  have hb1 : b ∈ G.reachableN 1 a := by
    rw [mem_reachableN_succ]; exact Or.inl ((mem_outNeighbors G a b).mpr hab)
  have ha1 : a ∈ G.reachableN 1 b := by
    rw [mem_reachableN_succ]; exact Or.inl ((mem_outNeighbors G b a).mpr h)
  have ha2 : a ∈ G.reachableN 2 a := by
    rw [mem_reachableN_succ]
    exact Or.inr ⟨b, (mem_outNeighbors G a b).mpr hab, ha1⟩
  have hreach : a ∈ G.descendants a := reachableN_mono G hcard a ha2
  have : G.canReach a a = true := by
    simp only [canReach, descendants, reachable] at hreach ⊢
    exact decide_eq_true hreach
  rw [G.canReach_self a] at this
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

-- ─────────────────────────────────────────────────────────────────────────────
-- §5. Reversal preserves blocking
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

-- Appending a node to a vertex list that already ends in two known nodes `c, b`
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

-- Reversing a vertex list preserves blocking: the multiset of consecutive triples is
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

-- ─────────────────────────────────────────────────────────────────────────────
-- Reachability and path restriction helpers
-- ─────────────────────────────────────────────────────────────────────────────

/-- Directed descendants compose; the finite reachability bound is saturating. -/
lemma descendants_trans (G : DAG V) {a b c : V}
    (hab : b ∈ G.descendants a) (hbc : c ∈ G.descendants b) :
    c ∈ G.descendants a := by
  exact reachableN_subset_card G a _
    (reachableN_trans G _ _ a b c hab hbc)

private lemma not_self_descendant (G : DAG V) (v : V) : v ∉ G.descendants v := by
  intro h
  have : G.canReach v v = true := decide_eq_true h
  rw [G.canReach_self v] at this
  contradiction

private lemma pathBlocked_tail (G : DAG V) (Z : Finset V) (a : V) (L : List V)
    (h : G.pathBlocked Z (a :: L) = false) : G.pathBlocked Z L = false := by
  rw [pathBlocked_cons, Bool.or_eq_false_iff] at h
  exact h.2

private lemma pathBlocked_suffix (G : DAG V) (Z : Finset V) (A L : List V)
    (h : G.pathBlocked Z (A ++ L) = false) : G.pathBlocked Z L = false := by
  induction A with
  | nil => exact h
  | cons a A ih => exact ih (pathBlocked_tail G Z a (A ++ L) h)

private lemma pathBlocked_prefix (G : DAG V) (Z : Finset V) (A : List V) (b : V)
    (C : List V) (h : G.pathBlocked Z (A ++ b :: C) = false) :
    G.pathBlocked Z (A ++ [b]) = false := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    cases A with
    | nil => rfl
    | cons d A =>
      cases A with
      | nil =>
        have hs := (Bool.or_eq_false_iff.mp h).1
        simpa [pathBlocked] using hs
      | cons e A =>
        obtain ⟨hs, ht⟩ := Bool.or_eq_false_iff.mp h
        exact Bool.or_eq_false_iff.mpr ⟨hs, ih ht⟩

private lemma segmentBlocked_extract (G : DAG V) (Z : Finset V)
    (A : List V) (a b c : V) (C : List V)
    (h : G.pathBlocked Z (A ++ a :: b :: c :: C) = false) :
    G.segmentBlocked Z a b c = false :=
  (Bool.or_eq_false_iff.mp (pathBlocked_suffix G Z A (a :: b :: c :: C) h)).1

theorem dConnected_iff_not_dSep (G : DAG V) (X Y : V) (Z : Finset V) :
    G.dConnected X Y Z ↔ ¬ G.dSep X Y Z := by
  simp only [dConnected, dSep, not_forall, Bool.not_eq_true, exists_prop]

-- ─────────────────────────────────────────────────────────────────────────────
-- Direct simple-path proofs of the graphoid axioms
-- ─────────────────────────────────────────────────────────────────────────────

/-- Truncating a simple path preserves simplicity. -/
lemma isPath_prefix (G : DAG V) (A : List V) (v : V) (C : List V)
    (hp : G.IsPath (A ++ v :: C)) : G.IsPath (A ++ [v]) := by
  have hpre : A ++ [v] <+: A ++ v :: C := ⟨C, by simp⟩
  exact ⟨hp.1.prefix hpre, hp.2.sublist hpre.sublist⟩

/-- Every vertex after the first on a directed chain is a descendant. -/
private lemma mem_directed_chain_descendant (G : DAG V) :
    ∀ (L : List V) (a b : V), (a :: L).IsChain (fun u v => G.hasEdge u v = true) →
      b ∈ L → b ∈ G.descendants a := by
  intro L
  induction L with
  | nil => intro a b _ hb; simp at hb
  | cons c L ih =>
      intro a b hd hb
      obtain ⟨hac, ht⟩ := List.isChain_cons_cons.mp hd
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hasEdge_mem_descendants G hac
      · exact descendants_trans G (hasEdge_mem_descendants G hac) (ih c b ht hb)

/-- A directed chain in a DAG cannot repeat a vertex. -/
private lemma directed_chain_nodup (G : DAG V) :
    ∀ L : List V, L.IsChain (fun u v => G.hasEdge u v = true) → L.Nodup := by
  intro L
  induction L with
  | nil => intro _; exact List.nodup_nil
  | cons a L ih =>
      intro hd
      apply List.nodup_cons.mpr
      refine ⟨fun ha => not_self_descendant G a (mem_directed_chain_descendant G L a a hd ha), ?_⟩
      exact ih hd.tail

/-- Bounded reachability supplies a directed chain with the specified endpoints. -/
private lemma directed_chain_of_reachable (G : DAG V) :
    ∀ (n : ℕ) (a b : V), b ∈ G.reachableN n a →
      ∃ L : List V, (a :: L).IsChain (fun u v => G.hasEdge u v = true) ∧
        (a :: L).getLast? = some b := by
  intro n
  induction n with
  | zero => intro a b hb; simp at hb
  | succ n ih =>
      intro a b hb
      rcases (mem_reachableN_succ G n a b).mp hb with hab | ⟨c, hac, hcb⟩
      · exact ⟨[b], List.isChain_cons_cons.mpr
          ⟨(mem_outNeighbors G a b).mp hab, List.isChain_singleton b⟩, rfl⟩
      · obtain ⟨L, hd, hl⟩ := ih c b hcb
        exact ⟨c :: L, List.isChain_cons_cons.mpr ⟨(mem_outNeighbors G a c).mp hac, hd⟩,
          by simpa using hl⟩

private lemma directed_chain_active (G : DAG V) (Z : Finset V) :
    ∀ (L : List V) (a : V), (a :: L).IsChain (fun u v => G.hasEdge u v = true) →
      (∀ v ∈ a :: L, v ∉ Z) → G.pathBlocked Z (a :: L) = false := by
  intro L
  induction L with
  | nil => intro _ _ _; rfl
  | cons b L ih =>
      intro a hd hz
      cases L with
      | nil => rfl
      | cons c L =>
          have htail := (List.isChain_cons_cons.mp hd).2
          exact Bool.or_eq_false_iff.mpr
            ⟨segmentBlocked_chain G Z a b c (List.isChain_cons_cons.mp htail).1
              (hz b (by simp)), ih b htail (fun v hv => hz v (by simp [hv]))⟩

/-- Appending a directed continuation that avoids `Z` preserves activity:
    its first edge makes the joining vertex a non-collider. -/
private lemma pathBlocked_append_directed (G : DAG V) (Z : Finset V)
    (A : List V) (v : V) (R : List V)
    (hp : G.pathBlocked Z (A ++ [v]) = false)
    (hd : (v :: R).IsChain (fun a b => G.hasEdge a b = true))
    (hz : ∀ u ∈ v :: R, u ∉ Z) : G.pathBlocked Z (A ++ v :: R) = false := by
  induction A with
  | nil => exact directed_chain_active G Z R v hd hz
  | cons a A ih =>
      cases A with
      | nil =>
          cases R with
          | nil => rfl
          | cons b R =>
              exact Bool.or_eq_false_iff.mpr
                ⟨segmentBlocked_chain G Z a v b (List.isChain_cons_cons.mp hd).1
                  (hz v (by simp)), directed_chain_active G Z (b :: R) v hd hz⟩
      | cons b A =>
          have hh : (A ++ [v]).head? = (A ++ v :: R).head? := by cases A <;> rfl
          simp only [List.cons_append] at hp ⊢
          rw [pathBlocked_cons_cons, Bool.or_eq_false_iff] at hp ⊢
          exact ⟨hh ▸ hp.1, ih hp.2⟩

/-- Splice an active simple path with a directed path avoiding `Z`.
    At an overlap, truncate the first path and advance along the directed path.
    Once the remaining vertices are disjoint, concatenation is a simple path. -/
private lemma splice_directed_path (G : DAG V) (Z : Finset V) :
    ∀ (A : List V) (v : V) (R : List V), G.IsPath (A ++ [v]) →
      G.pathBlocked Z (A ++ [v]) = false →
      (v :: R).IsChain (fun a b => G.hasEdge a b = true) →
      (∀ u ∈ v :: R, u ∉ Z) →
      ∃ P : List V, G.IsPath P ∧ P.head? = (A ++ [v]).head? ∧
        P.getLast? = (v :: R).getLast? ∧ G.pathBlocked Z P = false := by
  intro A v R hp hb hd hz
  by_cases hover : ∃ u, u ∈ R ∧ u ∈ A ++ [v]
  · obtain ⟨u, huR, huA⟩ := hover
    obtain ⟨B, C, hR⟩ := List.append_of_mem huR
    obtain ⟨A', E, hA⟩ := List.append_of_mem huA
    have hp' := isPath_prefix G A' u E (hA ▸ hp)
    have hb' := pathBlocked_prefix G Z A' u E (hA ▸ hb)
    have hd' : (u :: C).IsChain (fun a b => G.hasEdge a b = true) := by
      apply List.IsChain.right_of_append (l₁ := v :: B)
      simpa only [hR, List.cons_append] using hd
    have hz' : ∀ w ∈ u :: C, w ∉ Z := by
      intro w hw
      apply hz w
      simp only [hR, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (List.mem_cons.mp hw))
    obtain ⟨P, hP, hh, hl, hactive⟩ := splice_directed_path G Z A' u C hp' hb' hd' hz'
    refine ⟨P, hP, ?_, ?_, hactive⟩
    · rw [hh, hA]; cases A' <;> rfl
    · rw [hl, hR]
      exact (List.getLast?_append_of_ne_nil (v :: B) (by simp : u :: C ≠ [])).symm
  · refine ⟨A ++ v :: R, ?_, ?_, ?_, pathBlocked_append_directed G Z A v R hb hd hz⟩
    · refine ⟨List.isChain_split.mpr ⟨hp.1, hd.imp (fun _ _ h => Or.inl h)⟩, ?_⟩
      have hn := List.nodup_append.mpr
        ⟨hp.2, (directed_chain_nodup G (v :: R) hd).of_cons, by
          intro a ha b hb heq
          subst b
          exact hover ⟨a, hb, ha⟩⟩
      simpa using hn
    · cases A <;> rfl
    · exact List.getLast?_append_of_ne_nil A (by simp : v :: R ≠ [])
  termination_by _ _ R => R.length
  decreasing_by simp only [hR, List.length_append, List.length_cons]; omega

/-- Locate the first blocked interior triple. The prefix ending at its centre
    is active, since that centre is an endpoint of the prefix. -/
private lemma first_blocked_segment (G : DAG V) (Z : Finset V) :
    ∀ P : List V, G.pathBlocked Z P = true →
      ∃ (A : List V) (a v b : V) (C : List V), P = A ++ a :: v :: b :: C ∧
        G.pathBlocked Z (A ++ [a, v]) = false ∧ G.segmentBlocked Z a v b = true := by
  intro P
  match P with
  | [] | [_] | [_, _] => intro h; contradiction
  | a :: b :: c :: L =>
      intro hb
      by_cases hs : G.segmentBlocked Z a b c = true
      · exact ⟨[], a, b, c, L, rfl, rfl, hs⟩
      · have hsf : G.segmentBlocked Z a b c = false := by simpa using hs
        have ht : G.pathBlocked Z (b :: c :: L) = true := by
          change (G.segmentBlocked Z a b c || G.pathBlocked Z (b :: c :: L)) = true at hb
          simpa only [hsf, Bool.false_or] using hb
        obtain ⟨A, p, q, r, C, heq, hpre, hseg⟩ := first_blocked_segment G Z (b :: c :: L) ht
        refine ⟨a :: A, p, q, r, C, ?_, ?_, hseg⟩
        · simp only [List.cons_append]; rw [heq]
        · have hh : (A ++ [p, q]).head? = some b := by
            have h := congrArg List.head? heq
            cases A <;> simpa using h.symm
          have hh2 : (A ++ [p, q]).tail.head? = some c := by
            have h := congrArg (fun xs : List V => xs.tail.head?) heq
            cases A with
            | nil => simpa using h.symm
            | cons d A => cases A <;> simpa using h.symm
          simp only [List.cons_append, pathBlocked_cons, hh, hh2, Option.elim_some]
          exact Bool.or_eq_false_iff.mpr ⟨hsf, hpre⟩
  termination_by P => P.length
  decreasing_by simp_wf

/-- **Active simple-path lemma.** An active simple path to `Y` given `Z ∪ W`
    gives an active simple path, with the same head, to `Y ∪ W` given `Z`.
    A newly blocked collider is rerouted along a directed path to `W`, using
    `splice_directed_path` to preserve simplicity even when the paths overlap. -/
theorem active_path_lemma (G : DAG V) (Y W Z : Finset V) (P : List V) (y : V)
    (hp : G.IsPath P) (hl : P.getLast? = some y) (hy : y ∈ Y)
    (hb : G.pathBlocked (Z ∪ W) P = false) :
    ∃ (Q : List V) (b : V), G.IsPath Q ∧ Q.getLast? = some b ∧ b ∈ Y ∪ W ∧
      G.pathBlocked Z Q = false ∧ Q.head? = P.head? := by
  by_cases hZ : G.pathBlocked Z P = false
  · exact ⟨P, y, hp, hl, Finset.mem_union.mpr (.inl hy), hZ, rfl⟩
  · have hZtrue : G.pathBlocked Z P = true := by simpa using hZ
    obtain ⟨A, a, v, b, C, rfl, hpre, hseg⟩ := first_blocked_segment G Z P hZtrue
    have hp' : G.IsPath (A ++ [a, v]) := by
      simpa using isPath_prefix G (A ++ [a]) v (b :: C) (by simpa using hp)
    have hh' : (A ++ [a, v]).head? = (A ++ a :: v :: b :: C).head? := by
      cases A <;> rfl
    have hsU := segmentBlocked_extract G (Z ∪ W) A a v b C hb
    by_cases hc : G.isCollider a v b = true
    · have hnoZ : ¬ G.hasReflDescIn v Z := by
        intro hv
        have hf := (collider_seg_false_iff G Z a v b hc).mpr hv
        rw [hf] at hseg
        contradiction
      have hW : G.hasReflDescIn v W := by
        have hU := (collider_seg_false_iff G (Z ∪ W) a v b hc).mp hsU
        exact ((hasReflDescIn_union G v Z W).mp hU).resolve_left hnoZ
      rcases hW with hvW | ⟨w, hw⟩
      · refine ⟨A ++ [a, v], v, hp', ?_, Finset.mem_union.mpr (.inr hvW), hpre, hh'⟩
        simp [List.getLast?_append, List.getLast?_cons]
      · obtain ⟨hwdesc, hwW⟩ := Finset.mem_inter.mp hw
        obtain ⟨R, hd, hlast⟩ := directed_chain_of_reachable G (Fintype.card V) v w hwdesc
        have hz : ∀ u ∈ v :: R, u ∉ Z := by
          intro u hu huZ
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hnoZ (Or.inl huZ)
          · exact hnoZ (Or.inr ⟨u, Finset.mem_inter.mpr
              ⟨mem_directed_chain_descendant G R v u hd hu, huZ⟩⟩)
        obtain ⟨Q, hQ, hhead, hlast', hactive⟩ :=
          splice_directed_path G Z (A ++ [a]) v R (by simpa using hp') (by simpa using hpre) hd hz
        refine ⟨Q, w, hQ, hlast'.trans hlast, Finset.mem_union.mpr (.inr hwW), hactive, ?_⟩
        exact hhead.trans (by simp only [List.append_assoc, List.singleton_append]; exact hh')
    · have hcf : G.isCollider a v b = false := by simpa using hc
      have hvZ : v ∈ Z := by simpa [segmentBlocked, hcf] using hseg
      have hvU := (noncollider_seg_false_iff G (Z ∪ W) a v b hcf).mp hsU
      exact False.elim (hvU (Finset.mem_union.mpr (.inl hvZ)))

/-- An active simple path either remains active after conditioning on `Y`,
    or has a strictly shorter active simple prefix ending in `Y`. -/
theorem contraction_path (G : DAG V) (Y Z : Finset V) (P : List V)
    (hp : G.IsPath P) (hb : G.pathBlocked Z P = false) :
    G.pathBlocked (Z ∪ Y) P = false ∨
      ∃ (Q : List V) (y : V), G.IsPath Q ∧ Q.head? = P.head? ∧ Q.getLast? = some y ∧
        y ∈ Y ∧ G.pathBlocked Z Q = false ∧ Q <+: P ∧ Q.length < P.length := by
  by_cases hU : G.pathBlocked (Z ∪ Y) P = false
  · exact Or.inl hU
  · have hUtrue : G.pathBlocked (Z ∪ Y) P = true := by simpa using hU
    obtain ⟨A, a, v, b, C, rfl, _, hsU⟩ := first_blocked_segment G (Z ∪ Y) P hUtrue
    have hsZ := segmentBlocked_extract G Z A a v b C hb
    have hcf : G.isCollider a v b = false := by
      by_contra hc
      have hct : G.isCollider a v b = true := by simpa using hc
      have hvZ := (collider_seg_false_iff G Z a v b hct).mp hsZ
      have hvU := (hasReflDescIn_union G v Z Y).mpr (Or.inl hvZ)
      have hf := (collider_seg_false_iff G (Z ∪ Y) a v b hct).mpr hvU
      rw [hf] at hsU
      contradiction
    have hvU : v ∈ Z ∪ Y := by simpa [segmentBlocked, hcf] using hsU
    have hvZ := (noncollider_seg_false_iff G Z a v b hcf).mp hsZ
    have hvY := (Finset.mem_union.mp hvU).resolve_left hvZ
    refine Or.inr ⟨A ++ [a, v], v, ?_, ?_, ?_, hvY, ?_, ?_, ?_⟩
    · simpa using isPath_prefix G (A ++ [a]) v (b :: C) (by simpa using hp)
    · cases A <;> rfl
    · simp [List.getLast?_append, List.getLast?_cons]
    · simpa using pathBlocked_prefix G Z (A ++ [a]) v (b :: C) (by simpa using hb)
    · exact ⟨b :: C, by simp⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- **Intersection helper.**  An active path given `Z` ending in `Y ∪ W` can be
    re-routed (by alternately applying `contraction_path` to `W` and to `Y`) into
    either an active path to `Y` given `Z ∪ W`, or an active path to `W` given
    `Z ∪ Y`, with the same head.  The alternation terminates because each
    `contraction_path` cut produces a strictly shorter path. -/
theorem intersection_path (G : DAG V) (Y W Z : Finset V) :
    ∀ (π : List V) (t : V), G.IsPath π → G.pathBlocked Z π = false →
      π.getLast? = some t → t ∈ Y ∪ W →
      (∃ (πa : List V) (a : V), G.IsPath πa ∧ πa.head? = π.head? ∧
          πa.getLast? = some a ∧ a ∈ Y ∧ G.pathBlocked (Z ∪ W) πa = false) ∨
      (∃ (πb : List V) (b : V), G.IsPath πb ∧ πb.head? = π.head? ∧
          πb.getLast? = some b ∧ b ∈ W ∧ G.pathBlocked (Z ∪ Y) πb = false) := by
  intro π t hpath hactive hlast htYW
  rcases Finset.mem_union.mp htYW with hY | hW
  · -- last node in Y: try to keep it active given Z ∪ W (enlarge by W).
    rcases contraction_path G W Z π hpath hactive with
      hZW | ⟨π', w', hw', hhead', hlast', hw'W, hblk', _, hlen'⟩
    · exact Or.inl ⟨π, t, hpath, rfl, hlast, hY, hZW⟩
    · rcases intersection_path G Y W Z π' w' hw' hblk' hlast'
          (Finset.mem_union.mpr (Or.inr hw'W)) with
        ⟨πa, a, hwa, hha, hla, haY, hba⟩ | ⟨πb, b, hwb, hhb, hlb, hbW, hbb⟩
      · exact Or.inl ⟨πa, a, hwa, hha.trans hhead', hla, haY, hba⟩
      · exact Or.inr ⟨πb, b, hwb, hhb.trans hhead', hlb, hbW, hbb⟩
  · -- last node in W: try to keep it active given Z ∪ Y (enlarge by Y).
    rcases contraction_path G Y Z π hpath hactive with
      hZY | ⟨π', y', hw', hhead', hlast', hy'Y, hblk', _, hlen'⟩
    · exact Or.inr ⟨π, t, hpath, rfl, hlast, hW, hZY⟩
    · rcases intersection_path G Y W Z π' y' hw' hblk' hlast'
          (Finset.mem_union.mpr (Or.inl hy'Y)) with
        ⟨πa, a, hwa, hha, hla, haY, hba⟩ | ⟨πb, b, hwb, hhb, hlb, hbW, hbb⟩
      · exact Or.inl ⟨πa, a, hwa, hha.trans hhead', hla, haY, hba⟩
      · exact Or.inr ⟨πb, b, hwb, hhb.trans hhead', hlb, hbW, hbb⟩
  termination_by π => π.length
  decreasing_by all_goals omega

/-- Symmetry of simple-path d-separation. -/
theorem dSep_symm (G : DAG V) (X Y : V) (Z : Finset V)
    (h : G.dSep X Y Z) : G.dSep Y X Z := by
  intro P hp hh hl
  rw [← pathBlocked_reverse G Z P]
  exact h P.reverse ((isPath_reverse G P).mpr hp)
    (by simpa using hl) (by simpa using hh)

theorem dSepSet_symm (G : DAG V) (X Y Z : Finset V) :
    G.dSepSet X Y Z ↔ G.dSepSet Y X Z := by
  constructor
  · intro h y hy x hx; exact dSep_symm G x y Z (h x hx y hy)
  · intro h x hx y hy; exact dSep_symm G y x Z (h y hy x hx)

theorem dSepSet_decomp (G : DAG V) (X Y W Z : Finset V) :
    G.dSepSet X (Y ∪ W) Z → G.dSepSet X Y Z ∧ G.dSepSet X W Z := by
  intro h
  exact ⟨fun x hx y hy => h x hx y (Finset.mem_union.mpr (.inl hy)),
    fun x hx w hw => h x hx w (Finset.mem_union.mpr (.inr hw))⟩

/-- One direction of Weak Union, proved by the contrapositive through the
    Active Path Lemma: an active simple path from `X` to `Y` given `Z ∪ W` yields an
    active simple path from `X` to `Y ∪ W` given `Z`, contradicting `X ⊥ Y ∪ W | Z`. -/
private lemma weak_union_path_half (G : DAG V) (X Y W Z : Finset V)
    (h : G.dSepSet X (Y ∪ W) Z) : G.dSepSet X Y (Z ∪ W) := by
  intro x hx y hy π hpath hhead hlast
  by_contra hne
  rw [Bool.not_eq_true] at hne
  obtain ⟨π', b, hw', hlast', hb', hblk', hhead'⟩ :=
    active_path_lemma G Y W Z π y hpath hlast hy hne
  have hxb : G.dSep x b Z := h x hx b hb'
  have hcontra : G.pathBlocked Z π' = true := hxb π' hw' (by rw [hhead', hhead]) hlast'
  rw [hblk'] at hcontra
  exact absurd hcontra (by simp)

/-- **Weak Union** for d-separation: X ⊥ Y ∪ W | Z → X ⊥ Y | Z ∪ W ∧ X ⊥ W | Z ∪ Y.
    Proved directly from the d-separation definition via Verma's Active Path
    Lemma (`active_path_lemma`). Both conjuncts
    follow from `weak_union_path_half`, the second by swapping the roles of Y and W. -/
theorem dSepSet_weak_union (G : DAG V) (X Y W Z : Finset V) :
    G.dSepSet X (Y ∪ W) Z →
    G.dSepSet X Y (Z ∪ W) ∧ G.dSepSet X W (Z ∪ Y) := by
  intro h
  refine ⟨weak_union_path_half G X Y W Z h, ?_⟩
  have h' : G.dSepSet X (W ∪ Y) Z := by rw [Finset.union_comm]; exact h
  exact weak_union_path_half G X W Y Z h'

/-- **Contraction**: X ⊥ Y | Z ∧ X ⊥ W | Z ∪ Y → X ⊥ Y ∪ W | Z.
    The Y-branch closes directly from `h1`.  For the W-branch, an active simple path
    `x → w` given `Z` is, by `contraction_path`, either active given `Z ∪ Y`
    (contradicting `h2`) or has an active prefix `x → y' ∈ Y` given `Z`
    (contradicting `h1`); hence no such path exists. -/
theorem dSepSet_contraction (G : DAG V) (X Y W Z : Finset V) :
    G.dSepSet X Y Z → G.dSepSet X W (Z ∪ Y) → G.dSepSet X (Y ∪ W) Z := by
  intro h1 h2 x hx yw hyw
  rcases Finset.mem_union.mp hyw with hy | hw
  · exact h1 x hx yw hy
  · intro π hpath hhead hlast
    by_contra hne
    rw [Bool.not_eq_true] at hne
    rcases contraction_path G Y Z π hpath hne with
      hZY | ⟨π', y', hw', hhead', hlast', hyY, hblk', _, _⟩
    · have hc : G.pathBlocked (Z ∪ Y) π = true := h2 x hx yw hw π hpath hhead hlast
      rw [hZY] at hc; exact absurd hc (by simp)
    · have hc : G.pathBlocked Z π' = true :=
        h1 x hx y' hyY π' hw' (by rw [hhead', hhead]) hlast'
      rw [hblk'] at hc; exact absurd hc (by simp)

/-- **Intersection**: X ⊥ Y | Z ∪ W ∧ X ⊥ W | Z ∪ Y → X ⊥ Y ∪ W | Z.

    Unlike *probabilistic* independence (which needs strict positivity for
    Intersection), the graphical d-separation relation satisfies Intersection
    unconditionally — d-separation is a (compositional) graphoid.  An active simple path
    `x → (Y ∪ W)` given `Z` is re-routed by `intersection_path` into an active
    simple path to `Y` given `Z ∪ W` or to `W` given `Z ∪ Y`, contradicting one of the
    hypotheses; hence no such path exists. -/
theorem dSepSet_intersection (G : DAG V) (X Y W Z : Finset V) :
    G.dSepSet X Y (Z ∪ W) → G.dSepSet X W (Z ∪ Y) → G.dSepSet X (Y ∪ W) Z := by
  intro h1 h2 x hx yw hyw π hpath hhead hlast
  by_contra hne
  rw [Bool.not_eq_true] at hne
  rcases intersection_path G Y W Z π yw hpath hne hlast hyw with
    ⟨πa, a, hwa, hheada, hlasta, haY, hblka⟩ | ⟨πb, b, hwb, hheadb, hlastb, hbW, hblkb⟩
  · have hc : G.pathBlocked (Z ∪ W) πa = true :=
      h1 x hx a haY πa hwa (by rw [hheada, hhead]) hlasta
    rw [hblka] at hc; exact absurd hc (by simp)
  · have hc : G.pathBlocked (Z ∪ Y) πb = true :=
      h2 x hx b hbW πb hwb (by rw [hheadb, hhead]) hlastb
    rw [hblkb] at hc; exact absurd hc (by simp)


/-- All four semigraphoid axioms for simple-path d-separation. -/
theorem dSep_semigraphoid (G : DAG V) :
    (∀ X Y Z : Finset V, G.dSepSet X Y Z ↔ G.dSepSet Y X Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X (Y ∪ W) Z → G.dSepSet X Y Z ∧ G.dSepSet X W Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X (Y ∪ W) Z →
      G.dSepSet X Y (Z ∪ W) ∧ G.dSepSet X W (Z ∪ Y)) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X Y Z → G.dSepSet X W (Z ∪ Y) →
      G.dSepSet X (Y ∪ W) Z) :=
  ⟨dSepSet_symm G, dSepSet_decomp G, dSepSet_weak_union G, dSepSet_contraction G⟩

/-- All five graphoid axioms hold for d-separation over simple paths. -/
theorem dSep_full_graphoid (G : DAG V) :
    (∀ X Y Z : Finset V, G.dSepSet X Y Z ↔ G.dSepSet Y X Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X (Y ∪ W) Z → G.dSepSet X Y Z ∧ G.dSepSet X W Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X (Y ∪ W) Z →
      G.dSepSet X Y (Z ∪ W) ∧ G.dSepSet X W (Z ∪ Y)) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X Y Z → G.dSepSet X W (Z ∪ Y) →
      G.dSepSet X (Y ∪ W) Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X Y (Z ∪ W) → G.dSepSet X W (Z ∪ Y) →
      G.dSepSet X (Y ∪ W) Z) :=
  ⟨dSepSet_symm G, dSepSet_decomp G, dSepSet_weak_union G,
    dSepSet_contraction G, dSepSet_intersection G⟩

end DAG
end CausalLib

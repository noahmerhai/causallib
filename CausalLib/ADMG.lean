-- ─────────────────────────────────────────────────────────────────────────────
-- ADMG.lean
-- Acyclic Directed Mixed Graph (ADMG) — directed AND bidirected edges,
-- directed part acyclic, bow-free.  m-Separation (the mixed-graph analogue of
-- d-separation) is defined here, and the full graphoid development of DAG.lean
-- is carried over with complete proofs (no sorries): Symmetry, Decomposition,
-- Weak Union, Contraction, and Intersection.
-- ─────────────────────────────────────────────────────────────────────────────

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Chain
import Mathlib.Tactic
import CausalLib.DirectedGraph
import CausalLib.DAG

namespace CausalLib

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ─────────────────────────────────────────────────────────────────────────────
-- §1. ADMG structure
-- ─────────────────────────────────────────────────────────────────────────────

/-- An Acyclic Directed Mixed Graph (ADMG) over vertex type V.
    Contains two kinds of edges:
      Directed edges (→):   `directed u v = true` means u → v
      Bidirected edges (↔): `bidirected u v = true` means u ↔ v (symmetric)

    Acyclicity is enforced over directed edges only — the directed part must
    be a DAG.  Bidirected edges represent hidden common causes.

    We additionally require the graph to be BOW-FREE: no pair of nodes carries
    both a directed and a bidirected edge.  Walks are represented below as
    vertex lists, which cannot distinguish parallel edges; a bow would let the
    bidirected edge masquerade as the directed one at a collider check, and
    m-separation over vertex walks would then fail Weak Union.  Bow-freeness
    makes the vertex-walk semantics faithful, and is exactly the hypothesis
    under which the graphoid axioms below are proved. -/
structure ADMG (V : Type*) [Fintype V] [DecidableEq V] where
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
  /-- Bow-free: no pair has BOTH a directed and a bidirected edge -/
  no_bow      : ∀ u v : V, directed u v = true → bidirected u v = false
  /-- The directed part is acyclic -/
  dir_acyclic : ∀ v : V,
    (DirectedGraph.mk directed dir_no_loop).canReach v v = false

namespace ADMG

-- ─────────────────────────────────────────────────────────────────────────────
-- §2. Edge queries
-- ─────────────────────────────────────────────────────────────────────────────

/-- Is there a directed edge u → v? -/
def hasDirected (G : ADMG V) (u v : V) : Bool :=
  G.directed u v

/-- Is there a bidirected edge u ↔ v? -/
def hasBidirected (G : ADMG V) (u v : V) : Bool :=
  G.bidirected u v

/-- Is there ANY edge between u and v (directed either way, or bidirected)? -/
def hasEdge (G : ADMG V) (u v : V) : Bool :=
  G.directed u v || G.directed v u || G.bidirected u v

/-- Parents of v: nodes with a directed edge INTO v -/
def parents (G : ADMG V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => G.directed u v)

/-- Children of v: nodes v has a directed edge TO -/
def children (G : ADMG V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => G.directed v u)

/-- Spouses of v: nodes connected to v by a bidirected edge -/
def spouses (G : ADMG V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => G.bidirected u v)

-- ─────────────────────────────────────────────────────────────────────────────
-- §3. The directed part, ancestors and descendants
-- ─────────────────────────────────────────────────────────────────────────────

/-- The directed part of G as a DirectedGraph -/
def directedPart (G : ADMG V) : DirectedGraph V :=
  DirectedGraph.mk G.directed G.dir_no_loop

/-- The directed part is acyclic (restatement of the structure field). -/
lemma directedPart_acyclic (G : ADMG V) (v : V) :
    G.directedPart.canReach v v = false :=
  G.dir_acyclic v

/-- Ancestors via directed edges only -/
def ancestors (G : ADMG V) (v : V) : Finset V :=
  G.directedPart.transpose.reachable v

/-- Descendants via directed edges only -/
def descendants (G : ADMG V) (v : V) : Finset V :=
  G.directedPart.reachable v

/-- Is u an ancestor of v (via directed edges)? -/
def isAncestor (G : ADMG V) (u v : V) : Bool :=
  u ∈ G.ancestors v

/-- Is u a descendant of v (via directed edges)? -/
def isDescendant (G : ADMG V) (u v : V) : Bool :=
  u ∈ G.descendants v

-- ── Reachability helper lemmas on an arbitrary directed graph ───────────────
-- (Restated privately here so they apply to `directedPart`; DAG.lean carries
--  its own copies phrased for the DAG structure.)

private lemma mem_outNeighbors (H : DirectedGraph V) (v u : V) :
    u ∈ H.outNeighbors v ↔ H.adj v u = true := by
  simp [DirectedGraph.outNeighbors]

private lemma mem_reachableN_succ (H : DirectedGraph V) (n : ℕ) (v w : V) :
    w ∈ H.reachableN (n + 1) v ↔
      w ∈ H.outNeighbors v ∨
        ∃ u ∈ H.outNeighbors v, w ∈ H.reachableN n u := by
  simp only [DirectedGraph.reachableN, Finset.mem_union, Finset.mem_biUnion]

private lemma reachableN_subset_succ (H : DirectedGraph V) (n : ℕ) (v : V) :
    H.reachableN n v ⊆ H.reachableN (n + 1) v := by
  induction n generalizing v with
  | zero => simp [DirectedGraph.reachableN]
  | succ m ih =>
      intro w hw
      rw [mem_reachableN_succ] at hw ⊢
      rcases hw with h | ⟨u, hu, hwu⟩
      · exact Or.inl h
      · exact Or.inr ⟨u, hu, ih u hwu⟩

private lemma reachableN_mono (H : DirectedGraph V) {n m : ℕ} (h : n ≤ m) (v : V) :
    H.reachableN n v ⊆ H.reachableN m v := by
  induction h with
  | refl => exact fun _ hx => hx
  | step _ ih => exact fun x hx => reachableN_subset_succ H _ v (ih hx)

/-- A directed edge lands in the descendant set. -/
lemma directed_mem_descendants (G : ADMG V) {a b : V} (h : G.directed a b = true) :
    b ∈ G.descendants a := by
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
  have h1 : b ∈ G.directedPart.reachableN 1 a := by
    rw [mem_reachableN_succ]
    exact Or.inl ((mem_outNeighbors G.directedPart a b).mpr h)
  exact reachableN_mono G.directedPart hcard a h1

/-- Acyclicity of the directed part rules out 2-cycles:
    a directed edge has no reverse directed edge. -/
lemma dir_no_2cycle (G : ADMG V) {a b : V} (hab : G.directed a b = true) :
    G.directed b a = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  have hne : a ≠ b := by
    rintro rfl
    rw [G.dir_no_loop a] at hab
    exact absurd hab (by simp)
  have hcard : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨a, b, hne⟩
  have ha1 : a ∈ G.directedPart.reachableN 1 b := by
    rw [mem_reachableN_succ]
    exact Or.inl ((mem_outNeighbors G.directedPart b a).mpr h)
  have ha2 : a ∈ G.directedPart.reachableN 2 a := by
    rw [mem_reachableN_succ]
    exact Or.inr ⟨b, (mem_outNeighbors G.directedPart a b).mpr hab, ha1⟩
  have hreach : a ∈ G.directedPart.reachable a :=
    reachableN_mono G.directedPart hcard a ha2
  have hcan : G.directedPart.canReach a a = true := by
    simp only [DirectedGraph.canReach, DirectedGraph.reachable] at hreach ⊢
    exact decide_eq_true hreach
  rw [directedPart_acyclic G a] at hcan
  exact absurd hcan (by simp)

/-- Acyclicity + bow-freeness: a directed edge c → n means NO arrowhead
    points from n back into c — neither n → c (acyclicity) nor n ↔ c (no bow).
    This is what makes a directed chain node a genuine non-collider. -/
lemma no_arrowhead_back (G : ADMG V) {c n : V} (h : G.directed c n = true) :
    (G.directed n c || G.bidirected n c) = false := by
  rw [dir_no_2cycle G h, Bool.false_or, G.bid_symm n c]
  exact G.no_bow c n h

-- ─────────────────────────────────────────────────────────────────────────────
-- §3b. Walks
-- ─────────────────────────────────────────────────────────────────────────────

-- As in DAG.lean, a "path" for m-separation is an UNDIRECTED walk: consecutive
-- nodes must be adjacent (connected by SOME edge).  Quantifying over walks —
-- rather than arbitrary node lists — is what makes m-separation the standard,
-- non-degenerate notion.

/-- Two nodes are adjacent if some edge joins them: a directed edge in either
    direction, or a bidirected edge. -/
def Adj (G : ADMG V) (a b : V) : Prop :=
  G.directed a b = true ∨ G.directed b a = true ∨ G.bidirected a b = true

lemma Adj_symm (G : ADMG V) {a b : V} (h : G.Adj a b) : G.Adj b a := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (by rw [G.bid_symm b a]; exact h))

/-- A directed edge gives adjacency. -/
lemma adj_of_directed (G : ADMG V) {a b : V} (h : G.directed a b = true) : G.Adj a b :=
  Or.inl h

/-- A bidirected edge gives adjacency. -/
lemma adj_of_bidirected (G : ADMG V) {a b : V} (h : G.bidirected a b = true) : G.Adj a b :=
  Or.inr (Or.inr h)

/-- Adjacency coincides with the Boolean edge query. -/
lemma adj_iff_hasEdge (G : ADMG V) (a b : V) : G.Adj a b ↔ G.hasEdge a b = true := by
  simp [Adj, hasEdge, or_assoc]

/-- A walk: every pair of consecutive nodes is adjacent. -/
def IsWalk (G : ADMG V) (l : List V) : Prop := l.IsChain G.Adj

@[simp] lemma isWalk_nil (G : ADMG V) : G.IsWalk ([] : List V) := List.isChain_nil
@[simp] lemma isWalk_singleton (G : ADMG V) (a : V) : G.IsWalk [a] := List.isChain_singleton a

lemma isWalk_cons₂ (G : ADMG V) (a b : V) (l : List V) :
    G.IsWalk (a :: b :: l) ↔ G.Adj a b ∧ G.IsWalk (b :: l) := List.isChain_cons_cons

/-- Reversing a walk is still a walk (adjacency is symmetric). -/
lemma isWalk_reverse (G : ADMG V) (l : List V) : G.IsWalk l.reverse ↔ G.IsWalk l := by
  unfold IsWalk
  rw [List.isChain_reverse]
  exact ⟨fun h => h.imp fun _ _ h' => G.Adj_symm h',
         fun h => h.imp fun _ _ h' => G.Adj_symm h'⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- §4. m-Separation
-- ─────────────────────────────────────────────────────────────────────────────

-- In a mixed graph, a node is a collider when BOTH edge marks at that node are
-- arrowheads.  This covers directed and bidirected edge combinations:
--   prev → curr ← next    prev ↔ curr ← next
--   prev → curr ↔ next    prev ↔ curr ↔ next

/-- Is curr a COLLIDER on the path segment (prev, curr, next)?
    Both the prev-side and next-side must have arrowheads pointing into curr. -/
def isCollider (G : ADMG V) (prev curr next : V) : Bool :=
  (G.directed prev curr || G.bidirected prev curr) &&
  (G.directed next curr || G.bidirected next curr)

/-- Is the 3-node segment (prev, curr, next) BLOCKED by conditioning set Z?
    - Non-collider: blocked when curr ∈ Z
    - Collider:     blocked when curr ∉ Z AND no (directed-edge) descendant
                    of curr is in Z — i.e. curr is opened exactly when it is
                    an ancestor of Z (curr ∈ An(Z)). -/
def segmentBlocked (G : ADMG V) (Z : Finset V) (prev curr next : V) : Bool :=
  if G.isCollider prev curr next then
    !(curr ∈ Z || (G.descendants curr ∩ Z).Nonempty)
  else
    curr ∈ Z

/-- A path is BLOCKED by Z when at least one interior 3-node segment is
    blocked.  Paths of length 0, 1, or 2 have no interior node. -/
def pathBlocked (G : ADMG V) (Z : Finset V) : List V → Bool
  | []                           => false
  | [_]                          => false
  | [_, _]                       => false
  | prev :: curr :: next :: rest =>
      G.segmentBlocked Z prev curr next ||
      G.pathBlocked Z (curr :: next :: rest)

/-- X and Y are M-SEPARATED by Z in G (written X ⊥_m Y | Z) iff every
    undirected WALK between X and Y is blocked by Z. -/
def mSep (G : ADMG V) (X Y : V) (Z : Finset V) : Prop :=
  ∀ path : List V,
    G.IsWalk path →
    path.head?    = some X →
    path.getLast? = some Y →
    G.pathBlocked Z path = true

/-- X and Y are M-CONNECTED given Z —
    there exists an active (unblocked) WALK between them. -/
def mConnected (G : ADMG V) (X Y : V) (Z : Finset V) : Prop :=
  ∃ path : List V,
    G.IsWalk path ∧
    path.head?    = some X ∧
    path.getLast? = some Y ∧
    G.pathBlocked Z path = false

/-- Alias: d-separation in an ADMG is m-separation. -/
abbrev dSep (G : ADMG V) (X Y : V) (Z : Finset V) : Prop :=
  G.mSep X Y Z

-- ─────────────────────────────────────────────────────────────────────────────
-- §4b. Chain-segment lemmas (for the active-path argument)
-- ─────────────────────────────────────────────────────────────────────────────

/-- A forward directed edge out of `c` makes `c` a non-collider (chain) on the
    segment — acyclicity kills a reverse directed edge and bow-freeness kills a
    parallel bidirected edge — so the segment is unblocked exactly when `c ∉ Z`. -/
lemma segmentBlocked_chain (G : ADMG V) (Z : Finset V) (p c n : V)
    (h : G.directed c n = true) (hc : c ∉ Z) :
    G.segmentBlocked Z p c n = false := by
  have hcoll : G.isCollider p c n = false := by
    unfold isCollider
    rw [no_arrowhead_back G h, Bool.and_false]
  unfold segmentBlocked
  split
  · rename_i hh; rw [hcoll] at hh; simp at hh
  · exact decide_eq_false hc

/-- **chainBuild.** Given a descendant `w` of `q` (reachable within `n` directed
    steps) all of whose reachable nodes avoid `Z`, with `q ∉ Z` and `p`
    adjacent to `q`, the directed chain `p, q, …, w` is an unblocked walk
    ending at `w`.

    This realises the directed path `σ : V_k → … → w` of Case (b) of the
    Active Path Lemma, already glued to its predecessor `p = V_{k-1}`. -/
lemma chainBuild (G : ADMG V) (Z : Finset V) :
    ∀ (n : ℕ) (q w p : V),
      w ∈ G.directedPart.reachableN n q →
      (∀ u ∈ G.directedPart.reachableN n q, u ∉ Z) →
      G.Adj p q →
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
        have hqw : G.directed q w = true := (mem_outNeighbors G.directedPart q w).mp hwq
        refine ⟨[w], ?_, ?_, ?_⟩
        · rw [isWalk_cons₂]
          exact ⟨hpq, by
            rw [isWalk_cons₂]; exact ⟨adj_of_directed G hqw, isWalk_singleton G w⟩⟩
        · rfl
        · show (G.segmentBlocked Z p q w || G.pathBlocked Z [q, w]) = false
          rw [Bool.or_eq_false_iff]
          exact ⟨segmentBlocked_chain G Z p q w hqw hq, rfl⟩
      · -- edge q → u, then recurse from u to w
        have hqu : G.directed q u = true := (mem_outNeighbors G.directedPart q u).mp hu
        have huZ : u ∉ Z := hZ u (by rw [mem_reachableN_succ]; exact Or.inl hu)
        have hsub : G.directedPart.reachableN m u ⊆ G.directedPart.reachableN (m + 1) q := by
          intro x hx; rw [mem_reachableN_succ]; exact Or.inr ⟨u, hu, hx⟩
        obtain ⟨rt, hwalk, hlast, hblk⟩ :=
          ih u w q hwu (fun x hx => hZ x (hsub hx)) (adj_of_directed G hqu) huZ
        refine ⟨u :: rt, ?_, ?_, ?_⟩
        · rw [isWalk_cons₂]; exact ⟨hpq, hwalk⟩
        · rw [List.getLast?_cons_cons]; exact hlast
        · show (G.segmentBlocked Z p q u || G.pathBlocked Z (q :: u :: rt)) = false
          rw [Bool.or_eq_false_iff]
          exact ⟨segmentBlocked_chain G Z p q u hqu hq, hblk⟩

-- ── Reflexive-descendant analysis of segments ───────────────────────────────

/-- `v` itself, or a (directed-edge) descendant of `v`, lies in `S` — i.e.
    `v ∈ An(S)`.  This is the collider-opening condition of m-separation. -/
def hasReflDescIn (G : ADMG V) (v : V) (S : Finset V) : Prop :=
  v ∈ S ∨ (G.descendants v ∩ S).Nonempty

instance (G : ADMG V) (v : V) (S : Finset V) : Decidable (G.hasReflDescIn v S) := by
  unfold hasReflDescIn; infer_instance

lemma hasReflDescIn_union (G : ADMG V) (v : V) (Z W : Finset V) :
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
lemma collider_seg_false_iff (G : ADMG V) (Z : Finset V) (p c n : V)
    (h : G.isCollider p c n = true) :
    G.segmentBlocked Z p c n = false ↔ G.hasReflDescIn c Z := by
  unfold segmentBlocked hasReflDescIn
  rw [if_pos h, Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]

/-- At a non-collider, the segment is unblocked exactly when the node avoids the
    conditioning set. -/
lemma noncollider_seg_false_iff (G : ADMG V) (Z : Finset V) (p c n : V)
    (h : G.isCollider p c n = false) :
    G.segmentBlocked Z p c n = false ↔ c ∉ Z := by
  unfold segmentBlocked
  rw [if_neg (by rw [h]; simp), decide_eq_false_iff_not]

-- ── Verma's Active Path Lemma ────────────────────────────────────────────────

/-- **Active Path Lemma** (Verma & Pearl, adapted to m-separation).  If there
    is an active walk from (the head of) `π` to a node `y ∈ Y` given `Z ∪ W`,
    then there is an active walk with the SAME head to some node `b ∈ Y ∪ W`
    given `Z`.

    Scanning from the head, let the gluing node be the first internal node
    `V_k` that is either (a) in `W`, or (b) a collider with a reflexive
    descendant in `W` but none in `Z`.  We recurse past every earlier internal
    node (which is then active given `Z` too), and on reaching `V_k` we stop:
    case (a) truncates the walk at `V_k`; case (b) glues on the directed path
    to a `W`-descendant via `chainBuild`, turning `V_k` into a chain
    non-collider (this is where bow-freeness and directed acyclicity are
    used).  The extra conclusions (`head?` and the first-two-nodes are
    preserved) are what allow the head to be re-attached recursively. -/
theorem active_path_lemma (G : ADMG V) (Y W Z : Finset V) :
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
          obtain ⟨_, hWdesc, hnoZ⟩ := hbcase
          have hv2Z : v2 ∉ Z := fun h => hnoZ (Or.inl h)
          have hallZ : ∀ u ∈ G.descendants v2, u ∉ Z := by
            intro u hu huZ
            exact hnoZ (Or.inr ⟨u, Finset.mem_inter.mpr ⟨hu, huZ⟩⟩)
          obtain ⟨w, hw_desc, hwW⟩ : ∃ w, w ∈ G.descendants v2 ∧ w ∈ W := by
            rcases hWdesc with h | ⟨x, hx⟩
            · exact absurd h ha
            · rw [Finset.mem_inter] at hx; exact ⟨x, hx.1, hx.2⟩
          obtain ⟨rt, hwalk, hlast2, hblk2⟩ :=
            chainBuild G Z (Fintype.card V) v2 w v hw_desc hallZ hadj hv2Z
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
theorem contraction_walk (G : ADMG V) (Y Z : Finset V) :
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
theorem intersection_walk (G : ADMG V) (Y W Z : Finset V) :
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
-- §5. Symmetry of m-separation
-- ─────────────────────────────────────────────────────────────────────────────

-- isCollider is symmetric: the && of two Bool values is commutative.
private lemma isCollider_symm (G : ADMG V) (prev curr next : V) :
    G.isCollider prev curr next = G.isCollider next curr prev := by
  simp [isCollider, Bool.and_comm]

-- segmentBlocked depends on isCollider and curr only, so it inherits symmetry.
private lemma segmentBlocked_symm (G : ADMG V) (Z : Finset V) (prev curr next : V) :
    G.segmentBlocked Z prev curr next = G.segmentBlocked Z next curr prev := by
  simp [segmentBlocked, isCollider_symm]

-- A uniform one-step unfolding of `pathBlocked` valid for ALL tails `l`
-- (the raw definition only fires on a literal three-element prefix).
private lemma pathBlocked_cons_cons (G : ADMG V) (Z : Finset V) (a b : V) (l : List V) :
    G.pathBlocked Z (a :: b :: l)
      = ((l.head?.elim false (fun n => G.segmentBlocked Z a b n)) || G.pathBlocked Z (b :: l)) := by
  cases l <;> rfl

-- One-step unfolding peeling a single head from an arbitrary list.
private lemma pathBlocked_cons (G : ADMG V) (Z : Finset V) (a : V) (L : List V) :
    G.pathBlocked Z (a :: L)
      = ((L.head?.elim false
            (fun b => L.tail.head?.elim false (fun n => G.segmentBlocked Z a b n)))
          || G.pathBlocked Z L) := by
  cases L with
  | nil => rfl
  | cons b L' => cases L' <;> rfl

-- Appending a node to a walk that already ends in two known nodes `c, b`
-- only adds the boundary segment `(c, b, x)`.
private lemma pathBlocked_snoc (G : ADMG V) (Z : Finset V) :
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
private lemma pathBlocked_reverse (G : ADMG V) (Z : Finset V) (path : List V) :
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

/-- m-Separation is symmetric: X ⊥ Y | Z → Y ⊥ X | Z -/
theorem mSep_symm (G : ADMG V) (X Y : V) (Z : Finset V)
    (h : mSep G X Y Z) : mSep G Y X Z := by
  intro path hwalk hhead hlast
  rw [← pathBlocked_reverse G Z path]
  apply h
  · exact (isWalk_reverse G path).mpr hwalk
  · rwa [List.head?_reverse]
  · rwa [List.getLast?_reverse]

-- ─────────────────────────────────────────────────────────────────────────────
-- §6. Set-level m-separation and the graphoid axioms
-- ─────────────────────────────────────────────────────────────────────────────

/-- X ⊥ Y | Z for sets: every pair of members is m-separated. -/
def mSepSet (G : ADMG V) (X Y Z : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, G.mSep x y Z

/-- Symmetry: X ⊥ Y | Z ↔ Y ⊥ X | Z -/
theorem mSepSet_symm (G : ADMG V) (X Y Z : Finset V) :
    G.mSepSet X Y Z ↔ G.mSepSet Y X Z := by
  simp only [mSepSet]
  constructor
  · intro h y hy x hx
    exact mSep_symm G x y Z (h x hx y hy)
  · intro h x hx y hy
    exact mSep_symm G y x Z (h y hy x hx)

/-- Decomposition: X ⊥ Y ∪ W | Z → X ⊥ Y | Z ∧ X ⊥ W | Z
    Purely structural: projects from union membership. -/
theorem mSepSet_decomp (G : ADMG V) (X Y W Z : Finset V) :
    G.mSepSet X (Y ∪ W) Z → G.mSepSet X Y Z ∧ G.mSepSet X W Z := by
  intro h
  exact ⟨fun x hx y hy => h x hx y (Finset.mem_union.mpr (.inl hy)),
         fun x hx w hw => h x hx w (Finset.mem_union.mpr (.inr hw))⟩

/-- One direction of Weak Union, proved by the contrapositive through the
    Active Path Lemma: an active walk from `X` to `Y` given `Z ∪ W` yields an
    active walk from `X` to `Y ∪ W` given `Z`, contradicting `X ⊥ Y ∪ W | Z`. -/
private lemma weak_union_half (G : ADMG V) (X Y W Z : Finset V)
    (h : G.mSepSet X (Y ∪ W) Z) : G.mSepSet X Y (Z ∪ W) := by
  intro x hx y hy π hwalk hhead hlast
  by_contra hne
  rw [Bool.not_eq_true] at hne
  obtain ⟨π', b, hw', hlast', hb', hblk', hhead', _⟩ :=
    active_path_lemma G Y W Z π y hwalk hlast hy hne
  have hxb : G.mSep x b Z := h x hx b hb'
  have hcontra : G.pathBlocked Z π' = true := hxb π' hw' (by rw [hhead', hhead]) hlast'
  rw [hblk'] at hcontra
  exact absurd hcontra (by simp)

/-- **Weak Union** for m-separation: X ⊥ Y ∪ W | Z → X ⊥ Y | Z ∪ W ∧ X ⊥ W | Z ∪ Y.
    Proved directly from the m-separation definition via Verma's Active Path
    Lemma (`active_path_lemma`).  Both conjuncts follow from
    `weak_union_half`, the second by swapping the roles of Y and W. -/
theorem mSepSet_weak_union (G : ADMG V) (X Y W Z : Finset V) :
    G.mSepSet X (Y ∪ W) Z →
    G.mSepSet X Y (Z ∪ W) ∧ G.mSepSet X W (Z ∪ Y) := by
  intro h
  refine ⟨weak_union_half G X Y W Z h, ?_⟩
  have h' : G.mSepSet X (W ∪ Y) Z := by rw [Finset.union_comm]; exact h
  exact weak_union_half G X W Y Z h'

/-- **Contraction**: X ⊥ Y | Z ∧ X ⊥ W | Z ∪ Y → X ⊥ Y ∪ W | Z.
    The Y-branch closes directly from `h1`.  For the W-branch, an active walk
    `x → w` given `Z` is, by `contraction_walk`, either active given `Z ∪ Y`
    (contradicting `h2`) or has an active prefix `x → y' ∈ Y` given `Z`
    (contradicting `h1`); hence no such walk exists. -/
theorem mSepSet_contraction (G : ADMG V) (X Y W Z : Finset V) :
    G.mSepSet X Y Z → G.mSepSet X W (Z ∪ Y) → G.mSepSet X (Y ∪ W) Z := by
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

/-- m-Separation on (bow-free) ADMGs satisfies all four semi-graphoid axioms —
    Symmetry, Decomposition, Weak Union, and Contraction — fully proved. -/
theorem mSep_semigraphoid (G : ADMG V) :
    (∀ X Y Z : Finset V, G.mSepSet X Y Z ↔ G.mSepSet Y X Z) ∧
    (∀ X Y W Z : Finset V, G.mSepSet X (Y ∪ W) Z → G.mSepSet X Y Z ∧ G.mSepSet X W Z) ∧
    (∀ X Y W Z : Finset V, G.mSepSet X (Y ∪ W) Z →
        G.mSepSet X Y (Z ∪ W) ∧ G.mSepSet X W (Z ∪ Y)) ∧
    (∀ X Y W Z : Finset V, G.mSepSet X Y Z → G.mSepSet X W (Z ∪ Y) →
        G.mSepSet X (Y ∪ W) Z) :=
  ⟨fun X Y Z     => mSepSet_symm G X Y Z,
   fun X Y W Z h => mSepSet_decomp G X Y W Z h,
   fun X Y W Z h => mSepSet_weak_union G X Y W Z h,
   fun X Y W Z h1 h2 => mSepSet_contraction G X Y W Z h1 h2⟩

/-- **Intersection**: X ⊥ Y | Z ∪ W ∧ X ⊥ W | Z ∪ Y → X ⊥ Y ∪ W | Z.

    As for DAGs, the graphical m-separation relation satisfies Intersection
    unconditionally — m-separation is a (compositional) graphoid.  An active
    walk `x → (Y ∪ W)` given `Z` is re-routed by `intersection_walk` into an
    active walk to `Y` given `Z ∪ W` or to `W` given `Z ∪ Y`, contradicting one
    of the hypotheses; hence no such walk exists. -/
theorem mSepSet_intersection (G : ADMG V) (X Y W Z : Finset V) :
    G.mSepSet X Y (Z ∪ W) → G.mSepSet X W (Z ∪ Y) → G.mSepSet X (Y ∪ W) Z := by
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

-- ─────────────────────────────────────────────────────────────────────────────
-- §7. Basic lemmas
-- ─────────────────────────────────────────────────────────────────────────────

/-- Bidirected edges are symmetric by construction -/
lemma bid_symmetric (G : ADMG V) (u v : V) :
    G.hasBidirected u v = G.hasBidirected v u := by
  simp [hasBidirected, G.bid_symm u v]

/-- No self-loops on directed edges -/
lemma no_self_directed (G : ADMG V) (v : V) :
    G.hasDirected v v = false :=
  G.dir_no_loop v

/-- No self-loops on bidirected edges -/
lemma no_self_bidirected (G : ADMG V) (v : V) :
    G.hasBidirected v v = false :=
  G.bid_no_loop v

/-- Bow-freeness, symmetrically: a directed edge u → v also excludes v ↔ u. -/
lemma no_bow_symm (G : ADMG V) {u v : V} (h : G.directed u v = true) :
    G.bidirected v u = false := by
  rw [G.bid_symm v u]
  exact G.no_bow u v h

/-- Spouses are symmetric: v ∈ spouses u ↔ u ∈ spouses v -/
lemma spouses_symm (G : ADMG V) (u v : V) :
    u ∈ G.spouses v ↔ v ∈ G.spouses u := by
  simp [spouses, G.bid_symm]

end ADMG

-- ─────────────────────────────────────────────────────────────────────────────
-- §8. Correspondence with DAG.lean
-- ─────────────────────────────────────────────────────────────────────────────

-- Every definition above was ported from DAG.lean, not MAG.lean.  This section
-- certifies that formally: a DAG, viewed as an ADMG with no bidirected edges,
-- has the SAME colliders, the SAME blocked segments/paths, and the SAME
-- separation relation as DAG.lean defines directly.  (MAG.lean's variants —
-- its ancestor-based collider opening and its walk-free `mSep` — would fail
-- these correspondence lemmas.)

namespace DAG

/-- View a DAG as an ADMG with no bidirected edges.  Bow-freeness holds
    vacuously. -/
def toADMG (D : DAG V) : ADMG V where
  directed    := D.graph.adj
  bidirected  := fun _ _ => false
  dir_no_loop := D.graph.no_self_loop
  bid_no_loop := fun _ => rfl
  bid_symm    := fun _ _ => rfl
  no_bow      := fun _ _ _ => rfl
  dir_acyclic := D.acyclic

/-- Adjacency agrees. -/
lemma toADMG_adj (D : DAG V) (a b : V) : D.toADMG.Adj a b ↔ D.Adj a b := by
  simp [ADMG.Adj, DAG.Adj, toADMG, DAG.hasEdge, DirectedGraph.hasEdge]

/-- Walks agree. -/
lemma toADMG_isWalk (D : DAG V) (l : List V) : D.toADMG.IsWalk l ↔ D.IsWalk l :=
  ⟨fun h => h.imp fun a b => (toADMG_adj D a b).mp,
   fun h => h.imp fun a b => (toADMG_adj D a b).mpr⟩

/-- Colliders agree: with no bidirected edges, the arrowhead-based mixed-graph
    collider is exactly the DAG collider. -/
lemma toADMG_isCollider (D : DAG V) (p c n : V) :
    D.toADMG.isCollider p c n = D.isCollider p c n := by
  simp [ADMG.isCollider, DAG.isCollider, toADMG, DAG.hasEdge, DirectedGraph.hasEdge]

/-- Descendants agree (both are directed-edge reachability). -/
lemma toADMG_descendants (D : DAG V) (v : V) :
    D.toADMG.descendants v = D.descendants v := rfl

/-- Blocked segments agree: in particular the collider-opening condition is the
    DAG one (self or DESCENDANT in Z), not an ancestor-based variant. -/
lemma toADMG_segmentBlocked (D : DAG V) (Z : Finset V) (p c n : V) :
    D.toADMG.segmentBlocked Z p c n = D.segmentBlocked Z p c n := by
  simp only [ADMG.segmentBlocked, DAG.segmentBlocked, toADMG_isCollider,
    toADMG_descendants]
  rfl

/-- Blocked paths agree. -/
lemma toADMG_pathBlocked (D : DAG V) (Z : Finset V) :
    ∀ l : List V, D.toADMG.pathBlocked Z l = D.pathBlocked Z l
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: c :: rest => by
      show (D.toADMG.segmentBlocked Z a b c || D.toADMG.pathBlocked Z (b :: c :: rest))
        = (D.segmentBlocked Z a b c || D.pathBlocked Z (b :: c :: rest))
      rw [toADMG_segmentBlocked, toADMG_pathBlocked D Z (b :: c :: rest)]

/-- **m-Separation on a bidirected-edge-free ADMG is exactly d-separation.**
    The ADMG development is a conservative extension of DAG.lean. -/
theorem toADMG_mSep_iff (D : DAG V) (X Y : V) (Z : Finset V) :
    D.toADMG.mSep X Y Z ↔ D.dSep X Y Z := by
  constructor
  · intro h path hwalk hhead hlast
    rw [← toADMG_pathBlocked]
    exact h path ((toADMG_isWalk D path).mpr hwalk) hhead hlast
  · intro h path hwalk hhead hlast
    rw [toADMG_pathBlocked]
    exact h path ((toADMG_isWalk D path).mp hwalk) hhead hlast

/-- Set-level correspondence. -/
theorem toADMG_mSepSet_iff (D : DAG V) (X Y Z : Finset V) :
    D.toADMG.mSepSet X Y Z ↔ D.dSepSet X Y Z := by
  unfold ADMG.mSepSet DAG.dSepSet
  exact forall₄_congr fun x _ y _ => toADMG_mSep_iff D x y Z

end DAG
end CausalLib

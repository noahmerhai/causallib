-- ─────────────────────────────────────────────────────────────────────────────
-- ADMG.lean
-- Acyclic Directed Mixed Graph (ADMG) — directed AND bidirected edges,
-- directed part acyclic.  GENERAL ADMGs are allowed: a pair of vertices may
-- carry BOTH a directed and a bidirected edge (a "bow").  Walks record the
-- SPECIFIC edge used at each step (a `Mark`), so collider detection stays
-- unambiguous even across a bow — no bow-freeness assumption is needed.
--
-- `dSep` is the literal textbook definition: quantified over genuine SIMPLE
-- PATHS (no repeated vertex).  Symmetry and Decomposition are proved
-- directly for it.  Weak Union, Contraction and Intersection are proved
-- here for the auxiliary, walk-quantified relation `dSepWalk` (repeats
-- allowed, the same style DAG.lean itself uses for its `dSep`).
--
-- `CausalLib/WalkToPath.lean` closes the gap: it proves `dSep ↔ dSepWalk`
-- and lands all five graphoid axioms on `dSep` itself.
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

/-- An Acyclic Directed Mixed Graph (ADMG) over vertex type V.  A GENERAL
    ADMG: a pair of vertices may carry both a directed edge and a bidirected
    edge (a "bow").  Acyclicity is enforced over directed edges only. -/
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

end ADMG

-- ─────────────────────────────────────────────────────────────────────────────
-- §3b. Marks — the specific edge used at one step of a walk
-- ─────────────────────────────────────────────────────────────────────────────

/-- Which physical edge is traversed at one step of a walk from `a` to `b`,
    and its orientation relative to the direction of travel.  Recording this
    explicitly — instead of deriving colliders from bare vertex adjacency —
    is what lets a walk pass correctly through a BOW: a pair carrying both a
    directed and a bidirected edge no longer has an ambiguous collider
    status, because the walk records which edge it actually took. -/
inductive Mark
  | dirFwd
  | dirBack
  | bidir
  deriving DecidableEq

namespace Mark

/-- Reversing the direction of travel swaps a directed edge's role; a
    bidirected edge reads the same either way. -/
def flip : Mark → Mark
  | dirFwd  => dirBack
  | dirBack => dirFwd
  | bidir   => bidir

@[simp] lemma flip_flip (m : Mark) : m.flip.flip = m := by cases m <;> rfl

/-- Does this edge have an arrowhead pointing INTO the right-hand (second)
    vertex of the step? -/
def intoRight : Mark → Bool
  | dirFwd  => true
  | dirBack => false
  | bidir   => true

/-- Does this edge have an arrowhead pointing INTO the left-hand (first)
    vertex of the step? -/
def intoLeft : Mark → Bool
  | dirFwd  => false
  | dirBack => true
  | bidir   => true

@[simp] lemma intoLeft_flip (m : Mark) : m.flip.intoLeft = m.intoRight := by cases m <;> rfl
@[simp] lemma intoRight_flip (m : Mark) : m.flip.intoRight = m.intoLeft := by cases m <;> rfl

/-- Is `m` a valid choice of edge from `x` to `y` in `G`? -/
def valid (G : ADMG V) (x y : V) : Mark → Bool
  | dirFwd  => G.directed x y
  | dirBack => G.directed y x
  | bidir   => G.bidirected x y

lemma valid_flip (G : ADMG V) (a b : V) (m : Mark) :
    valid G a b m = valid G b a m.flip := by
  cases m <;> simp [valid, flip, G.bid_symm a b]

end Mark

-- ─────────────────────────────────────────────────────────────────────────────
-- §3c. Colliders and blocking (mark-based, no bow-freeness needed)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Is the interior vertex a COLLIDER, given the marks of its two incident
    edges in walk order (`m1` from the previous vertex, `m2` to the next)?
    Both sides must have an arrowhead pointing in. -/
def isCollider (m1 m2 : Mark) : Bool := m1.intoRight && m2.intoLeft

lemma isCollider_flip_swap (m1 m2 : Mark) :
    isCollider m2.flip m1.flip = isCollider m1 m2 := by
  cases m1 <;> cases m2 <;> rfl

/-- Is the interior vertex `curr` BLOCKED by Z, given the marks of its two
    incident edges?
    - Non-collider: blocked when curr ∈ Z
    - Collider:     blocked when curr ∉ Z and no descendant of curr is in Z -/
def ADMG.segmentBlocked (G : ADMG V) (Z : Finset V) (curr : V) (m1 m2 : Mark) : Bool :=
  if isCollider m1 m2 then
    !(curr ∈ Z || (G.descendants curr ∩ Z).Nonempty)
  else
    curr ∈ Z

lemma ADMG.segmentBlocked_flip_swap (G : ADMG V) (Z : Finset V) (curr : V) (m1 m2 : Mark) :
    G.segmentBlocked Z curr m2.flip m1.flip = G.segmentBlocked Z curr m1 m2 := by
  simp [ADMG.segmentBlocked, isCollider_flip_swap]

namespace ADMG

-- ─────────────────────────────────────────────────────────────────────────────
-- §4. Walks and simple paths
-- ─────────────────────────────────────────────────────────────────────────────

/-- `IsWalk G verts marks` holds when `verts` lists the walk's vertices and
    `marks`, in lockstep, the specific edge used between each consecutive
    pair (so necessarily `marks.length + 1 = verts.length`). -/
def IsWalk (G : ADMG V) : List V → List Mark → Prop
  | [], [] => True
  | [_], [] => True
  | a :: b :: vs, m :: ms => Mark.valid G a b m = true ∧ IsWalk G (b :: vs) ms
  | _, _ => False

/-- A genuine simple path: a walk with no repeated vertex. -/
def IsPath (G : ADMG V) (verts : List V) (marks : List Mark) : Prop :=
  G.IsWalk verts marks ∧ verts.Nodup

@[simp] lemma isWalk_nil (G : ADMG V) : G.IsWalk ([] : List V) [] := trivial
@[simp] lemma isWalk_singleton (G : ADMG V) (a : V) : G.IsWalk [a] [] := trivial

/-- The length invariant an `IsWalk` always satisfies. -/
lemma isWalk_length (G : ADMG V) :
    ∀ (verts : List V) (marks : List Mark), G.IsWalk verts marks →
      marks.length + 1 = verts.length ∨ (verts = [] ∧ marks = []) := by
  intro verts
  induction verts with
  | nil => intro marks h; cases marks with
      | nil => exact Or.inr ⟨rfl, rfl⟩
      | cons m ms => exact absurd h (by simp [IsWalk])
  | cons a vs ih =>
    intro marks h
    cases vs with
    | nil =>
      cases marks with
      | nil => exact Or.inl rfl
      | cons m ms => exact absurd h (by simp [IsWalk])
    | cons b vs' =>
      cases marks with
      | nil => exact absurd h (by simp [IsWalk])
      | cons m ms =>
        obtain ⟨_, htail⟩ := h
        rcases ih ms htail with heq | ⟨hveq, _⟩
        · left; simp only [List.length_cons] at heq ⊢; omega
        · exact absurd hveq (by simp)

/-- Specialization for a nonempty vertex list (the common case). -/
lemma isWalk_length' (G : ADMG V) {verts : List V} {marks : List Mark}
    (h : G.IsWalk verts marks) (hne : verts ≠ []) :
    marks.length + 1 = verts.length := by
  rcases isWalk_length G verts marks h with heq | ⟨hveq, _⟩
  · exact heq
  · exact absurd hveq hne

lemma isWalk_cons₂ (G : ADMG V) (a b : V) (m : Mark) (l : List V) (ms : List Mark) :
    G.IsWalk (a :: b :: l) (m :: ms) ↔ Mark.valid G a b m = true ∧ G.IsWalk (b :: l) ms :=
  Iff.rfl

/-- Marks for the walk traversed backward: reverse the order and flip each
    step's orientation. -/
def reverseMarks (marks : List Mark) : List Mark := (marks.map Mark.flip).reverse

@[simp] lemma reverseMarks_nil : reverseMarks ([] : List Mark) = [] := rfl

/-- Extending a walk by one more validated step at the end. -/
private lemma isWalk_append_one (G : ADMG V) :
    ∀ (l : List V) (ms : List Mark) (c : V), G.IsWalk l ms → l.getLast? = some c →
      ∀ (x : V) (m' : Mark), Mark.valid G c x m' = true →
        G.IsWalk (l ++ [x]) (ms ++ [m']) := by
  intro l
  induction l with
  | nil => intro ms c _ hc; simp at hc
  | cons a l ih =>
    cases l with
    | nil =>
      intro ms c hwalk hc x m' hvalid
      cases ms with
      | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hc
        subst hc
        exact ⟨hvalid, trivial⟩
      | cons _ _ => exact absurd hwalk (by simp [IsWalk])
    | cons b l' =>
      intro ms c hwalk hc x m' hvalid
      cases ms with
      | nil => exact absurd hwalk (by simp [IsWalk])
      | cons m ms' =>
        obtain ⟨hv, htail⟩ := hwalk
        rw [List.getLast?_cons_cons] at hc
        have ihres := ih ms' c htail hc x m' hvalid
        exact ⟨hv, ihres⟩

/-- Reversing a walk is still a walk (with marks reversed and flipped). -/
lemma isWalk_reverse (G : ADMG V) :
    ∀ (verts : List V) (marks : List Mark), G.IsWalk verts marks →
      G.IsWalk verts.reverse (reverseMarks marks) := by
  intro verts
  induction verts with
  | nil =>
      intro marks h
      cases marks with
      | nil => simp [reverseMarks]
      | cons m ms => exact absurd h (by simp [IsWalk])
  | cons a vs ih =>
    intro marks h
    cases vs with
    | nil =>
      cases marks with
      | nil => simp [reverseMarks]
      | cons m ms => exact absurd h (by simp [IsWalk])
    | cons b vs' =>
      cases marks with
      | nil => exact absurd h (by simp [IsWalk])
      | cons m ms =>
        obtain ⟨hv, htail⟩ := h
        have ihtail := ih ms htail
        have hc : (b :: vs').reverse.getLast? = some b := by
          simp [List.getLast?_reverse]
        have hval : Mark.valid G b a m.flip = true := by
          rw [← Mark.valid_flip]; exact hv
        have hstep := isWalk_append_one G (b :: vs').reverse (reverseMarks ms) b ihtail hc a m.flip hval
        have heq1 : (a :: b :: vs').reverse = (b :: vs').reverse ++ [a] := by
          simp [List.reverse_cons]
        have heq2 : reverseMarks (m :: ms) = reverseMarks ms ++ [m.flip] := by
          simp [reverseMarks, List.reverse_cons]
        rw [heq1, heq2]
        exact hstep

-- ─────────────────────────────────────────────────────────────────────────────
-- §5. Blocked paths
-- ─────────────────────────────────────────────────────────────────────────────

/-- A path is BLOCKED by Z when at least one interior 3-node segment is
    blocked.  Paths of length 0, 1, or 2 have no interior node. -/
def pathBlocked (G : ADMG V) (Z : Finset V) : List V → List Mark → Bool
  | [], _ => false
  | [_], _ => false
  | [_, _], _ => false
  | _ :: _ :: _ :: _, [] => false
  | _ :: _ :: _ :: _, [_] => false
  | _ :: b :: c :: restV, m1 :: m2 :: restM =>
      G.segmentBlocked Z b m1 m2 || pathBlocked G Z (b :: c :: restV) (m2 :: restM)

/-- A forward directed edge out of `c` makes `c` a non-collider (chain),
    REGARDLESS of what edge precedes it — using `dirFwd` for the OUTGOING
    step forces `intoLeft = false` on that side, so `isCollider` is false no
    matter the incoming mark.  This is where the mark-based design pays off:
    no bow-freeness assumption is needed to rule out `c` masquerading as a
    collider. -/
lemma segmentBlocked_chain (G : ADMG V) (Z : Finset V) (c : V) (m1 : Mark) (hc : c ∉ Z) :
    G.segmentBlocked Z c m1 Mark.dirFwd = false := by
  have hcoll : isCollider m1 Mark.dirFwd = false := by simp [isCollider, Mark.intoLeft]
  simp [ADMG.segmentBlocked, hcoll, hc]

-- One-step unfolding of `pathBlocked`, valid for an arbitrary NONEMPTY tail
-- `l` (the raw definition only fires on a literal three/two-element prefix).
private lemma pathBlocked_cons_cons_of_ne (G : ADMG V) (Z : Finset V) (a b : V) (m1 : Mark)
    (l : List V) (ms : List Mark) (hl : l ≠ []) :
    G.pathBlocked Z (a :: b :: l) (m1 :: ms)
      = ((Option.map (fun m2 => G.segmentBlocked Z b m1 m2) ms.head?).getD false
          || G.pathBlocked Z (b :: l) ms) := by
  rcases l with _ | ⟨c, l'⟩
  · exact absurd rfl hl
  · cases ms with
    | nil => cases l' <;> simp [pathBlocked]
    | cons m2 ms' => simp [pathBlocked]

/-- Appending two more validated steps `b` (mark `m1`) then `x` (mark `m2`)
    to the end of a walk `l` (with matching mark count) only adds one new
    interior segment, at `b`. -/
private lemma pathBlocked_snoc (G : ADMG V) (Z : Finset V) :
    ∀ (l : List V) (ms : List Mark), ms.length + 1 = l.length →
      ∀ (b x : V) (m1 m2 : Mark),
        G.pathBlocked Z (l ++ [b, x]) (ms ++ [m1, m2])
          = (G.pathBlocked Z (l ++ [b]) (ms ++ [m1]) || G.segmentBlocked Z b m1 m2) := by
  intro l
  induction l with
  | nil => intro ms hlen; simp at hlen
  | cons v l ih =>
    cases l with
    | nil =>
      intro ms hlen b x m1 m2
      have hms : ms = [] := by
        have hz : ms.length = 0 := by simpa using hlen
        exact List.length_eq_zero_iff.mp hz
      subst hms
      simp [pathBlocked]
    | cons w l' =>
      intro ms hlen b x m1 m2
      cases ms with
      | nil => simp at hlen
      | cons m ms' =>
        have hlen' : ms'.length + 1 = (w :: l').length := by
          simp only [List.length_cons] at hlen ⊢; omega
        have ihres := ih ms' hlen' b x m1 m2
        simp only [List.cons_append] at ihres ⊢
        have hne1 : l' ++ [b, x] ≠ ([] : List V) := by simp
        have hne2 : l' ++ [b] ≠ ([] : List V) := by simp
        rw [pathBlocked_cons_cons_of_ne G Z v w m (l' ++ [b, x]) (ms' ++ [m1, m2]) hne1,
            pathBlocked_cons_cons_of_ne G Z v w m (l' ++ [b]) (ms' ++ [m1]) hne2]
        have h2 : (ms' ++ [m1, m2]).head? = (ms' ++ [m1]).head? := by cases ms' <;> rfl
        rw [h2, ihres, Bool.or_assoc]

/-- Reversing a walk preserves blocking: the interior triples are the same
    set (reversed order, marks swapped-and-flipped at each), and
    `segmentBlocked` is invariant under that swap-and-flip. -/
lemma pathBlocked_reverse (G : ADMG V) (Z : Finset V) :
    ∀ (verts : List V) (marks : List Mark), G.IsWalk verts marks →
      G.pathBlocked Z verts.reverse (reverseMarks marks) = G.pathBlocked Z verts marks := by
  intro verts
  induction verts with
  | nil => intro marks _; cases marks <;> rfl
  | cons a vs ih =>
    intro marks hwalk
    cases vs with
    | nil => cases marks with
        | nil => rfl
        | cons m ms => exact absurd hwalk (by simp [IsWalk])
    | cons b vs' =>
      cases marks with
      | nil => exact absurd hwalk (by simp [IsWalk])
      | cons m ms =>
        obtain ⟨hv, htail⟩ := hwalk
        cases vs' with
        | nil =>
          cases ms with
          | nil =>
            -- verts = [a,b], no interior node either way.
            rfl
          | cons _ _ => exact absurd htail (by simp [IsWalk])
        | cons c vs'' =>
          cases ms with
          | nil => exact absurd htail (by simp [IsWalk])
          | cons m2 ms' =>
            have ihres := ih (m2 :: ms') htail
            obtain ⟨_, htail2⟩ := htail
            -- Go directly from `(c::vs'').reverse` to appending BOTH `b` and
            -- `a` at once, avoiding any append-associativity bookkeeping.
            have heqV : (a :: b :: c :: vs'').reverse = (c :: vs'').reverse ++ [b, a] := by
              simp [List.reverse_cons]
            have heqM : reverseMarks (m :: m2 :: ms') = reverseMarks ms' ++ [m2.flip, m.flip] := by
              simp [reverseMarks, List.reverse_cons]
            have heqV2 : (c :: vs'').reverse ++ [b] = (b :: c :: vs'').reverse := by
              simp [List.reverse_cons]
            have heqM2 : reverseMarks ms' ++ [m2.flip] = reverseMarks (m2 :: ms') := by
              simp [reverseMarks, List.reverse_cons]
            have hlenP : (reverseMarks ms').length + 1 = (c :: vs'').reverse.length := by
              have hthis := isWalk_length' G htail2 (List.cons_ne_nil c vs'')
              simp only [reverseMarks, List.length_reverse, List.length_map,
                List.length_cons] at hthis ⊢
              omega
            rw [heqV, heqM,
                pathBlocked_snoc G Z (c :: vs'').reverse (reverseMarks ms') hlenP b a m2.flip m.flip,
                heqV2, heqM2, ihres, G.segmentBlocked_flip_swap Z b m m2, Bool.or_comm]
            rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- §6. d-Separation
-- ─────────────────────────────────────────────────────────────────────────────

/-- **d-Separation** (X ⊥ Y | Z): every genuine SIMPLE PATH (no repeated
    vertex) between X and Y is blocked by Z.  The literal textbook
    definition of separation (m-separation, or d-separation) on a mixed
    graph. -/
def dSep (G : ADMG V) (X Y : V) (Z : Finset V) : Prop :=
  ∀ (verts : List V) (marks : List Mark),
    G.IsWalk verts marks → verts.Nodup →
    verts.head?    = some X →
    verts.getLast? = some Y →
    G.pathBlocked Z verts marks = true

/-- **Auxiliary, walk-quantified separation** (repeated vertices allowed).
    `dSepWalk` is STRICTLY STRONGER than `dSep` as a hypothesis — blocking
    every walk is harder than blocking only the simple paths, which are a
    subset of the walks — and correspondingly stronger as a conclusion.
    DAG.lean's own `dSep` is exactly this walk-quantified notion.

    Weak Union, Contraction and Intersection below are proved for
    `dSepWalk`, not `dSep` directly.  `dSep_of_dSepWalk` is the direction
    that transfers for free.

    The converse — "every active walk contains an active simple path", and
    hence `dSep ↔ dSepWalk` — is proved in `CausalLib/WalkToPath.lean` by a
    minimal-witness/excision argument, which also transfers all five
    graphoid axioms onto `dSep` (`ADMG.dSep_full_graphoid`). -/
def dSepWalk (G : ADMG V) (X Y : V) (Z : Finset V) : Prop :=
  ∀ (verts : List V) (marks : List Mark),
    G.IsWalk verts marks →
    verts.head?    = some X →
    verts.getLast? = some Y →
    G.pathBlocked Z verts marks = true

/-- Blocking every walk certainly blocks every simple path (a path is a
    special case of a walk). -/
lemma dSep_of_dSepWalk (G : ADMG V) (X Y : V) (Z : Finset V)
    (h : G.dSepWalk X Y Z) : G.dSep X Y Z :=
  fun verts marks hwalk _ hhead hlast => h verts marks hwalk hhead hlast

/-- d-Separation is symmetric: X ⊥ Y | Z → Y ⊥ X | Z -/
theorem dSep_symm (G : ADMG V) (X Y : V) (Z : Finset V) (h : G.dSep X Y Z) :
    G.dSep Y X Z := by
  intro verts marks hwalk hnodup hhead hlast
  rw [← pathBlocked_reverse G Z verts marks hwalk]
  apply h
  · exact isWalk_reverse G verts marks hwalk
  · exact List.nodup_reverse.mpr hnodup
  · rwa [List.head?_reverse]
  · rwa [List.getLast?_reverse]

/-- d-Separation (walk-quantified) is symmetric. -/
theorem dSepWalk_symm (G : ADMG V) (X Y : V) (Z : Finset V) (h : G.dSepWalk X Y Z) :
    G.dSepWalk Y X Z := by
  intro verts marks hwalk hhead hlast
  rw [← pathBlocked_reverse G Z verts marks hwalk]
  apply h
  · exact isWalk_reverse G verts marks hwalk
  · rwa [List.head?_reverse]
  · rwa [List.getLast?_reverse]

-- ─────────────────────────────────────────────────────────────────────────────
-- §7. Set-level separation and Symmetry / Decomposition
-- ─────────────────────────────────────────────────────────────────────────────

/-- X ⊥ Y | Z for sets: every pair of members is d-separated (path-quantified). -/
def dSepSet (G : ADMG V) (X Y Z : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, G.dSep x y Z

/-- X ⊥ Y | Z for sets, walk-quantified. -/
def dSepSetWalk (G : ADMG V) (X Y Z : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, G.dSepWalk x y Z

lemma dSepSet_of_dSepSetWalk (G : ADMG V) (X Y Z : Finset V) (h : G.dSepSetWalk X Y Z) :
    G.dSepSet X Y Z :=
  fun x hx y hy => dSep_of_dSepWalk G x y Z (h x hx y hy)

/-- Symmetry: X ⊥ Y | Z ↔ Y ⊥ X | Z -/
theorem dSepSet_symm (G : ADMG V) (X Y Z : Finset V) :
    G.dSepSet X Y Z ↔ G.dSepSet Y X Z := by
  constructor
  · intro h y hy x hx; exact dSep_symm G x y Z (h x hx y hy)
  · intro h x hx y hy; exact dSep_symm G y x Z (h y hy x hx)

theorem dSepSetWalk_symm (G : ADMG V) (X Y Z : Finset V) :
    G.dSepSetWalk X Y Z ↔ G.dSepSetWalk Y X Z := by
  constructor
  · intro h y hy x hx; exact dSepWalk_symm G x y Z (h x hx y hy)
  · intro h x hx y hy; exact dSepWalk_symm G y x Z (h y hy x hx)

/-- Decomposition: X ⊥ Y ∪ W | Z → X ⊥ Y | Z ∧ X ⊥ W | Z
    Purely structural: projects from union membership.  Holds identically
    for `dSepSet` and `dSepSetWalk`. -/
theorem dSepSet_decomp (G : ADMG V) (X Y W Z : Finset V) :
    G.dSepSet X (Y ∪ W) Z → G.dSepSet X Y Z ∧ G.dSepSet X W Z := by
  intro h
  exact ⟨fun x hx y hy => h x hx y (Finset.mem_union.mpr (.inl hy)),
         fun x hx w hw => h x hx w (Finset.mem_union.mpr (.inr hw))⟩

theorem dSepSetWalk_decomp (G : ADMG V) (X Y W Z : Finset V) :
    G.dSepSetWalk X (Y ∪ W) Z → G.dSepSetWalk X Y Z ∧ G.dSepSetWalk X W Z := by
  intro h
  exact ⟨fun x hx y hy => h x hx y (Finset.mem_union.mpr (.inl hy)),
         fun x hx w hw => h x hx w (Finset.mem_union.mpr (.inr hw))⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- §8. chainBuild and the Active Path Lemma (dSepWalk level)
-- ─────────────────────────────────────────────────────────────────────────────

/-- `v` itself, or a (directed-edge) descendant of `v`, lies in `S` — i.e.
    `v ∈ An(S)`.  This is the collider-opening condition. -/
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
lemma collider_seg_false_iff (G : ADMG V) (Z : Finset V) (c : V) (m1 m2 : Mark)
    (h : isCollider m1 m2 = true) :
    G.segmentBlocked Z c m1 m2 = false ↔ G.hasReflDescIn c Z := by
  unfold ADMG.segmentBlocked hasReflDescIn
  rw [if_pos h, Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]

/-- At a non-collider, the segment is unblocked exactly when the node avoids
    the conditioning set. -/
lemma noncollider_seg_false_iff (G : ADMG V) (Z : Finset V) (c : V) (m1 m2 : Mark)
    (h : isCollider m1 m2 = false) :
    G.segmentBlocked Z c m1 m2 = false ↔ c ∉ Z := by
  unfold ADMG.segmentBlocked
  rw [if_neg (by rw [h]; simp), decide_eq_false_iff_not]

/-- **chainBuild.** Given a descendant `w` of `q` (reachable within `n`
    directed steps) all of whose reachable nodes avoid `Z`, with `q ∉ Z` and
    `p` connected to `q` via a validated edge (mark `m0`), the directed chain
    `p, q, …, w` (all subsequent steps `dirFwd`) is an unblocked walk ending
    at `w`.  Every outgoing step uses `dirFwd`, which forces a non-collider
    at each interior node REGARDLESS of the incoming mark — this is where
    the mark-based design removes the need for bow-freeness. -/
lemma chainBuild (G : ADMG V) (Z : Finset V) :
    ∀ (n : ℕ) (q w p : V) (m0 : Mark),
      w ∈ G.directedPart.reachableN n q →
      (∀ u ∈ G.directedPart.reachableN n q, u ∉ Z) →
      Mark.valid G p q m0 = true →
      q ∉ Z →
      ∃ (rtV : List V) (rtM : List Mark), G.IsWalk (p :: q :: rtV) (m0 :: rtM) ∧
        (p :: q :: rtV).getLast? = some w ∧
        G.pathBlocked Z (p :: q :: rtV) (m0 :: rtM) = false := by
  intro n
  induction n with
  | zero => intro q w p m0 hw _ _ _; simp [DirectedGraph.reachableN] at hw
  | succ m ih =>
      intro q w p m0 hw hZ hpq hq
      rw [mem_reachableN_succ] at hw
      rcases hw with hwq | ⟨u, hu, hwu⟩
      · -- edge q → w directly; chain p, q, w
        have hqw : G.directed q w = true := (mem_outNeighbors G.directedPart q w).mp hwq
        refine ⟨[w], [Mark.dirFwd], ?_, ?_, ?_⟩
        · rw [isWalk_cons₂]
          refine ⟨hpq, ?_⟩
          rw [isWalk_cons₂]
          exact ⟨hqw, isWalk_singleton G w⟩
        · simp
        · show (G.segmentBlocked Z q m0 Mark.dirFwd || G.pathBlocked Z [q, w] [Mark.dirFwd]) = false
          rw [Bool.or_eq_false_iff]
          exact ⟨segmentBlocked_chain G Z q m0 hq, rfl⟩
      · -- edge q → u, then recurse from u to w
        have hqu : G.directed q u = true := (mem_outNeighbors G.directedPart q u).mp hu
        have huZ : u ∉ Z := hZ u (by rw [mem_reachableN_succ]; exact Or.inl hu)
        have hsub : G.directedPart.reachableN m u ⊆ G.directedPart.reachableN (m + 1) q := by
          intro x hx; rw [mem_reachableN_succ]; exact Or.inr ⟨u, hu, hx⟩
        obtain ⟨rtV, rtM, hwalk, hlast, hblk⟩ :=
          ih u w q Mark.dirFwd hwu (fun x hx => hZ x (hsub hx)) hqu huZ
        refine ⟨u :: rtV, Mark.dirFwd :: rtM, ?_, ?_, ?_⟩
        · rw [isWalk_cons₂]; exact ⟨hpq, hwalk⟩
        · rw [List.getLast?_cons_cons]; exact hlast
        · show (G.segmentBlocked Z q m0 Mark.dirFwd ||
              G.pathBlocked Z (q :: u :: rtV) (Mark.dirFwd :: rtM)) = false
          rw [Bool.or_eq_false_iff]
          exact ⟨segmentBlocked_chain G Z q m0 hq, hblk⟩

/-- **Active Path Lemma** (Verma & Pearl, adapted to a marked mixed graph).
    If there is an active walk from (the head of) `πV` to a node `y ∈ Y`
    given `Z ∪ W`, then there is an active walk with the SAME head to some
    node `b ∈ Y ∪ W` given `Z`.

    Scanning from the head, the gluing node is the first internal node `V_k`
    that is either (a) in `W`, or (b) a collider with a reflexive descendant
    in `W` but none in `Z`.  We recurse past every earlier internal node
    (active given `Z` too), and on reaching `V_k` we stop: case (a) truncates
    the walk there; case (b) glues on the directed chain to a `W`-descendant
    via `chainBuild`, turning `V_k` into a chain non-collider.  The extra
    "preserved prefix" conclusion is what lets the head be re-attached in the
    recursive step (it must fix not just the head vertex but also the second
    vertex and the mark between them, since the outer step needs to re-derive
    the collider status at the second vertex). -/
theorem active_path_lemma (G : ADMG V) (Y W Z : Finset V) :
    ∀ (πV : List V) (πM : List Mark) (y : V), G.IsWalk πV πM →
      πV.getLast? = some y → y ∈ Y → G.pathBlocked (Z ∪ W) πV πM = false →
      ∃ (π'V : List V) (π'M : List Mark) (b : V), G.IsWalk π'V π'M ∧
        π'V.getLast? = some b ∧ b ∈ Y ∪ W ∧
        G.pathBlocked Z π'V π'M = false ∧ π'V.head? = πV.head? ∧
        (∀ a c m t tm, πV = a :: c :: t → πM = m :: tm →
          ∃ t' tm', π'V = a :: c :: t' ∧ π'M = m :: tm') := by
  intro πV
  match πV with
  | [] =>
      intro πM y _ hl _ _; simp at hl
  | [v] =>
      intro πM y hw hl hy _
      cases πM with
      | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hl
        subst hl
        refine ⟨[v], [], v, isWalk_singleton G v, rfl,
          Finset.mem_union.mpr (Or.inl hy), rfl, rfl, ?_⟩
        intro a c m t tm h _; simp at h
      | cons _ _ => exact absurd hw (by simp [IsWalk])
  | [v, v2] =>
      intro πM y hw hl hy _
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      refine ⟨[v, v2], πM, v2, hw, rfl, Finset.mem_union.mpr (Or.inl hy), rfl, rfl, ?_⟩
      intro a c m t tm h hm; exact ⟨t, tm, h, hm⟩
  | v :: v2 :: v3 :: rest =>
      intro πM y hw hl hy hb
      cases πM with
      | nil => exact absurd hw (by simp [IsWalk])
      | cons m1 πM' =>
        cases πM' with
        | nil => exact absurd hw (by simp [IsWalk])
        | cons m2 πM'' =>
          rw [isWalk_cons₂] at hw
          obtain ⟨hadj, hwtail⟩ := hw
          have hb2 : (G.segmentBlocked (Z ∪ W) v2 m1 m2 ||
              G.pathBlocked (Z ∪ W) (v2 :: v3 :: rest) (m2 :: πM'')) = false := hb
          obtain ⟨hseg, htail⟩ := Bool.or_eq_false_iff.mp hb2
          rw [List.getLast?_cons_cons] at hl
          by_cases ha : v2 ∈ W
          · -- Case (a): V_k = v2 ∈ W; truncate to [v, v2].
            refine ⟨[v, v2], [m1], v2,
              (isWalk_cons₂ G v v2 m1 [] []).mpr ⟨hadj, isWalk_singleton G v2⟩, rfl,
              Finset.mem_union.mpr (Or.inr ha), rfl, rfl, ?_⟩
            intro a c m t tm h hm
            obtain ⟨rfl, hr⟩ := List.cons.inj h
            obtain ⟨rfl, _⟩ := List.cons.inj hr
            obtain ⟨rfl, _⟩ := List.cons.inj hm
            exact ⟨[], [], rfl, rfl⟩
          · by_cases hbcase :
              isCollider m1 m2 = true ∧ G.hasReflDescIn v2 W ∧ ¬ G.hasReflDescIn v2 Z
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
              obtain ⟨rtV, rtM, hwalk, hlast2, hblk2⟩ :=
                chainBuild G Z (Fintype.card V) v2 w v m1 hw_desc hallZ hadj hv2Z
              refine ⟨v :: v2 :: rtV, m1 :: rtM, w, hwalk, hlast2,
                Finset.mem_union.mpr (Or.inr hwW), hblk2, rfl, ?_⟩
              intro a c m t tm h hm
              obtain ⟨rfl, hr⟩ := List.cons.inj h
              obtain ⟨rfl, _⟩ := List.cons.inj hr
              obtain ⟨rfl, _⟩ := List.cons.inj hm
              exact ⟨rtV, rtM, rfl, rfl⟩
            · -- Neither (a) nor (b): v2 is active given Z; recurse on the tail.
              have hsegZ : G.segmentBlocked Z v2 m1 m2 = false := by
                by_cases hcoll : isCollider m1 m2 = true
                · rw [collider_seg_false_iff G Z v2 m1 m2 hcoll]
                  have hU : G.hasReflDescIn v2 (Z ∪ W) :=
                    (collider_seg_false_iff G (Z ∪ W) v2 m1 m2 hcoll).mp hseg
                  rw [hasReflDescIn_union] at hU
                  rcases hU with hUZ | hUW
                  · exact hUZ
                  · by_contra hnz; exact hbcase ⟨hcoll, hUW, hnz⟩
                · have hcf : isCollider m1 m2 = false := by simpa using hcoll
                  rw [noncollider_seg_false_iff G Z v2 m1 m2 hcf]
                  have hv2 : v2 ∉ Z ∪ W :=
                    (noncollider_seg_false_iff G (Z ∪ W) v2 m1 m2 hcf).mp hseg
                  exact fun h => hv2 (Finset.mem_union.mpr (Or.inl h))
              obtain ⟨π''V, π''M, b, hw'', hlast'', hb'', hblk'', hhead'', hpre''⟩ :=
                active_path_lemma G Y W Z (v2 :: v3 :: rest) (m2 :: πM'') y hwtail hl hy htail
              obtain ⟨t', tm', hπ''Veq, hπ''Meq⟩ := hpre'' v2 v3 m2 rest πM'' rfl rfl
              refine ⟨v :: π''V, m1 :: π''M, b, ?_, ?_, hb'', ?_, rfl, ?_⟩
              · rw [hπ''Veq, hπ''Meq, isWalk_cons₂]
                exact ⟨hadj, by rw [← hπ''Veq, ← hπ''Meq]; exact hw''⟩
              · rw [hπ''Veq, List.getLast?_cons_cons, ← hπ''Veq]; exact hlast''
              · rw [hπ''Veq, hπ''Meq]
                show (G.segmentBlocked Z v2 m1 m2 ||
                    G.pathBlocked Z (v2 :: v3 :: t') (m2 :: tm')) = false
                rw [Bool.or_eq_false_iff]
                refine ⟨hsegZ, ?_⟩
                rw [← hπ''Veq, ← hπ''Meq]
                exact hblk''
              · intro a c m t tm h hm
                obtain ⟨rfl, hr⟩ := List.cons.inj h
                obtain ⟨rfl, _⟩ := List.cons.inj hr
                obtain ⟨rfl, _⟩ := List.cons.inj hm
                exact ⟨v3 :: t', m2 :: tm', by rw [hπ''Veq], by rw [hπ''Meq]⟩
  termination_by πV => πV.length
  decreasing_by simp_wf

/-- **Contraction helper.**  Scanning an active walk given `Z` from the head:
    it is either still active given `Z ∪ Y`, or its first non-collider in
    `Y` cuts off a prefix that is an active walk from the same head to a
    node of `Y` given `Z`. -/
theorem contraction_walk (G : ADMG V) (Y Z : Finset V) :
    ∀ (πV : List V) (πM : List Mark), G.IsWalk πV πM → G.pathBlocked Z πV πM = false →
      G.pathBlocked (Z ∪ Y) πV πM = false ∨
      (∃ (π'V : List V) (π'M : List Mark) (y' : V), G.IsWalk π'V π'M ∧
        π'V.head? = πV.head? ∧ π'V.getLast? = some y' ∧ y' ∈ Y ∧
        G.pathBlocked Z π'V π'M = false ∧
        (∀ a c m t tm, πV = a :: c :: t → πM = m :: tm →
          ∃ t' tm', π'V = a :: c :: t' ∧ π'M = m :: tm') ∧
        π'V.length < πV.length) := by
  intro πV
  match πV with
  | [] => intro πM _ _; exact Or.inl rfl
  | [v] => intro πM _ _; exact Or.inl rfl
  | [v, v2] => intro πM _ _; exact Or.inl rfl
  | v :: v2 :: v3 :: rest =>
      intro πM hw hb
      cases πM with
      | nil => exact absurd hw (by simp [IsWalk])
      | cons m1 πM' =>
        cases πM' with
        | nil => exact absurd hw (by simp [IsWalk])
        | cons m2 πM'' =>
          rw [isWalk_cons₂] at hw
          obtain ⟨hadj, hwtail⟩ := hw
          have hb2 : (G.segmentBlocked Z v2 m1 m2 ||
              G.pathBlocked Z (v2 :: v3 :: rest) (m2 :: πM'')) = false := hb
          obtain ⟨hseg, htail⟩ := Bool.or_eq_false_iff.mp hb2
          by_cases hfound : v2 ∈ Y ∧ isCollider m1 m2 = false
          · -- First non-collider in Y: cut the prefix [v, v2].
            refine Or.inr ⟨[v, v2], [m1], v2,
              (isWalk_cons₂ G v v2 m1 [] []).mpr ⟨hadj, isWalk_singleton G v2⟩,
              rfl, rfl, hfound.1, rfl, ?_, ?_⟩
            · intro a c m t tm h hm
              obtain ⟨rfl, hr⟩ := List.cons.inj h
              obtain ⟨rfl, _⟩ := List.cons.inj hr
              obtain ⟨rfl, _⟩ := List.cons.inj hm
              exact ⟨[], [], rfl, rfl⟩
            · simp only [List.length_cons, List.length_nil]; omega
          · -- v2 remains unblocked under Z ∪ Y; recurse on the tail.
            have hsegZY : G.segmentBlocked (Z ∪ Y) v2 m1 m2 = false := by
              by_cases hcoll : isCollider m1 m2 = true
              · rw [collider_seg_false_iff G (Z ∪ Y) v2 m1 m2 hcoll, hasReflDescIn_union]
                exact Or.inl ((collider_seg_false_iff G Z v2 m1 m2 hcoll).mp hseg)
              · have hcf : isCollider m1 m2 = false := by simpa using hcoll
                rw [noncollider_seg_false_iff G (Z ∪ Y) v2 m1 m2 hcf]
                have hv2Z : v2 ∉ Z := (noncollider_seg_false_iff G Z v2 m1 m2 hcf).mp hseg
                have hv2Y : v2 ∉ Y := fun h => hfound ⟨h, hcf⟩
                exact fun h => (Finset.mem_union.mp h).elim hv2Z hv2Y
            rcases contraction_walk G Y Z (v2 :: v3 :: rest) (m2 :: πM'') hwtail htail with
              hZY | ⟨π''V, π''M, y', hw'', hhead'', hlast'', hyY, hblk'', hpre'', hlen''⟩
            · refine Or.inl ?_
              show (G.segmentBlocked (Z ∪ Y) v2 m1 m2 ||
                  G.pathBlocked (Z ∪ Y) (v2 :: v3 :: rest) (m2 :: πM'')) = false
              rw [Bool.or_eq_false_iff]; exact ⟨hsegZY, hZY⟩
            · obtain ⟨t', tm', hπ''Veq, hπ''Meq⟩ := hpre'' v2 v3 m2 rest πM'' rfl rfl
              refine Or.inr ⟨v :: π''V, m1 :: π''M, y', ?_, rfl, ?_, hyY, ?_, ?_, ?_⟩
              · rw [hπ''Veq, hπ''Meq, isWalk_cons₂]
                exact ⟨hadj, by rw [← hπ''Veq, ← hπ''Meq]; exact hw''⟩
              · rw [hπ''Veq, List.getLast?_cons_cons, ← hπ''Veq]; exact hlast''
              · rw [hπ''Veq, hπ''Meq]
                show (G.segmentBlocked Z v2 m1 m2 ||
                    G.pathBlocked Z (v2 :: v3 :: t') (m2 :: tm')) = false
                rw [Bool.or_eq_false_iff]
                refine ⟨hseg, ?_⟩
                rw [← hπ''Veq, ← hπ''Meq]
                exact hblk''
              · intro a c m t tm h hm
                obtain ⟨rfl, hr⟩ := List.cons.inj h
                obtain ⟨rfl, _⟩ := List.cons.inj hr
                obtain ⟨rfl, _⟩ := List.cons.inj hm
                exact ⟨v3 :: t', m2 :: tm', by rw [hπ''Veq], by rw [hπ''Meq]⟩
              · simp only [List.length_cons] at hlen'' ⊢; omega
  termination_by πV => πV.length
  decreasing_by simp_wf

/-- **Intersection helper.**  An active walk given `Z` ending in `Y ∪ W` can
    be re-routed (by alternately applying `contraction_walk` to `W` and to
    `Y`) into either an active walk to `Y` given `Z ∪ W`, or an active walk
    to `W` given `Z ∪ Y`, with the same head. -/
theorem intersection_walk (G : ADMG V) (Y W Z : Finset V) :
    ∀ (πV : List V) (πM : List Mark) (t : V), G.IsWalk πV πM →
      G.pathBlocked Z πV πM = false → πV.getLast? = some t → t ∈ Y ∪ W →
      (∃ (πaV : List V) (πaM : List Mark) (a : V), G.IsWalk πaV πaM ∧
          πaV.head? = πV.head? ∧ πaV.getLast? = some a ∧ a ∈ Y ∧
          G.pathBlocked (Z ∪ W) πaV πaM = false) ∨
      (∃ (πbV : List V) (πbM : List Mark) (b : V), G.IsWalk πbV πbM ∧
          πbV.head? = πV.head? ∧ πbV.getLast? = some b ∧ b ∈ W ∧
          G.pathBlocked (Z ∪ Y) πbV πbM = false) := by
  intro πV πM t hwalk hactive hlast htYW
  rcases Finset.mem_union.mp htYW with hY | hW
  · rcases contraction_walk G W Z πV πM hwalk hactive with
      hZW | ⟨π'V, π'M, w', hw', hhead', hlast', hw'W, hblk', _, hlen'⟩
    · exact Or.inl ⟨πV, πM, t, hwalk, rfl, hlast, hY, hZW⟩
    · rcases intersection_walk G Y W Z π'V π'M w' hw' hblk' hlast'
          (Finset.mem_union.mpr (Or.inr hw'W)) with
        ⟨πaV, πaM, a, hwa, hha, hla, haY, hba⟩ | ⟨πbV, πbM, b, hwb, hhb, hlb, hbW, hbb⟩
      · exact Or.inl ⟨πaV, πaM, a, hwa, hha.trans hhead', hla, haY, hba⟩
      · exact Or.inr ⟨πbV, πbM, b, hwb, hhb.trans hhead', hlb, hbW, hbb⟩
  · rcases contraction_walk G Y Z πV πM hwalk hactive with
      hZY | ⟨π'V, π'M, y', hw', hhead', hlast', hy'Y, hblk', _, hlen'⟩
    · exact Or.inr ⟨πV, πM, t, hwalk, rfl, hlast, hW, hZY⟩
    · rcases intersection_walk G Y W Z π'V π'M y' hw' hblk' hlast'
          (Finset.mem_union.mpr (Or.inl hy'Y)) with
        ⟨πaV, πaM, a, hwa, hha, hla, haY, hba⟩ | ⟨πbV, πbM, b, hwb, hhb, hlb, hbW, hbb⟩
      · exact Or.inl ⟨πaV, πaM, a, hwa, hha.trans hhead', hla, haY, hba⟩
      · exact Or.inr ⟨πbV, πbM, b, hwb, hhb.trans hhead', hlb, hbW, hbb⟩
  termination_by πV => πV.length
  decreasing_by all_goals omega

-- ─────────────────────────────────────────────────────────────────────────────
-- §9. Weak Union, Contraction, Intersection (dSepSetWalk level)
-- ─────────────────────────────────────────────────────────────────────────────

private lemma weak_union_half (G : ADMG V) (X Y W Z : Finset V)
    (h : G.dSepSetWalk X (Y ∪ W) Z) : G.dSepSetWalk X Y (Z ∪ W) := by
  intro x hx y hy πV πM hwalk hhead hlast
  by_contra hne
  rw [Bool.not_eq_true] at hne
  obtain ⟨π'V, π'M, b, hw', hlast', hb', hblk', hhead', _⟩ :=
    active_path_lemma G Y W Z πV πM y hwalk hlast hy hne
  have hxb : G.dSepWalk x b Z := h x hx b hb'
  have hcontra : G.pathBlocked Z π'V π'M = true := hxb π'V π'M hw' (by rw [hhead', hhead]) hlast'
  rw [hblk'] at hcontra
  exact absurd hcontra (by simp)

/-- **Weak Union** for `dSepWalk`: X ⊥ Y ∪ W | Z → X ⊥ Y | Z ∪ W ∧ X ⊥ W | Z ∪ Y. -/
theorem dSepSetWalk_weak_union (G : ADMG V) (X Y W Z : Finset V) :
    G.dSepSetWalk X (Y ∪ W) Z →
    G.dSepSetWalk X Y (Z ∪ W) ∧ G.dSepSetWalk X W (Z ∪ Y) := by
  intro h
  refine ⟨weak_union_half G X Y W Z h, ?_⟩
  have h' : G.dSepSetWalk X (W ∪ Y) Z := by rw [Finset.union_comm]; exact h
  exact weak_union_half G X W Y Z h'

/-- **Contraction** for `dSepWalk`: X ⊥ Y | Z ∧ X ⊥ W | Z ∪ Y → X ⊥ Y ∪ W | Z. -/
theorem dSepSetWalk_contraction (G : ADMG V) (X Y W Z : Finset V) :
    G.dSepSetWalk X Y Z → G.dSepSetWalk X W (Z ∪ Y) → G.dSepSetWalk X (Y ∪ W) Z := by
  intro h1 h2 x hx yw hyw
  rcases Finset.mem_union.mp hyw with hy | hw
  · exact h1 x hx yw hy
  · intro πV πM hwalk hhead hlast
    by_contra hne
    rw [Bool.not_eq_true] at hne
    rcases contraction_walk G Y Z πV πM hwalk hne with
      hZY | ⟨π'V, π'M, y', hw', hhead', hlast', hyY, hblk', _, _⟩
    · have hc : G.pathBlocked (Z ∪ Y) πV πM = true := h2 x hx yw hw πV πM hwalk hhead hlast
      rw [hZY] at hc; exact absurd hc (by simp)
    · have hc : G.pathBlocked Z π'V π'M = true :=
        h1 x hx y' hyY π'V π'M hw' (by rw [hhead', hhead]) hlast'
      rw [hblk'] at hc; exact absurd hc (by simp)

/-- `dSepWalk` satisfies all four semi-graphoid axioms. -/
theorem dSepWalk_semigraphoid (G : ADMG V) :
    (∀ X Y Z : Finset V, G.dSepSetWalk X Y Z ↔ G.dSepSetWalk Y X Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSetWalk X (Y ∪ W) Z → G.dSepSetWalk X Y Z ∧ G.dSepSetWalk X W Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSetWalk X (Y ∪ W) Z →
        G.dSepSetWalk X Y (Z ∪ W) ∧ G.dSepSetWalk X W (Z ∪ Y)) ∧
    (∀ X Y W Z : Finset V, G.dSepSetWalk X Y Z → G.dSepSetWalk X W (Z ∪ Y) →
        G.dSepSetWalk X (Y ∪ W) Z) :=
  ⟨fun X Y Z     => dSepSetWalk_symm G X Y Z,
   fun X Y W Z h => dSepSetWalk_decomp G X Y W Z h,
   fun X Y W Z h => dSepSetWalk_weak_union G X Y W Z h,
   fun X Y W Z h1 h2 => dSepSetWalk_contraction G X Y W Z h1 h2⟩

/-- **Intersection** for `dSepWalk`: X ⊥ Y | Z ∪ W ∧ X ⊥ W | Z ∪ Y → X ⊥ Y ∪ W | Z. -/
theorem dSepSetWalk_intersection (G : ADMG V) (X Y W Z : Finset V) :
    G.dSepSetWalk X Y (Z ∪ W) → G.dSepSetWalk X W (Z ∪ Y) → G.dSepSetWalk X (Y ∪ W) Z := by
  intro h1 h2 x hx yw hyw πV πM hwalk hhead hlast
  by_contra hne
  rw [Bool.not_eq_true] at hne
  rcases intersection_walk G Y W Z πV πM yw hwalk hne hlast hyw with
    ⟨πaV, πaM, a, hwa, hheada, hlasta, haY, hblka⟩ | ⟨πbV, πbM, b, hwb, hheadb, hlastb, hbW, hblkb⟩
  · have hc : G.pathBlocked (Z ∪ W) πaV πaM = true :=
      h1 x hx a haY πaV πaM hwa (by rw [hheada, hhead]) hlasta
    rw [hblka] at hc; exact absurd hc (by simp)
  · have hc : G.pathBlocked (Z ∪ Y) πbV πbM = true :=
      h2 x hx b hbW πbV πbM hwb (by rw [hheadb, hhead]) hlastb
    rw [hblkb] at hc; exact absurd hc (by simp)

end ADMG

-- ─────────────────────────────────────────────────────────────────────────────
-- §10. Correspondence with DAG.lean
-- ─────────────────────────────────────────────────────────────────────────────

-- A DAG, viewed as an ADMG with no bidirected edges, has NO bows, so its
-- walks admit a UNIQUE mark assignment (`toADMGMarks`), and under that
-- assignment `dSepWalk` on the embedding is exactly DAG.lean's own
-- (walk-quantified) `dSep`.

namespace DAG

/-- View a DAG as an ADMG with no bidirected edges. -/
def toADMG (D : DAG V) : ADMG V where
  directed    := D.graph.adj
  bidirected  := fun _ _ => false
  dir_no_loop := D.graph.no_self_loop
  bid_no_loop := fun _ => rfl
  bid_symm    := fun _ _ => rfl
  dir_acyclic := D.acyclic

/-- The canonical mark for a DAG edge: forward if the edge points that way,
    backward otherwise.  Since `toADMG` has no bidirected edges and
    acyclicity forbids both `hasEdge a b` and `hasEdge b a`, this is the
    ONLY mark that validates an actual DAG edge between `a` and `b`. -/
def toADMGMark (D : DAG V) (a b : V) : Mark :=
  if D.hasEdge a b then Mark.dirFwd else Mark.dirBack

/-- The canonical marks for a DAG walk. -/
def toADMGMarks (D : DAG V) : List V → List Mark
  | [] => []
  | [_] => []
  | a :: b :: l => D.toADMGMark a b :: D.toADMGMarks (b :: l)

lemma toADMGMark_valid (D : DAG V) {a b : V} (h : D.Adj a b) :
    Mark.valid D.toADMG a b (D.toADMGMark a b) = true := by
  unfold toADMGMark Mark.valid
  rcases h with h | h
  · rw [if_pos h]; exact h
  · by_cases hab : D.hasEdge a b
    · rw [if_pos hab]; exact hab
    · rw [if_neg hab]; exact h

lemma toADMG_isWalk (D : DAG V) : ∀ l : List V, D.IsWalk l →
    D.toADMG.IsWalk l (D.toADMGMarks l)
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, h => by
      rw [DAG.isWalk_cons₂] at h
      exact ⟨toADMGMark_valid D h.1, toADMG_isWalk D (b :: l) h.2⟩

/-- On a bow-free graph (like `toADMG`), the marks of a walk over given
    vertices are forced — there is only one valid choice at each step. -/
lemma toADMG_marks_unique (D : DAG V) :
    ∀ (verts : List V) (marks : List Mark), D.toADMG.IsWalk verts marks →
      marks = D.toADMGMarks verts := by
  intro verts
  induction verts with
  | nil => intro marks h; cases marks with
      | nil => rfl
      | cons m ms => exact absurd h (by simp [ADMG.IsWalk])
  | cons a vs ih =>
    intro marks h
    cases vs with
    | nil => cases marks with
        | nil => rfl
        | cons m ms => exact absurd h (by simp [ADMG.IsWalk])
    | cons b vs' =>
      cases marks with
      | nil => exact absurd h (by simp [ADMG.IsWalk])
      | cons m ms =>
        obtain ⟨hvalid, htail⟩ := h
        have hm : m = D.toADMGMark a b := by
          unfold toADMGMark
          cases m with
          | dirFwd =>
            have hab : D.hasEdge a b := hvalid
            rw [if_pos hab]
          | dirBack =>
            have hba : D.hasEdge b a := hvalid
            have hab : ¬ D.hasEdge a b := fun h => by
              have := D.no_2cycle h; rw [this] at hba; exact absurd hba (by simp)
            rw [if_neg hab]
          | bidir => simp [Mark.valid, toADMG] at hvalid
        show m :: ms = D.toADMGMark a b :: D.toADMGMarks (b :: vs')
        rw [hm, ih ms htail]

private lemma toADMGMark_intoRight (D : DAG V) (a b : V) :
    (D.toADMGMark a b).intoRight = D.hasEdge a b := by
  unfold toADMGMark
  by_cases h : D.hasEdge a b
  · rw [if_pos h, h]; rfl
  · rw [if_neg h]
    have hf : D.hasEdge a b = false := by simpa using h
    rw [hf]; rfl

-- Needs `Adj b c`: without SOME edge between b,c, `toADMGMark` defaults to
-- `dirBack`, which would not match `hasEdge c b = false` in the vacuous case.
private lemma toADMGMark_intoLeft (D : DAG V) {b c : V} (hbc : D.Adj b c) :
    (D.toADMGMark b c).intoLeft = D.hasEdge c b := by
  unfold toADMGMark
  by_cases h : D.hasEdge b c
  · rw [if_pos h, D.no_2cycle h]; rfl
  · rw [if_neg h]
    have hcb : D.hasEdge c b = true := by
      rcases hbc with h' | h'
      · exact absurd h' h
      · exact h'
    rw [hcb]; rfl

lemma toADMG_isCollider (D : DAG V) {a b c : V} (hbc : D.Adj b c) :
    CausalLib.isCollider (D.toADMGMark a b) (D.toADMGMark b c) = D.isCollider a b c := by
  unfold CausalLib.isCollider DAG.isCollider
  rw [toADMGMark_intoRight, toADMGMark_intoLeft D hbc]

lemma toADMG_descendants (D : DAG V) (v : V) :
    D.toADMG.descendants v = D.descendants v := rfl

lemma toADMG_segmentBlocked (D : DAG V) (Z : Finset V) {a b c : V} (hbc : D.Adj b c) :
    D.toADMG.segmentBlocked Z b (D.toADMGMark a b) (D.toADMGMark b c) = D.segmentBlocked Z a b c := by
  simp only [ADMG.segmentBlocked, DAG.segmentBlocked, toADMG_isCollider D hbc, toADMG_descendants]
  rfl

lemma toADMG_pathBlocked (D : DAG V) (Z : Finset V) :
    ∀ l : List V, D.IsWalk l → D.toADMG.pathBlocked Z l (D.toADMGMarks l) = D.pathBlocked Z l
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | a :: b :: c :: rest, hw => by
      rw [DAG.isWalk_cons₂] at hw
      obtain ⟨_, hw2⟩ := hw
      have hw2' := hw2
      rw [DAG.isWalk_cons₂] at hw2'
      obtain ⟨hbc, _⟩ := hw2'
      show (D.toADMG.segmentBlocked Z b (D.toADMGMark a b) (D.toADMGMark b c) ||
          D.toADMG.pathBlocked Z (b :: c :: rest) (D.toADMGMarks (b :: c :: rest)))
        = (D.segmentBlocked Z a b c || D.pathBlocked Z (b :: c :: rest))
      rw [toADMG_segmentBlocked D Z hbc, toADMG_pathBlocked D Z (b :: c :: rest) hw2]

/-- Recover an ordinary DAG walk from an ADMG walk over the (bidirected-edge-
    free) embedding: every mark must be `dirFwd` or `dirBack`, both of which
    give a genuine DAG edge. -/
lemma toADMG_isWalk_recover (D : DAG V) :
    ∀ (verts : List V) (marks : List Mark), D.toADMG.IsWalk verts marks → D.IsWalk verts := by
  intro verts
  induction verts with
  | nil => intro _ _; exact D.isWalk_nil
  | cons a vs ih =>
    intro marks h
    cases vs with
    | nil => exact D.isWalk_singleton a
    | cons b vs' =>
      cases marks with
      | nil => exact absurd h (by simp [ADMG.IsWalk])
      | cons m ms =>
        obtain ⟨hvalid, htail⟩ := h
        rw [DAG.isWalk_cons₂]
        refine ⟨?_, ih ms htail⟩
        unfold Mark.valid at hvalid
        cases m with
        | dirFwd => exact Or.inl hvalid
        | dirBack => exact Or.inr hvalid
        | bidir => simp [toADMG] at hvalid

/-- **`dSepWalk` on a bidirected-edge-free ADMG is exactly DAG.lean's own
    (walk-quantified) `dSep`.**  Bow-freeness is automatic here (no
    bidirected edges at all), which is why the correspondence is with
    `dSepWalk` — the walk-quantified relation — and not with the
    simple-path-quantified `dSep` (for which no such general correspondence
    with DAG.lean's walk-based `dSep` is claimed). -/
theorem toADMG_dSepWalk_iff (D : DAG V) (X Y : V) (Z : Finset V) :
    D.toADMG.dSepWalk X Y Z ↔ D.dSep X Y Z := by
  constructor
  · intro h path hwalk hhead hlast
    rw [← toADMG_pathBlocked D Z path hwalk]
    exact h path (D.toADMGMarks path) (toADMG_isWalk D path hwalk) hhead hlast
  · intro h verts marks hwalk hhead hlast
    have hdwalk : D.IsWalk verts := toADMG_isWalk_recover D verts marks hwalk
    rw [toADMG_marks_unique D verts marks hwalk, toADMG_pathBlocked D Z verts hdwalk]
    exact h verts hdwalk hhead hlast

end DAG
end CausalLib

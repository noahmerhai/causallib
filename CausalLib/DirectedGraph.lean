-- General finite directed graphs and bounded reachability.

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.ByContra

namespace CausalLib

/-- A finite directed graph. Self-loops are forbidden; longer cycles are allowed. -/
structure DirectedGraph (V : Type*) [Fintype V] [DecidableEq V] where
  /-- `adj u v = true` means there is a directed edge `u → v`. -/
  adj : V → V → Bool
  /-- No vertex has an edge to itself. -/
  no_self_loop : ∀ v : V, adj v v = false

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace DirectedGraph

-- ─────────────────────────────────────────────────────────────────────────────
-- Directed graph queries
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
-- Directed reachability (depth-bounded, computable)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Nodes reachable from `v` by one to `n` directed edges. -/
def reachableN (G : DirectedGraph V) : ℕ → V → Finset V
  | 0, _ => ∅
  | n + 1, v => G.outNeighbors v ∪ (G.outNeighbors v).biUnion (fun u => G.reachableN n u)

/-- Nodes reachable by following one or more directed edges, bounded by the vertex count.
    The bound includes cycles returning to the starting vertex. -/
def reachable (G : DirectedGraph V) (v : V) : Finset V :=
  G.reachableN (Fintype.card V) v

/-- Can we reach u from v? -/
def canReach (G : DirectedGraph V) (v u : V) : Bool :=
  u ∈ G.reachable v

lemma mem_outNeighbors_iff (H : DirectedGraph V) (v u : V) :
    u ∈ H.outNeighbors v ↔ H.adj v u = true := by
  simp [outNeighbors]

lemma mem_reachableN_succ_iff (H : DirectedGraph V) (n : ℕ) (v w : V) :
    w ∈ H.reachableN (n + 1) v ↔
      w ∈ H.outNeighbors v ∨ ∃ u ∈ H.outNeighbors v, w ∈ H.reachableN n u := by
  simp only [reachableN, Finset.mem_union, Finset.mem_biUnion]

@[simp] lemma reachableN_zero (H : DirectedGraph V) (v : V) :
    H.reachableN 0 v = ∅ := rfl

lemma reachableN_one (H : DirectedGraph V) (v : V) :
    H.reachableN 1 v = H.outNeighbors v := by
  ext w
  rw [mem_reachableN_succ_iff]
  simp

lemma reachableN_subset_succ (H : DirectedGraph V) (n : ℕ) (v : V) :
    H.reachableN n v ⊆ H.reachableN (n + 1) v := by
  induction n generalizing v with
  | zero => simp
  | succ m ih =>
      intro w hw
      rw [mem_reachableN_succ_iff] at hw ⊢
      rcases hw with h | ⟨u, hu, hwu⟩
      · exact Or.inl h
      · exact Or.inr ⟨u, hu, ih u hwu⟩

lemma reachableN_mono (H : DirectedGraph V) {n m : ℕ} (h : n ≤ m) (v : V) :
    H.reachableN n v ⊆ H.reachableN m v := by
  induction h with
  | refl => exact fun _ hx => hx
  | step _ ih => exact fun x hx => reachableN_subset_succ H _ v (ih hx)

/-- One more edge stays within one more step of reachability. -/
lemma reachableN_step (H : DirectedGraph V) :
    ∀ (n : ℕ) (v w u : V), w ∈ H.reachableN n v → u ∈ H.outNeighbors w →
      u ∈ H.reachableN (n + 1) v := by
  intro n
  induction n with
  | zero => intro v w u hw _; simp at hw
  | succ m ih =>
      intro v w u hw hu
      rw [mem_reachableN_succ_iff] at hw
      rw [mem_reachableN_succ_iff]
      rcases hw with hwv | ⟨x, hx, hwx⟩
      · refine Or.inr ⟨w, hwv, ?_⟩
        have h1 : u ∈ H.reachableN 1 w := by rw [reachableN_one]; exact hu
        exact reachableN_mono H (by omega) w h1
      · exact Or.inr ⟨x, hx, ih x w u hwx hu⟩

/-- Reachability composes (with the step bounds adding). -/
lemma reachableN_trans (H : DirectedGraph V) :
    ∀ (m n : ℕ) (a b c : V), b ∈ H.reachableN n a → c ∈ H.reachableN m b →
      c ∈ H.reachableN (n + m) a := by
  intro m
  induction m with
  | zero => intro n a b c _ hc; simp at hc
  | succ k ih =>
      intro n a b c hb hc
      rw [mem_reachableN_succ_iff] at hc
      rcases hc with hcb | ⟨x, hx, hcx⟩
      · exact reachableN_mono H (by omega) a (reachableN_step H n a b c hb hcb)
      · have hx' : x ∈ H.reachableN (n + 1) a := reachableN_step H n a b x hb hx
        exact reachableN_mono H (by omega) a (ih (n + 1) a x c hx' hcx)

/-- The "outward" recursion: one more step from the FRONTIER, rather than from
    the source.  This is the form that makes stabilisation propagate. -/
lemma reachableN_alt (H : DirectedGraph V) (n : ℕ) (hn : 1 ≤ n) (v : V) :
    H.reachableN (n + 1) v
      = H.reachableN n v ∪ (H.reachableN n v).biUnion H.outNeighbors := by
  induction n, hn using Nat.le_induction generalizing v with
  | base =>
      ext w
      rw [mem_reachableN_succ_iff]
      simp only [reachableN_one, Finset.mem_union, Finset.mem_biUnion]
  | succ k hk ih =>
      ext w
      constructor
      · intro hw
        rw [mem_reachableN_succ_iff] at hw
        rw [Finset.mem_union, Finset.mem_biUnion]
        rcases hw with hwv | ⟨x, hx, hwx⟩
        · left
          have h1 : w ∈ H.reachableN 1 v := by rw [reachableN_one]; exact hwv
          exact reachableN_mono H (by omega) v h1
        · rw [ih x, Finset.mem_union, Finset.mem_biUnion] at hwx
          rcases hwx with hin | ⟨u, hu, hwu⟩
          · left
            rw [mem_reachableN_succ_iff]
            exact Or.inr ⟨x, hx, hin⟩
          · right
            refine ⟨u, ?_, hwu⟩
            rw [mem_reachableN_succ_iff]
            exact Or.inr ⟨x, hx, hu⟩
      · intro hw
        rw [Finset.mem_union, Finset.mem_biUnion] at hw
        rcases hw with hin | ⟨u, hu, hwu⟩
        · exact reachableN_subset_succ H _ v hin
        · exact reachableN_step H _ v u w hu hwu

/-- Once the frontier stops growing it never grows again. -/
lemma reachableN_stable (H : DirectedGraph V) (v : V) (n : ℕ) (hn : 1 ≤ n)
    (h : H.reachableN (n + 1) v = H.reachableN n v) :
    ∀ k, H.reachableN (n + k) v = H.reachableN n v := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
      have hj : 1 ≤ n + j := by omega
      have e1 : H.reachableN (n + j + 1) v
          = H.reachableN (n + j) v ∪ (H.reachableN (n + j) v).biUnion H.outNeighbors :=
        reachableN_alt H (n + j) hj v
      have e2 : H.reachableN (n + 1) v
          = H.reachableN n v ∪ (H.reachableN n v).biUnion H.outNeighbors :=
        reachableN_alt H n hn v
      show H.reachableN (n + j + 1) v = H.reachableN n v
      rw [e1, ih, ← e2, h]

/-- If the out-neighbourhood is empty nothing is reachable at any depth. -/
private lemma reachableN_of_out_empty (H : DirectedGraph V) (v : V)
    (h : H.outNeighbors v = ∅) : ∀ n, H.reachableN n v = ∅ := by
  intro n
  cases n with
  | zero => rfl
  | succ m =>
      ext w
      rw [mem_reachableN_succ_iff]
      simp [h]

/-- **Saturation.**  `Fintype.card V` steps already reach everything that any
    number of steps reaches.  (Pigeonhole: the frontier is nondecreasing and
    bounded by `card V`, so it must stall at or before step `card V`.) -/
lemma reachableN_subset_card (H : DirectedGraph V) (v : V) :
    ∀ m, H.reachableN m v ⊆ H.reachableN (Fintype.card V) v := by
  have hstall : ∃ n, n ≤ Fintype.card V ∧ H.reachableN (n + 1) v = H.reachableN n v := by
    by_contra hcon
    have hcon' : ∀ n, n ≤ Fintype.card V → H.reachableN (n + 1) v ≠ H.reachableN n v := by
      intro n hn he; exact hcon ⟨n, hn, he⟩
    have hgrow : ∀ n, n ≤ Fintype.card V → n ≤ (H.reachableN n v).card := by
      intro n
      induction n with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
          intro hk
          have hk' : k ≤ Fintype.card V := by omega
          have hss : H.reachableN k v ⊂ H.reachableN (k + 1) v :=
            Finset.ssubset_iff_subset_ne.mpr
              ⟨reachableN_subset_succ H k v, Ne.symm (hcon' k hk')⟩
          have h1 := Finset.card_lt_card hss
          have h2 := ih hk'
          omega
    have h1 : Fintype.card V ≤ (H.reachableN (Fintype.card V) v).card := hgrow _ le_rfl
    have h2 : (H.reachableN (Fintype.card V) v).card ≤ Fintype.card V :=
      Finset.card_le_univ _
    have huniv : H.reachableN (Fintype.card V) v = Finset.univ := by
      apply Finset.eq_univ_of_card
      omega
    refine hcon' (Fintype.card V) le_rfl ?_
    apply Finset.Subset.antisymm
    · rw [huniv]; exact Finset.subset_univ _
    · exact reachableN_subset_succ H _ v
  obtain ⟨n, hnN, hn⟩ := hstall
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    have hout : H.outNeighbors v = ∅ := by
      have h1 : H.reachableN 1 v = H.reachableN 0 v := hn
      rw [reachableN_one, reachableN_zero] at h1
      exact h1
    intro m
    rw [reachableN_of_out_empty H v hout m]
    exact Finset.empty_subset _
  · intro m
    by_cases hm : m ≤ Fintype.card V
    · exact reachableN_mono H hm v
    · have e1 : H.reachableN m v = H.reachableN n v := by
        have hs := reachableN_stable H v n hn1 hn (m - n)
        rwa [show n + (m - n) = m from by omega] at hs
      have e2 : H.reachableN (Fintype.card V) v = H.reachableN n v := by
        have hs := reachableN_stable H v n hn1 hn (Fintype.card V - n)
        rwa [show n + (Fintype.card V - n) = Fintype.card V from by omega] at hs
      rw [e1, e2]

end DirectedGraph
end CausalLib

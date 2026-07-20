-- ─────────────────────────────────────────────────────────────────────────────
-- WalkToPath.lean
-- Closing the walk-to-path gap for ADMG separation.
--
-- `ADMG.dSep` quantifies over genuine SIMPLE PATHS (Nodup); `ADMG.dSepWalk`
-- quantifies over walks.  `dSepWalk → dSep` is free.  This file proves the
-- converse, `dSep → dSepWalk`, by a minimal-witness argument: an active walk
-- of minimum length has no repeated vertex, because a repetition can be
-- EXCISED while keeping the walk active.
--
-- The excision is the crux.  Cutting `A ++ v :: B ++ v :: C` down to
-- `A ++ v :: C` leaves every surviving triple's inputs untouched (collider
-- opening is the GRAPH-LEVEL descendant test, independent of which vertices
-- the walk visits), so only the new seam triple at `v` needs an argument.
--
-- That argument needs transitivity of `descendants`, which is NOT immediate
-- from the depth-bounded `reachableN (Fintype.card V)` definition: it needs
-- the bound to be saturating.  §1 establishes that by a pigeonhole argument.
-- ─────────────────────────────────────────────────────────────────────────────

import CausalLib.ADMG

namespace CausalLib

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ─────────────────────────────────────────────────────────────────────────────
-- §1. Reachability: the depth bound `Fintype.card V` saturates
-- ─────────────────────────────────────────────────────────────────────────────

namespace DirectedGraph

lemma mem_outNeighbors_iff (H : DirectedGraph V) (v u : V) :
    u ∈ H.outNeighbors v ↔ H.adj v u = true := by
  simp [DirectedGraph.outNeighbors]

lemma mem_reachableN_succ_iff (H : DirectedGraph V) (n : ℕ) (v w : V) :
    w ∈ H.reachableN (n + 1) v ↔
      w ∈ H.outNeighbors v ∨ ∃ u ∈ H.outNeighbors v, w ∈ H.reachableN n u := by
  simp only [DirectedGraph.reachableN, Finset.mem_union, Finset.mem_biUnion]

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

namespace ADMG

/-- **Transitivity of `descendants`.**  Needs saturation of the depth bound. -/
lemma descendants_trans (G : ADMG V) {a b c : V}
    (hab : b ∈ G.descendants a) (hbc : c ∈ G.descendants b) :
    c ∈ G.descendants a := by
  have h := DirectedGraph.reachableN_trans G.directedPart
    (Fintype.card V) (Fintype.card V) a b c hab hbc
  exact DirectedGraph.reachableN_subset_card G.directedPart a _ h

/-- Being an ancestor of `Z` is inherited upstream along `descendants`. -/
lemma hasReflDescIn_of_descendant (G : ADMG V) {u w : V} {Z : Finset V}
    (hw : w ∈ G.descendants u) (h : G.hasReflDescIn w Z) :
    G.hasReflDescIn u Z := by
  rcases h with hwZ | ⟨z, hz⟩
  · exact Or.inr ⟨w, Finset.mem_inter.mpr ⟨hw, hwZ⟩⟩
  · rw [Finset.mem_inter] at hz
    exact Or.inr ⟨z, Finset.mem_inter.mpr ⟨descendants_trans G hw hz.1, hz.2⟩⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- §2. Structural lemmas for `IsWalk` and `pathBlocked`
-- ─────────────────────────────────────────────────────────────────────────────

/-- One-step unfolding of `pathBlocked` with the segment's CENTRE vertex `b`
    exposed, valid for an arbitrary lock-step tail. -/
lemma pathBlocked_cons2 (G : ADMG V) (Z : Finset V) (a b : V) (L : List V)
    (m1 : Mark) (M : List Mark) (hlen : M.length = L.length) :
    G.pathBlocked Z (a :: b :: L) (m1 :: M)
      = ((M.head?.elim false (fun m2 => G.segmentBlocked Z b m1 m2))
          || G.pathBlocked Z (b :: L) M) := by
  cases L with
  | nil => cases M with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons c L' => cases M with
    | nil => simp at hlen
    | cons m2 M' => rfl

lemma isWalk_tail (G : ADMG V) {a : V} {L : List V} {m : Mark} {M : List Mark}
    (h : G.IsWalk (a :: L) (m :: M)) : G.IsWalk L M := by
  cases L with
  | nil => exact absurd h (by simp [IsWalk])
  | cons b vs => exact h.2

lemma pathBlocked_tail (G : ADMG V) (Z : Finset V) {a : V} {L : List V}
    {m : Mark} {M : List Mark} (hlen : M.length + 1 = L.length)
    (h : G.pathBlocked Z (a :: L) (m :: M) = false) : G.pathBlocked Z L M = false := by
  cases L with
  | nil => simp at hlen
  | cons b L' =>
      have hlen' : M.length = L'.length := by simpa using hlen
      rw [pathBlocked_cons2 G Z a b L' m M hlen', Bool.or_eq_false_iff] at h
      exact h.2

/-- A walk restricted to a suffix is still a walk. -/
lemma isWalk_suffix (G : ADMG V) :
    ∀ (P : List V) (MP : List Mark), MP.length = P.length →
      ∀ (S : List V) (MS : List Mark),
        G.IsWalk (P ++ S) (MP ++ MS) → G.IsWalk S MS := by
  intro P
  induction P with
  | nil =>
      intro MP hlen S MS h
      have hMP : MP = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst hMP; simpa using h
  | cons p P' ih =>
      intro MP hlen S MS h
      cases MP with
      | nil => simp at hlen
      | cons mp MP' =>
          have hlen' : MP'.length = P'.length := by simpa using hlen
          rw [List.cons_append, List.cons_append] at h
          exact ih MP' hlen' S MS (isWalk_tail G h)

/-- Blocking of a suffix follows from blocking of the whole. -/
lemma pathBlocked_suffix (G : ADMG V) (Z : Finset V) :
    ∀ (P : List V) (MP : List Mark), MP.length = P.length →
      ∀ (S : List V) (MS : List Mark), MS.length + 1 = S.length →
        G.pathBlocked Z (P ++ S) (MP ++ MS) = false → G.pathBlocked Z S MS = false := by
  intro P
  induction P with
  | nil =>
      intro MP hlen S MS _ h
      have hMP : MP = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst hMP; simpa using h
  | cons p P' ih =>
      intro MP hlen S MS hS h
      cases MP with
      | nil => simp at hlen
      | cons mp MP' =>
          have hlen' : MP'.length = P'.length := by simpa using hlen
          rw [List.cons_append, List.cons_append] at h
          have hcat : (MP' ++ MS).length + 1 = (P' ++ S).length := by
            simp only [List.length_append]; omega
          exact ih MP' hlen' S MS hS (pathBlocked_tail G Z hcat h)

/-- A walk truncated just after a chosen vertex is still a walk. -/
lemma isWalk_take (G : ADMG V) :
    ∀ (P : List V) (MP : List Mark), MP.length = P.length →
      ∀ (x : V) (S : List V) (MS : List Mark),
        G.IsWalk (P ++ x :: S) (MP ++ MS) → G.IsWalk (P ++ [x]) MP := by
  intro P
  induction P with
  | nil =>
      intro MP hlen x S MS _
      have hMP : MP = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst hMP; exact isWalk_singleton G x
  | cons p P' ih =>
      intro MP hlen x S MS h
      cases MP with
      | nil => simp at hlen
      | cons mp MP' =>
          have hlen' : MP'.length = P'.length := by simpa using hlen
          rw [List.cons_append, List.cons_append] at h
          cases P' with
          | nil =>
              have hMP' : MP' = [] := List.length_eq_zero_iff.mp (by simpa using hlen')
              subst hMP'
              exact ⟨h.1, isWalk_singleton G x⟩
          | cons p' P'' =>
              refine ⟨h.1, ?_⟩
              have := ih MP' hlen' x S MS h.2
              exact this

/-- Blocking of a truncation follows from blocking of the whole. -/
lemma pathBlocked_take (G : ADMG V) (Z : Finset V) :
    ∀ (P : List V) (MP : List Mark), MP.length = P.length →
      ∀ (x : V) (S : List V) (MS : List Mark), MS.length = S.length →
        G.pathBlocked Z (P ++ x :: S) (MP ++ MS) = false →
        G.pathBlocked Z (P ++ [x]) MP = false := by
  intro P
  induction P with
  | nil =>
      intro MP hlen x S MS _ _
      have hMP : MP = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst hMP; rfl
  | cons p P' ih =>
      intro MP hlen x S MS hS h
      cases MP with
      | nil => simp at hlen
      | cons mp MP' =>
          have hlen' : MP'.length = P'.length := by simpa using hlen
          rw [List.cons_append, List.cons_append] at h
          cases P' with
          | nil =>
              have hMP' : MP' = [] := List.length_eq_zero_iff.mp (by simpa using hlen')
              subst hMP'
              rfl
          | cons p' P'' =>
              cases MP' with
              | nil => simp at hlen'
              | cons m2 MP'' =>
                  have hlen'' : MP''.length = P''.length := by simpa using hlen'
                  simp only [List.cons_append] at h ⊢
                  rw [pathBlocked_cons2 G Z p p' (P'' ++ [x]) mp (m2 :: MP'')
                        (by simp only [List.length_append, List.length_cons]; omega),
                      Bool.or_eq_false_iff]
                  rw [pathBlocked_cons2 G Z p p' (P'' ++ x :: S) mp (m2 :: (MP'' ++ MS))
                        (by simp only [List.length_append, List.length_cons]; omega),
                      Bool.or_eq_false_iff] at h
                  refine ⟨h.1, ?_⟩
                  have := ih (m2 :: MP'') hlen' x S MS hS (by simp only [List.cons_append]; exact h.2)
                  simpa only [List.cons_append] using this

/-- Read off the blocking verdict at one interior vertex of an active walk. -/
lemma segmentBlocked_extract (G : ADMG V) (Z : Finset V)
    (P : List V) (MP : List Mark) (hlen : MP.length = P.length)
    (w x y : V) (D : List V) (m1 m2 : Mark) (MD : List Mark)
    (hD : MD.length = D.length)
    (h : G.pathBlocked Z (P ++ w :: x :: y :: D) (MP ++ m1 :: m2 :: MD) = false) :
    G.segmentBlocked Z x m1 m2 = false := by
  have hsuf : G.pathBlocked Z (w :: x :: y :: D) (m1 :: m2 :: MD) = false := by
    refine pathBlocked_suffix G Z P MP hlen _ _ ?_ h
    simp only [List.length_cons]; omega
  have hstep : G.pathBlocked Z (w :: x :: y :: D) (m1 :: m2 :: MD)
      = (G.segmentBlocked Z x m1 m2 || G.pathBlocked Z (x :: y :: D) (m2 :: MD)) := rfl
  rw [hstep, Bool.or_eq_false_iff] at hsuf
  exact hsuf.1

private lemma exists_concat {α : Type*} :
    ∀ (l : List α), l ≠ [] → ∃ L b, l = L ++ [b] := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
      intro _
      cases t with
      | nil => exact ⟨[], a, rfl⟩
      | cons b t' =>
          obtain ⟨L, x, hx⟩ := ih (by simp)
          exact ⟨a :: L, x, by rw [hx]; simp⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- §3. Leaving a vertex forward: chain, or an opened collider downstream
-- ─────────────────────────────────────────────────────────────────────────────

/-- **Chain-or-ancestor.**  An active walk that leaves `u` along a FORWARD
    directed edge either continues forward the whole way, or hits a collider
    that (being a descendant of `u`) makes `u` an ancestor of `Z`. -/
lemma chain_or_ancestor (G : ADMG V) (Z : Finset V) :
    ∀ (L : List V) (M' : List Mark) (u : V),
      M'.length + 1 = L.length →
      G.IsWalk (u :: L) (Mark.dirFwd :: M') →
      G.pathBlocked Z (u :: L) (Mark.dirFwd :: M') = false →
      (∀ m ∈ M', m = Mark.dirFwd) ∨ G.hasReflDescIn u Z := by
  intro L
  induction L with
  | nil => intro M' u hlen _ _; simp at hlen
  | cons l0 L' ih =>
      intro M' u hlen hwalk hblk
      have hlen' : M'.length = L'.length := by simpa using hlen
      have hdir : G.directed u l0 = true := hwalk.1
      have hdesc : l0 ∈ G.descendants u := G.directed_mem_descendants hdir
      have hwalk' : G.IsWalk (l0 :: L') M' := hwalk.2
      cases M' with
      | nil => left; intro m hm; simp at hm
      | cons m' M'' =>
          have hlen'' : M''.length + 1 = L'.length := by simpa using hlen'
          rw [pathBlocked_cons2 G Z u l0 L' Mark.dirFwd (m' :: M'') hlen',
              Bool.or_eq_false_iff] at hblk
          have hseg : G.segmentBlocked Z l0 Mark.dirFwd m' = false := by
            simpa using hblk.1
          have htail : G.pathBlocked Z (l0 :: L') (m' :: M'') = false := hblk.2
          by_cases hm' : m' = Mark.dirFwd
          · subst hm'
            rcases ih M'' l0 hlen'' hwalk' htail with hall | hanc
            · left
              intro m hm
              rcases List.mem_cons.mp hm with h | h
              · exact h
              · exact hall m h
            · exact Or.inr (hasReflDescIn_of_descendant G hdesc hanc)
          · refine Or.inr ?_
            have hcoll : isCollider Mark.dirFwd m' = true := by
              cases m' with
              | dirFwd => exact absurd rfl hm'
              | dirBack => rfl
              | bidir => rfl
            exact hasReflDescIn_of_descendant G hdesc
              ((collider_seg_false_iff G Z l0 Mark.dirFwd m' hcoll).mp hseg)

-- ─────────────────────────────────────────────────────────────────────────────
-- §4. The seam
-- ─────────────────────────────────────────────────────────────────────────────

/-- **The seam is still unblocked.**  Excising the loop `v :: B ++ [v]` from an
    active walk replaces the two triples at the two copies of `v` by a single
    new one (incoming mark `mA`, outgoing mark `mc`).  This new triple is
    unblocked.

    The only hard case is when the seam is a collider that neither original
    triple at `v` already opens.  Then the loop must leave `v` forward
    (`mb = dirFwd`) and re-enter `v` forward (`mblast = dirBack`, i.e. an
    arrow out of `v`), so somewhere strictly inside the loop the arrows meet
    head-on at a collider.  That collider is a descendant of `v` and is open,
    hence `v ∈ An(Z)` and the seam is open too. -/
lemma seam_unblocked (G : ADMG V) (Z : Finset V)
    (a v c0 : V) (mA mc : Mark) (B : List V) (MB : List Mark)
    (C'' : List V) (MC' : List Mark)
    (hMB : MB.length = B.length + 1) (hMC : MC'.length = C''.length)
    (hwalk : G.IsWalk (a :: v :: (B ++ v :: c0 :: C'')) (mA :: (MB ++ mc :: MC')))
    (hblk : G.pathBlocked Z (a :: v :: (B ++ v :: c0 :: C'')) (mA :: (MB ++ mc :: MC'))
      = false) :
    G.segmentBlocked Z v mA mc = false := by
  -- the loop cannot be empty: that would be a self-loop at `v`
  have hBne : B ≠ [] := by
    rintro rfl
    obtain ⟨mb, hmb⟩ : ∃ mb, MB = [mb] := by
      cases MB with
      | nil => simp at hMB
      | cons m ms => cases ms with
        | nil => exact ⟨m, rfl⟩
        | cons _ _ => simp at hMB
    subst hmb
    simp only [List.nil_append, List.cons_append] at hwalk
    have hv : Mark.valid G v v mb = true := hwalk.2.1
    cases mb with
    | dirFwd =>
        have h' : G.directed v v = true := hv
        rw [G.dir_no_loop v] at h'; exact absurd h' (by simp)
    | dirBack =>
        have h' : G.directed v v = true := hv
        rw [G.dir_no_loop v] at h'; exact absurd h' (by simp)
    | bidir =>
        have h' : G.bidirected v v = true := hv
        rw [G.bid_no_loop v] at h'; exact absurd h' (by simp)
  -- head decomposition of the loop's marks
  obtain ⟨mb, MB', hMBeq⟩ : ∃ mb MB', MB = mb :: MB' := by
    cases MB with
    | nil => simp at hMB
    | cons mb MB' => exact ⟨mb, MB', rfl⟩
  -- tail (snoc) decomposition of the loop and its marks
  obtain ⟨B'', blast, hBeq⟩ := exists_concat B hBne
  obtain ⟨MB'', mblast, hMBeq2⟩ := exists_concat MB (by rw [hMBeq]; simp)
  have hlenB'' : MB''.length = B''.length + 1 := by
    have hL : MB.length = B.length + 1 := hMB
    rw [hBeq, hMBeq2] at hL
    simp only [List.length_append, List.length_cons, List.length_nil] at hL
    omega
  have hlenMB' : MB'.length = B.length := by
    have hL : MB.length = B.length + 1 := hMB
    rw [hMBeq] at hL
    simpa using hL
  -- the two original triples at the two copies of `v`
  have h1 : G.segmentBlocked Z v mA mb = false := by
    obtain ⟨b0, B', hB0⟩ : ∃ b0 B', B = b0 :: B' := by
      cases B with
      | nil => exact absurd rfl hBne
      | cons b0 B' => exact ⟨b0, B', rfl⟩
    have hs : G.pathBlocked Z (a :: v :: b0 :: (B' ++ v :: c0 :: C''))
        (mA :: mb :: (MB' ++ mc :: MC')) = false := by
      have := hblk
      rw [hB0, hMBeq] at this
      simpa only [List.cons_append] using this
    have hstep : G.pathBlocked Z (a :: v :: b0 :: (B' ++ v :: c0 :: C''))
        (mA :: mb :: (MB' ++ mc :: MC'))
        = (G.segmentBlocked Z v mA mb
            || G.pathBlocked Z (v :: b0 :: (B' ++ v :: c0 :: C''))
                 (mb :: (MB' ++ mc :: MC'))) := rfl
    rw [hstep, Bool.or_eq_false_iff] at hs
    exact hs.1
  have h2 : G.segmentBlocked Z v mblast mc = false := by
    refine segmentBlocked_extract G Z (a :: v :: B'') (mA :: MB'') ?_
      blast v c0 C'' mblast mc MC' hMC ?_
    · simp only [List.length_cons]; omega
    · have := hblk
      rw [hBeq, hMBeq2] at this
      simpa only [List.append_assoc, List.cons_append, List.singleton_append,
        List.nil_append] using this
  -- case analysis on the seam
  by_cases hmA : mA.intoRight = true
  · by_cases hmc : mc.intoLeft = true
    · -- the seam IS a collider; we must show `v ∈ An(Z)`
      have hcollS : isCollider mA mc = true := by simp [isCollider, hmA, hmc]
      refine (collider_seg_false_iff G Z v mA mc hcollS).mpr ?_
      by_cases hmb : mb.intoLeft = true
      · have hcoll1 : isCollider mA mb = true := by simp [isCollider, hmA, hmb]
        exact (collider_seg_false_iff G Z v mA mb hcoll1).mp h1
      · by_cases hmbl : mblast.intoRight = true
        · have hcoll2 : isCollider mblast mc = true := by simp [isCollider, hmbl, hmc]
          exact (collider_seg_false_iff G Z v mblast mc hcoll2).mp h2
        · -- leaves `v` forward and re-enters `v` forward: chain argument
          have hmbF : mb = Mark.dirFwd := by
            cases mb with
            | dirFwd => rfl
            | dirBack => exact absurd rfl hmb
            | bidir => exact absurd rfl hmb
          have hmblB : mblast = Mark.dirBack := by
            cases mblast with
            | dirFwd => exact absurd rfl hmbl
            | dirBack => rfl
            | bidir => exact absurd rfl hmbl
          -- the walk and blocking restricted to the loop
          have hlen1 : MB.length = (v :: B).length := by simp only [List.length_cons]; omega
          have hwalkV : G.IsWalk ((v :: B) ++ v :: (c0 :: C'')) (MB ++ (mc :: MC')) := by
            simpa only [List.cons_append] using isWalk_tail G hwalk
          have hblkV : G.pathBlocked Z ((v :: B) ++ v :: (c0 :: C'')) (MB ++ (mc :: MC'))
              = false := by
            refine pathBlocked_tail G Z ?_ hblk
            simp only [List.length_append, List.length_cons]; omega
          have hloopWalk : G.IsWalk ((v :: B) ++ [v]) MB :=
            isWalk_take G (v :: B) MB hlen1 v (c0 :: C'') (mc :: MC') hwalkV
          have hloopBlk : G.pathBlocked Z ((v :: B) ++ [v]) MB = false :=
            pathBlocked_take G Z (v :: B) MB hlen1 v (c0 :: C'') (mc :: MC')
              (by simp only [List.length_cons]; omega) hblkV
          rw [List.cons_append, hMBeq, hmbF] at hloopWalk hloopBlk
          have hchain := chain_or_ancestor G Z (B ++ [v]) MB' v
            (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
            hloopWalk hloopBlk
          rcases hchain with hall | hanc
          · exfalso
            have hmem : mblast ∈ MB := by rw [hMBeq2]; simp
            rw [hMBeq] at hmem
            rcases List.mem_cons.mp hmem with h | h
            · rw [hmbF] at h; exact absurd (h ▸ hmblB) (by simp)
            · exact absurd (hall mblast h) (by rw [hmblB]; simp)
          · exact hanc
    · -- seam not a collider (no arrowhead into `v` from the right)
      have hmcf : mc.intoLeft = false := by simpa using hmc
      have hncS : isCollider mA mc = false := by simp [isCollider, hmcf]
      have hnc2 : isCollider mblast mc = false := by simp [isCollider, hmcf]
      exact (noncollider_seg_false_iff G Z v mA mc hncS).mpr
        ((noncollider_seg_false_iff G Z v mblast mc hnc2).mp h2)
  · -- seam not a collider (no arrowhead into `v` from the left)
    have hmAf : mA.intoRight = false := by simpa using hmA
    have hncS : isCollider mA mc = false := by simp [isCollider, hmAf]
    have hnc1 : isCollider mA mb = false := by simp [isCollider, hmAf]
    exact (noncollider_seg_false_iff G Z v mA mc hncS).mpr
      ((noncollider_seg_false_iff G Z v mA mb hnc1).mp h1)

-- ─────────────────────────────────────────────────────────────────────────────
-- §5. Excision
-- ─────────────────────────────────────────────────────────────────────────────

/-- Excising a loop leaves a walk. -/
lemma excise_isWalk (G : ADMG V) :
    ∀ (A : List V) (MA : List Mark), MA.length = A.length →
    ∀ (v : V) (B : List V) (MB : List Mark), MB.length = B.length + 1 →
    ∀ (C : List V) (MC : List Mark), MC.length = C.length →
    G.IsWalk (A ++ v :: (B ++ v :: C)) (MA ++ (MB ++ MC)) →
    G.IsWalk (A ++ v :: C) (MA ++ MC) := by
  intro A
  induction A with
  | nil =>
      intro MA hlenA v B MB hMB C MC hMC hwalk
      have hMA : MA = [] := List.length_eq_zero_iff.mp (by simpa using hlenA)
      subst hMA
      simp only [List.nil_append] at hwalk ⊢
      refine isWalk_suffix G (v :: B) MB (by simp only [List.length_cons]; omega)
        (v :: C) MC ?_
      simpa only [List.cons_append] using hwalk
  | cons a A' ih =>
      intro MA hlenA v B MB hMB C MC hMC hwalk
      cases MA with
      | nil => simp at hlenA
      | cons mA MA' =>
        have hlenA' : MA'.length = A'.length := by simpa using hlenA
        cases A' with
        | nil =>
            have hMA' : MA' = [] := List.length_eq_zero_iff.mp (by simpa using hlenA')
            subst hMA'
            simp only [List.nil_append, List.cons_append] at hwalk ⊢
            refine ⟨hwalk.1, ?_⟩
            refine isWalk_suffix G (v :: B) MB (by simp only [List.length_cons]; omega)
              (v :: C) MC ?_
            simpa only [List.cons_append] using hwalk.2
        | cons a' A'' =>
            cases MA' with
            | nil => simp at hlenA'
            | cons m2 MA'' =>
                simp only [List.cons_append] at hwalk ⊢
                refine ⟨hwalk.1, ?_⟩
                have hw2 : G.IsWalk ((a' :: A'') ++ v :: (B ++ v :: C))
                    ((m2 :: MA'') ++ (MB ++ MC)) := by
                  simpa only [List.cons_append] using hwalk.2
                have := ih (m2 :: MA'') hlenA' v B MB hMB C MC hMC hw2
                simpa only [List.cons_append] using this

/-- Excising a loop keeps the walk ACTIVE.  Everything except the seam triple
    at `v` is untouched; the seam is handled by `seam_unblocked`. -/
lemma excise_pathBlocked (G : ADMG V) (Z : Finset V) :
    ∀ (A : List V) (MA : List Mark), MA.length = A.length →
    ∀ (v : V) (B : List V) (MB : List Mark), MB.length = B.length + 1 →
    ∀ (C : List V) (MC : List Mark), MC.length = C.length →
    G.IsWalk (A ++ v :: (B ++ v :: C)) (MA ++ (MB ++ MC)) →
    G.pathBlocked Z (A ++ v :: (B ++ v :: C)) (MA ++ (MB ++ MC)) = false →
    G.pathBlocked Z (A ++ v :: C) (MA ++ MC) = false := by
  intro A
  induction A with
  | nil =>
      intro MA hlenA v B MB hMB C MC hMC _ hblk
      have hMA : MA = [] := List.length_eq_zero_iff.mp (by simpa using hlenA)
      subst hMA
      simp only [List.nil_append] at hblk ⊢
      refine pathBlocked_suffix G Z (v :: B) MB (by simp only [List.length_cons]; omega)
        (v :: C) MC (by simp only [List.length_cons]; omega) ?_
      simpa only [List.cons_append] using hblk
  | cons a A' ih =>
      intro MA hlenA v B MB hMB C MC hMC hwalk hblk
      cases MA with
      | nil => simp at hlenA
      | cons mA MA' =>
        have hlenA' : MA'.length = A'.length := by simpa using hlenA
        cases A' with
        | nil =>
            have hMA' : MA' = [] := List.length_eq_zero_iff.mp (by simpa using hlenA')
            subst hMA'
            simp only [List.nil_append, List.cons_append] at hwalk hblk ⊢
            cases C with
            | nil =>
                have hMCn : MC = [] := List.length_eq_zero_iff.mp (by simpa using hMC)
                subst hMCn
                rfl
            | cons c0 C'' =>
                cases MC with
                | nil => simp at hMC
                | cons mc MC' =>
                    have hMC' : MC'.length = C''.length := by simpa using hMC
                    show (G.segmentBlocked Z v mA mc
                      || G.pathBlocked Z (v :: c0 :: C'') (mc :: MC')) = false
                    rw [Bool.or_eq_false_iff]
                    refine ⟨seam_unblocked G Z a v c0 mA mc B MB C'' MC' hMB hMC' hwalk hblk, ?_⟩
                    refine pathBlocked_suffix G Z (a :: v :: B) (mA :: MB)
                      (by simp only [List.length_cons]; omega)
                      (v :: c0 :: C'') (mc :: MC')
                      (by simp only [List.length_cons]; omega) ?_
                    simpa only [List.cons_append] using hblk
        | cons a' A'' =>
            cases MA' with
            | nil => simp at hlenA'
            | cons m2 MA'' =>
                have hlenA'' : MA''.length = A''.length := by simpa using hlenA'
                simp only [List.cons_append] at hwalk hblk ⊢
                rw [pathBlocked_cons2 G Z a a' (A'' ++ v :: C) mA (m2 :: (MA'' ++ MC))
                      (by simp only [List.length_cons, List.length_append]; omega),
                    Bool.or_eq_false_iff]
                rw [pathBlocked_cons2 G Z a a' (A'' ++ v :: (B ++ v :: C)) mA
                      (m2 :: (MA'' ++ (MB ++ MC)))
                      (by simp only [List.length_cons, List.length_append]; omega),
                    Bool.or_eq_false_iff] at hblk
                refine ⟨by simpa using hblk.1, ?_⟩
                have hw2 : G.IsWalk ((a' :: A'') ++ v :: (B ++ v :: C))
                    ((m2 :: MA'') ++ (MB ++ MC)) := by
                  simpa only [List.cons_append] using hwalk.2
                have hb2 : G.pathBlocked Z ((a' :: A'') ++ v :: (B ++ v :: C))
                    ((m2 :: MA'') ++ (MB ++ MC)) = false := by
                  simpa only [List.cons_append] using hblk.2
                have := ih (m2 :: MA'') hlenA' v B MB hMB C MC hMC hw2 hb2
                simpa only [List.cons_append] using this

private lemma exists_dup_decomp {α : Type*} [DecidableEq α] :
    ∀ (l : List α), ¬ l.Nodup → ∃ (x : α) (A B C : List α), l = A ++ x :: (B ++ x :: C) := by
  intro l
  induction l with
  | nil => intro h; exact absurd List.nodup_nil h
  | cons a t ih =>
      intro h
      by_cases ht : t.Nodup
      · have hat : a ∈ t := by
          by_contra hna
          exact h (List.nodup_cons.mpr ⟨hna, ht⟩)
        obtain ⟨B, C, hBC⟩ := List.append_of_mem hat
        exact ⟨a, [], B, C, by rw [hBC]; rfl⟩
      · obtain ⟨x, A, B, C, hx⟩ := ih ht
        exact ⟨x, a :: A, B, C, by rw [hx]; simp⟩

private lemma split3 {α : Type*} (M : List α) (p q r : ℕ) (h : M.length = p + q + r) :
    ∃ M1 M2 M3, M = M1 ++ (M2 ++ M3) ∧ M1.length = p ∧ M2.length = q ∧ M3.length = r := by
  refine ⟨M.take p, (M.drop p).take q, (M.drop p).drop q, ?_, ?_, ?_, ?_⟩
  · rw [List.take_append_drop, List.take_append_drop]
  · simp only [List.length_take]; omega
  · simp only [List.length_take, List.length_drop]; omega
  · simp only [List.length_drop]; omega

private lemma getLast?_append_cons {α : Type*} (l : List α) (a : α) (t : List α) :
    (l ++ a :: t).getLast? = (a :: t).getLast? := by
  induction l with
  | nil => rfl
  | cons b l' ih =>
      have hne : l' ++ a :: t ≠ [] := by simp
      obtain ⟨y, s, hys⟩ : ∃ y s, l' ++ a :: t = y :: s := by
        cases hcase : l' ++ a :: t with
        | nil => exact absurd hcase hne
        | cons y s => exact ⟨y, s, rfl⟩
      rw [List.cons_append, hys, List.getLast?_cons_cons, ← hys]
      exact ih

/-- **Excision preserves activeness.**  A walk with a repeated vertex can be
    shortened to a strictly shorter active walk with the same endpoints. -/
lemma excise_preserves_active (G : ADMG V) (Z : Finset V)
    (verts : List V) (marks : List Mark)
    (hlen : marks.length + 1 = verts.length)
    (hwalk : G.IsWalk verts marks)
    (hactive : G.pathBlocked Z verts marks = false)
    (hrep : ¬ verts.Nodup) :
    ∃ (verts' : List V) (marks' : List Mark),
      G.IsWalk verts' marks' ∧
      marks'.length + 1 = verts'.length ∧
      verts'.length < verts.length ∧
      verts'.head? = verts.head? ∧
      verts'.getLast? = verts.getLast? ∧
      G.pathBlocked Z verts' marks' = false := by
  obtain ⟨x, A, B, C, hv⟩ := exists_dup_decomp verts hrep
  subst hv
  have hml : marks.length = A.length + (B.length + 1) + C.length := by
    simp only [List.length_append, List.length_cons] at hlen
    omega
  obtain ⟨MA, MB, MC, hm, hMA, hMB, hMC⟩ :=
    split3 marks A.length (B.length + 1) C.length hml
  subst hm
  refine ⟨A ++ x :: C, MA ++ MC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact excise_isWalk G A MA hMA x B MB hMB C MC hMC hwalk
  · simp only [List.length_append, List.length_cons]; omega
  · simp only [List.length_append, List.length_cons]; omega
  · cases A <;> rfl
  · have hL : (A ++ x :: C).getLast? = (x :: C).getLast? := getLast?_append_cons A x C
    have hR : (A ++ x :: (B ++ x :: C)).getLast? = (x :: C).getLast? := by
      have hsplit : A ++ x :: (B ++ x :: C) = (A ++ (x :: B)) ++ (x :: C) := by
        simp only [List.append_assoc, List.cons_append]
      rw [hsplit, getLast?_append_cons]
    rw [hL, hR]
  · exact excise_pathBlocked G Z A MA hMA x B MB hMB C MC hMC hwalk hactive

-- ─────────────────────────────────────────────────────────────────────────────
-- §6. Minimal witness: an active walk contains an active simple path
-- ─────────────────────────────────────────────────────────────────────────────

/-- There is an active WALK from `X` to `Y` given `Z`. -/
def dConnectedWalk (G : ADMG V) (X Y : V) (Z : Finset V) : Prop :=
  ∃ (verts : List V) (marks : List Mark), G.IsWalk verts marks ∧
    verts.head? = some X ∧ verts.getLast? = some Y ∧
    G.pathBlocked Z verts marks = false

/-- There is an active simple PATH from `X` to `Y` given `Z`. -/
def dConnectedPath (G : ADMG V) (X Y : V) (Z : Finset V) : Prop :=
  ∃ (verts : List V) (marks : List Mark), G.IsWalk verts marks ∧ verts.Nodup ∧
    verts.head? = some X ∧ verts.getLast? = some Y ∧
    G.pathBlocked Z verts marks = false

lemma not_dConnectedWalk_iff_dSepWalk (G : ADMG V) (X Y : V) (Z : Finset V) :
    ¬ G.dConnectedWalk X Y Z ↔ G.dSepWalk X Y Z := by
  constructor
  · intro h verts marks hw hh hl
    by_contra hne
    rw [Bool.not_eq_true] at hne
    exact h ⟨verts, marks, hw, hh, hl, hne⟩
  · rintro h ⟨verts, marks, hw, hh, hl, hb⟩
    rw [h verts marks hw hh hl] at hb
    exact absurd hb (by simp)

lemma not_dConnectedPath_iff_dSep (G : ADMG V) (X Y : V) (Z : Finset V) :
    ¬ G.dConnectedPath X Y Z ↔ G.dSep X Y Z := by
  constructor
  · intro h verts marks hw hn hh hl
    by_contra hne
    rw [Bool.not_eq_true] at hne
    exact h ⟨verts, marks, hw, hn, hh, hl, hne⟩
  · rintro h ⟨verts, marks, hw, hn, hh, hl, hb⟩
    rw [h verts marks hw hn hh hl] at hb
    exact absurd hb (by simp)

private lemma active_walk_to_path_aux (G : ADMG V) (X Y : V) (Z : Finset V) :
    ∀ (n : ℕ) (verts : List V) (marks : List Mark), verts.length ≤ n →
      marks.length + 1 = verts.length →
      G.IsWalk verts marks → verts.head? = some X → verts.getLast? = some Y →
      G.pathBlocked Z verts marks = false →
      G.dConnectedPath X Y Z := by
  intro n
  induction n with
  | zero =>
      intro verts marks hle _ _ hh _ _
      have hnil : verts = [] := List.length_eq_zero_iff.mp (by omega)
      subst hnil; simp at hh
  | succ k ih =>
      intro verts marks hle hlen hw hh hl hb
      by_cases hnd : verts.Nodup
      · exact ⟨verts, marks, hw, hnd, hh, hl, hb⟩
      · obtain ⟨verts', marks', hw', hlen', hlt, hh', hl', hb'⟩ :=
          excise_preserves_active G Z verts marks hlen hw hb hnd
        exact ih verts' marks' (by omega) hlen' hw'
          (by rw [hh', hh]) (by rw [hl', hl]) hb'

/-- **Every active walk contains an active simple path** with the same
    endpoints.  Take a minimum-length active walk: if it repeated a vertex,
    `excise_preserves_active` would produce a strictly shorter one. -/
theorem active_walk_contains_active_path (G : ADMG V) (X Y : V) (Z : Finset V) :
    G.dConnectedWalk X Y Z → G.dConnectedPath X Y Z := by
  rintro ⟨verts, marks, hw, hh, hl, hb⟩
  have hne : verts ≠ [] := by rintro rfl; simp at hh
  exact active_walk_to_path_aux G X Y Z verts.length verts marks le_rfl
    (G.isWalk_length' hw hne) hw hh hl hb

-- ─────────────────────────────────────────────────────────────────────────────
-- §7. The equivalence, and the graphoid axioms on `dSep`
-- ─────────────────────────────────────────────────────────────────────────────

/-- **Path separation and walk separation coincide.**  The `←` direction is
    free; the `→` direction is the minimal-witness argument above. -/
theorem dSep_iff_dSepWalk (G : ADMG V) (X Y : V) (Z : Finset V) :
    G.dSep X Y Z ↔ G.dSepWalk X Y Z := by
  constructor
  · intro h
    rw [← not_dConnectedWalk_iff_dSepWalk]
    intro hconn
    exact (not_dConnectedPath_iff_dSep G X Y Z).mpr h
      (active_walk_contains_active_path G X Y Z hconn)
  · exact dSep_of_dSepWalk G X Y Z

theorem dSepSet_iff_dSepSetWalk (G : ADMG V) (X Y Z : Finset V) :
    G.dSepSet X Y Z ↔ G.dSepSetWalk X Y Z := by
  constructor
  · intro h x hx y hy; exact (dSep_iff_dSepWalk G x y Z).mp (h x hx y hy)
  · intro h x hx y hy; exact (dSep_iff_dSepWalk G x y Z).mpr (h x hx y hy)

/-- **Weak Union** on the textbook path-based relation. -/
theorem dSepSet_weak_union_path (G : ADMG V) (X Y W Z : Finset V) :
    G.dSepSet X (Y ∪ W) Z → G.dSepSet X Y (Z ∪ W) ∧ G.dSepSet X W (Z ∪ Y) := by
  intro h
  rw [dSepSet_iff_dSepSetWalk] at h
  obtain ⟨h1, h2⟩ := dSepSetWalk_weak_union G X Y W Z h
  exact ⟨(dSepSet_iff_dSepSetWalk G X Y (Z ∪ W)).mpr h1,
         (dSepSet_iff_dSepSetWalk G X W (Z ∪ Y)).mpr h2⟩

/-- **Contraction** on the textbook path-based relation. -/
theorem dSepSet_contraction_path (G : ADMG V) (X Y W Z : Finset V) :
    G.dSepSet X Y Z → G.dSepSet X W (Z ∪ Y) → G.dSepSet X (Y ∪ W) Z := by
  intro h1 h2
  rw [dSepSet_iff_dSepSetWalk] at h1 h2 ⊢
  exact dSepSetWalk_contraction G X Y W Z h1 h2

/-- **Intersection** on the textbook path-based relation. -/
theorem dSepSet_intersection_path (G : ADMG V) (X Y W Z : Finset V) :
    G.dSepSet X Y (Z ∪ W) → G.dSepSet X W (Z ∪ Y) → G.dSepSet X (Y ∪ W) Z := by
  intro h1 h2
  rw [dSepSet_iff_dSepSetWalk] at h1 h2 ⊢
  exact dSepSetWalk_intersection G X Y W Z h1 h2

/-- **All five graphoid axioms for the textbook, simple-path relation `dSep`**:
    Symmetry, Decomposition, Weak Union, Contraction, Intersection. -/
theorem dSep_full_graphoid (G : ADMG V) :
    (∀ X Y Z : Finset V, G.dSepSet X Y Z ↔ G.dSepSet Y X Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X (Y ∪ W) Z → G.dSepSet X Y Z ∧ G.dSepSet X W Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X (Y ∪ W) Z →
        G.dSepSet X Y (Z ∪ W) ∧ G.dSepSet X W (Z ∪ Y)) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X Y Z → G.dSepSet X W (Z ∪ Y) →
        G.dSepSet X (Y ∪ W) Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X Y (Z ∪ W) → G.dSepSet X W (Z ∪ Y) →
        G.dSepSet X (Y ∪ W) Z) :=
  ⟨fun X Y Z => dSepSet_symm G X Y Z,
   fun X Y W Z h => dSepSet_decomp G X Y W Z h,
   fun X Y W Z h => dSepSet_weak_union_path G X Y W Z h,
   fun X Y W Z h1 h2 => dSepSet_contraction_path G X Y W Z h1 h2,
   fun X Y W Z h1 h2 => dSepSet_intersection_path G X Y W Z h1 h2⟩

end ADMG
end CausalLib

import CausalLib.DAG

namespace CausalLib

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite acyclic directed mixed graph. Bows are allowed; acyclicity concerns
only directed edges. -/
structure ADMG (V : Type*) [Fintype V] [DecidableEq V] extends DAG V where
  bidirected : V → V → Bool
  bid_no_loop : ∀ v, bidirected v v = false
  bid_symm : ∀ u v, bidirected u v = bidirected v u

namespace ADMG

abbrev directed (G : ADMG V) := G.toDAG.hasEdge
abbrev hasEdge (G : ADMG V) := G.directed
abbrev hasBidirectedEdge (G : ADMG V) := G.bidirected
abbrev parents (G : ADMG V) := G.toDAG.parents
abbrev children (G : ADMG V) := G.toDAG.children
abbrev ancestors (G : ADMG V) := G.toDAG.ancestors
abbrev descendants (G : ADMG V) := G.toDAG.descendants
abbrev reachableN (G : ADMG V) := G.toDAG.reachableN
abbrev canReach (G : ADMG V) := G.toDAG.canReach

def spouses (G : ADMG V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => G.bidirected v u)

def adjacent (G : ADMG V) (u v : V) : Bool :=
  G.directed u v || G.directed v u || G.bidirected u v

/-- The chosen edge and its orientation relative to traversal. Explicit marks
distinguish the two possible edges of a bow. -/
inductive Mark
  | dirFwd
  | dirBack
  | bidir
  deriving DecidableEq

namespace Mark

/-- Reverse the traversal orientation of an edge. -/
def flip : Mark → Mark
  | dirFwd  => dirBack
  | dirBack => dirFwd
  | bidir   => bidir

@[simp] lemma flip_flip (m : Mark) : m.flip.flip = m := by cases m <;> rfl

/-- Whether the edge has an arrowhead at the next vertex. -/
def intoRight : Mark → Bool
  | dirFwd  => true
  | dirBack => false
  | bidir   => true

/-- Whether the edge has an arrowhead at the previous vertex. -/
def intoLeft : Mark → Bool
  | dirFwd  => false
  | dirBack => true
  | bidir   => true

@[simp] lemma intoLeft_flip (m : Mark) : m.flip.intoLeft = m.intoRight := by cases m <;> rfl
@[simp] lemma intoRight_flip (m : Mark) : m.flip.intoRight = m.intoLeft := by cases m <;> rfl

/-- Validate the chosen edge between two consecutive vertices. -/
def valid (G : ADMG V) (x y : V) : Mark → Bool
  | dirFwd  => G.directed x y
  | dirBack => G.directed y x
  | bidir   => G.bidirected x y

lemma valid_flip (G : ADMG V) (a b : V) (m : Mark) :
    valid G a b m = valid G b a m.flip := by
  cases m <;> simp [valid, flip, G.bid_symm a b]

end Mark

/-- Both incident marks must have an arrowhead at the interior vertex. -/
def isCollider (m1 m2 : Mark) : Bool := m1.intoRight && m2.intoLeft

lemma isCollider_flip_swap (m1 m2 : Mark) :
    isCollider m2.flip m1.flip = isCollider m1 m2 := by
  cases m1 <;> cases m2 <;> rfl

/-- Non-colliders block when conditioned on; colliders block when neither
they nor any directed descendant is conditioned on. -/
def segmentBlocked (G : ADMG V) (Z : Finset V) (curr : V) (m1 m2 : Mark) : Bool :=
  if isCollider m1 m2 then
    !(curr ∈ Z || (G.descendants curr ∩ Z).Nonempty)
  else
    curr ∈ Z

lemma segmentBlocked_flip_swap (G : ADMG V) (Z : Finset V) (curr : V) (m1 m2 : Mark) :
    G.segmentBlocked Z curr m2.flip m1.flip = G.segmentBlocked Z curr m1 m2 := by
  simp [ADMG.segmentBlocked, isCollider_flip_swap]

/-- Aligned edge validation. Mismatched vertex/mark lists are rejected. -/
def ValidSteps (G : ADMG V) : List V → List Mark → Prop
  | [], [] => True
  | [_], [] => True
  | a :: b :: vs, m :: ms => Mark.valid G a b m = true ∧ ValidSteps G (b :: vs) ms
  | _, _ => False

/-- A marked simple path: aligned valid edges and no repeated vertices.
Empty and singleton paths have no marks. -/
def IsPath (G : ADMG V) (verts : List V) (marks : List Mark) : Prop :=
  G.ValidSteps verts marks ∧ verts.Nodup

instance instDecidableValidSteps (G : ADMG V) : ∀ P M, Decidable (G.ValidSteps P M)
  | [], [] => isTrue trivial
  | [_], [] => isTrue trivial
  | a :: b :: P, m :: M =>
      letI := instDecidableValidSteps G (b :: P) M
      inferInstanceAs (Decidable (Mark.valid G a b m = true ∧ G.ValidSteps (b :: P) M))
  | [], _ :: _ | [_], _ :: _ | _ :: _ :: _, [] => isFalse id

instance (G : ADMG V) (P : List V) (M : List Mark) : Decidable (G.IsPath P M) :=
  inferInstanceAs (Decidable (G.ValidSteps P M ∧ P.Nodup))

@[simp] lemma validSteps_nil (G : ADMG V) : G.ValidSteps ([] : List V) [] := trivial
@[simp] lemma validSteps_singleton (G : ADMG V) (a : V) : G.ValidSteps [a] [] := trivial

lemma validSteps_length (G : ADMG V) :
    ∀ (verts : List V) (marks : List Mark), G.ValidSteps verts marks →
      marks.length + 1 = verts.length ∨ (verts = [] ∧ marks = []) := by
  intro verts
  induction verts with
  | nil => intro marks h; cases marks with
      | nil => exact Or.inr ⟨rfl, rfl⟩
      | cons m ms => exact absurd h (by simp [ValidSteps])
  | cons a vs ih =>
    intro marks h
    cases vs with
    | nil =>
      cases marks with
      | nil => exact Or.inl rfl
      | cons m ms => exact absurd h (by simp [ValidSteps])
    | cons b vs' =>
      cases marks with
      | nil => exact absurd h (by simp [ValidSteps])
      | cons m ms =>
        obtain ⟨_, htail⟩ := h
        rcases ih ms htail with heq | ⟨hveq, _⟩
        · left; simp only [List.length_cons] at heq ⊢; omega
        · exact absurd hveq (by simp)

lemma validSteps_length' (G : ADMG V) {verts : List V} {marks : List Mark}
    (h : G.ValidSteps verts marks) (hne : verts ≠ []) :
    marks.length + 1 = verts.length := by
  rcases validSteps_length G verts marks h with heq | ⟨hveq, _⟩
  · exact heq
  · exact absurd hveq hne

lemma validSteps_cons₂ (G : ADMG V) (a b : V) (m : Mark) (l : List V) (ms : List Mark) :
    G.ValidSteps (a :: b :: l) (m :: ms) ↔ Mark.valid G a b m = true ∧ G.ValidSteps (b :: l) ms :=
  Iff.rfl

/-- Reverse the order of steps and flip each orientation. -/
def reverseMarks (marks : List Mark) : List Mark := (marks.map Mark.flip).reverse

@[simp] lemma reverseMarks_nil : reverseMarks ([] : List Mark) = [] := rfl

private lemma validSteps_append_one (G : ADMG V) :
    ∀ (l : List V) (ms : List Mark) (c : V), G.ValidSteps l ms → l.getLast? = some c →
      ∀ (x : V) (m' : Mark), Mark.valid G c x m' = true →
        G.ValidSteps (l ++ [x]) (ms ++ [m']) := by
  intro l
  induction l with
  | nil => intro ms c _ hc; simp at hc
  | cons a l ih =>
    cases l with
    | nil =>
      intro ms c hsteps hc x m' hvalid
      cases ms with
      | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hc
        subst hc
        exact ⟨hvalid, trivial⟩
      | cons _ _ => exact absurd hsteps (by simp [ValidSteps])
    | cons b l' =>
      intro ms c hsteps hc x m' hvalid
      cases ms with
      | nil => exact absurd hsteps (by simp [ValidSteps])
      | cons m ms' =>
        obtain ⟨hv, htail⟩ := hsteps
        rw [List.getLast?_cons_cons] at hc
        have ihres := ih ms' c htail hc x m' hvalid
        exact ⟨hv, ihres⟩

lemma validSteps_reverse (G : ADMG V) :
    ∀ (verts : List V) (marks : List Mark), G.ValidSteps verts marks →
      G.ValidSteps verts.reverse (reverseMarks marks) := by
  intro verts
  induction verts with
  | nil =>
      intro marks h
      cases marks with
      | nil => simp [reverseMarks]
      | cons m ms => exact absurd h (by simp [ValidSteps])
  | cons a vs ih =>
    intro marks h
    cases vs with
    | nil =>
      cases marks with
      | nil => simp [reverseMarks]
      | cons m ms => exact absurd h (by simp [ValidSteps])
    | cons b vs' =>
      cases marks with
      | nil => exact absurd h (by simp [ValidSteps])
      | cons m ms =>
        obtain ⟨hv, htail⟩ := h
        have ihtail := ih ms htail
        have hc : (b :: vs').reverse.getLast? = some b := by
          simp [List.getLast?_reverse]
        have hval : Mark.valid G b a m.flip = true := by
          rw [← Mark.valid_flip]; exact hv
        have hstep := validSteps_append_one G (b :: vs').reverse (reverseMarks ms) b ihtail hc a m.flip hval
        have heq1 : (a :: b :: vs').reverse = (b :: vs').reverse ++ [a] := by
          simp [List.reverse_cons]
        have heq2 : reverseMarks (m :: ms) = reverseMarks ms ++ [m.flip] := by
          simp [reverseMarks, List.reverse_cons]
        rw [heq1, heq2]
        exact hstep

/-- A path is blocked if any interior vertex blocks it. This query is used
with `IsPath`; malformed lists are rejected by that predicate. -/
def pathBlocked (G : ADMG V) (Z : Finset V) : List V → List Mark → Bool
  | [], _ => false
  | [_], _ => false
  | [_, _], _ => false
  | _ :: _ :: _ :: _, [] => false
  | _ :: _ :: _ :: _, [_] => false
  | _ :: b :: c :: restV, m1 :: m2 :: restM =>
      G.segmentBlocked Z b m1 m2 || pathBlocked G Z (b :: c :: restV) (m2 :: restM)

lemma segmentBlocked_chain (G : ADMG V) (Z : Finset V) (c : V) (m1 : Mark) (hc : c ∉ Z) :
    G.segmentBlocked Z c m1 Mark.dirFwd = false := by
  have hcoll : isCollider m1 Mark.dirFwd = false := by simp [isCollider, Mark.intoLeft]
  simp [ADMG.segmentBlocked, hcoll, hc]

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

private lemma validSteps_blocked_reverse (G : ADMG V) (Z : Finset V) :
    ∀ (verts : List V) (marks : List Mark), G.ValidSteps verts marks →
      G.pathBlocked Z verts.reverse (reverseMarks marks) = G.pathBlocked Z verts marks := by
  intro verts
  induction verts with
  | nil => intro marks _; cases marks <;> rfl
  | cons a vs ih =>
    intro marks hsteps
    cases vs with
    | nil => cases marks with
        | nil => rfl
        | cons m ms => exact absurd hsteps (by simp [ValidSteps])
    | cons b vs' =>
      cases marks with
      | nil => exact absurd hsteps (by simp [ValidSteps])
      | cons m ms =>
        obtain ⟨hv, htail⟩ := hsteps
        cases vs' with
        | nil =>
          cases ms with
          | nil =>

            rfl
          | cons _ _ => exact absurd htail (by simp [ValidSteps])
        | cons c vs'' =>
          cases ms with
          | nil => exact absurd htail (by simp [ValidSteps])
          | cons m2 ms' =>
            have ihres := ih (m2 :: ms') htail
            obtain ⟨_, htail2⟩ := htail

            have heqV : (a :: b :: c :: vs'').reverse = (c :: vs'').reverse ++ [b, a] := by
              simp [List.reverse_cons]
            have heqM : reverseMarks (m :: m2 :: ms') = reverseMarks ms' ++ [m2.flip, m.flip] := by
              simp [reverseMarks, List.reverse_cons]
            have heqV2 : (c :: vs'').reverse ++ [b] = (b :: c :: vs'').reverse := by
              simp [List.reverse_cons]
            have heqM2 : reverseMarks ms' ++ [m2.flip] = reverseMarks (m2 :: ms') := by
              simp [reverseMarks, List.reverse_cons]
            have hlenP : (reverseMarks ms').length + 1 = (c :: vs'').reverse.length := by
              have hthis := validSteps_length' G htail2 (List.cons_ne_nil c vs'')
              simp only [reverseMarks, List.length_reverse, List.length_map,
                List.length_cons] at hthis ⊢
              omega
            rw [heqV, heqM,
                pathBlocked_snoc G Z (c :: vs'').reverse (reverseMarks ms') hlenP b a m2.flip m.flip,
                heqV2, heqM2, ihres, G.segmentBlocked_flip_swap Z b m m2, Bool.or_comm]
            rfl

@[simp] lemma isPath_nil (G : ADMG V) : G.IsPath [] [] := ⟨trivial, List.nodup_nil⟩
@[simp] lemma isPath_singleton (G : ADMG V) (v : V) : G.IsPath [v] [] :=
  ⟨trivial, List.nodup_singleton v⟩

lemma isPath_reverse (G : ADMG V) (P : List V) (M : List Mark)
    (h : G.IsPath P M) : G.IsPath P.reverse (reverseMarks M) :=
  ⟨validSteps_reverse G P M h.1, List.nodup_reverse.mpr h.2⟩

lemma pathBlocked_reverse (G : ADMG V) (Z : Finset V) (P : List V) (M : List Mark)
    (h : G.IsPath P M) : G.pathBlocked Z P.reverse (reverseMarks M) = G.pathBlocked Z P M :=
  validSteps_blocked_reverse G Z P M h.1

/-- Separation quantifies over both vertices and chosen edges of simple paths.
Endpoints are not tested for blocking, including singleton paths. -/
def dSep (G : ADMG V) (X Y : V) (Z : Finset V) : Prop :=
  ∀ P M, G.IsPath P M → P.head? = some X → P.getLast? = some Y →
    G.pathBlocked Z P M = true

def dConnected (G : ADMG V) (X Y : V) (Z : Finset V) : Prop :=
  ∃ P M, G.IsPath P M ∧ P.head? = some X ∧ P.getLast? = some Y ∧
    G.pathBlocked Z P M = false

def dSepSet (G : ADMG V) (X Y Z : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, G.dSep x y Z

theorem dConnected_iff_not_dSep (G : ADMG V) (X Y : V) (Z : Finset V) :
    G.dConnected X Y Z ↔ ¬ G.dSep X Y Z := by
  simp only [dConnected, dSep, not_forall, Bool.not_eq_true, exists_prop]

/-- The collider-opening condition uses only directed descendants. -/
abbrev hasReflDescIn (G : ADMG V) := G.toDAG.hasReflDescIn

lemma hasReflDescIn_union (G : ADMG V) (v : V) (Z W : Finset V) :
    G.hasReflDescIn v (Z ∪ W) ↔ G.hasReflDescIn v Z ∨ G.hasReflDescIn v W :=
  G.toDAG.hasReflDescIn_union v Z W

lemma collider_seg_false_iff (G : ADMG V) (Z : Finset V) (v : V) (m n : Mark)
    (hc : isCollider m n = true) :
    G.segmentBlocked Z v m n = false ↔ G.hasReflDescIn v Z := by
  unfold segmentBlocked hasReflDescIn DAG.hasReflDescIn
  rw [if_pos hc, Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]

lemma noncollider_seg_false_iff (G : ADMG V) (Z : Finset V) (v : V) (m n : Mark)
    (hc : isCollider m n = false) : G.segmentBlocked Z v m n = false ↔ v ∉ Z := by
  simp [segmentBlocked, hc]

private lemma validSteps_split (G : ADMG V) (A : List V) (v : V) (C : List V)
    (MA MC : List Mark) (hlen : MA.length = A.length) :
    G.ValidSteps (A ++ v :: C) (MA ++ MC) ↔
      G.ValidSteps (A ++ [v]) MA ∧ G.ValidSteps (v :: C) MC := by
  induction A generalizing MA with
  | nil => have : MA = [] := List.length_eq_zero_iff.mp hlen; subst MA; simp
  | cons a A ih =>
      cases MA with
      | nil => simp at hlen
      | cons m MA =>
          have hn : MA.length = A.length := by simpa using hlen
          cases A with
          | nil =>
              have : MA = [] := List.length_eq_zero_iff.mp hn
              subst MA
              simp [ValidSteps]
          | cons b A =>
              change (Mark.valid G a b m = true ∧ G.ValidSteps ((b :: A) ++ v :: C) (MA ++ MC)) ↔ _
              rw [ih MA hn]
              exact and_assoc.symm

lemma isPath_prefix (G : ADMG V) (A : List V) (v : V) (C : List V)
    (MA MC : List Mark) (hlen : MA.length = A.length)
    (hp : G.IsPath (A ++ v :: C) (MA ++ MC)) : G.IsPath (A ++ [v]) MA := by
  have hpre : A ++ [v] <+: A ++ v :: C := ⟨C, by simp⟩
  exact ⟨((validSteps_split G A v C MA MC hlen).mp hp.1).1,
    hp.2.sublist hpre.sublist⟩

private lemma pathBlocked_tail (G : ADMG V) (Z : Finset V) (a : V) (P : List V)
    (m : Mark) (M : List Mark) (h : G.pathBlocked Z (a :: P) (m :: M) = false) :
    G.pathBlocked Z P M = false := by
  cases P with
  | nil => rfl
  | cons b P => cases P with
    | nil => rfl
    | cons c P => cases M with
      | nil => cases P <;> rfl
      | cons n M => exact (Bool.or_eq_false_iff.mp h).2

private lemma pathBlocked_suffix (G : ADMG V) (Z : Finset V)
    (A P : List V) (MA M : List Mark) (hlen : MA.length = A.length)
    (h : G.pathBlocked Z (A ++ P) (MA ++ M) = false) : G.pathBlocked Z P M = false := by
  induction A generalizing MA with
  | nil => have : MA = [] := List.length_eq_zero_iff.mp hlen; subst MA; exact h
  | cons a A ih =>
      cases MA with
      | nil => simp at hlen
      | cons m MA =>
          exact ih MA (by simpa using hlen) (pathBlocked_tail G Z a _ m _ h)

private lemma pathBlocked_prefix (G : ADMG V) (Z : Finset V)
    (A : List V) (v : V) (C : List V) (MA MC : List Mark) (hlen : MA.length = A.length)
    (h : G.pathBlocked Z (A ++ v :: C) (MA ++ MC) = false) :
    G.pathBlocked Z (A ++ [v]) MA = false := by
  induction A generalizing MA with
  | nil => rfl
  | cons a A ih =>
      cases A with
      | nil => rfl
      | cons b A =>
          cases MA with
          | nil => simp at hlen
          | cons m MA =>
              have hn : MA.length = A.length + 1 := by simpa using hlen
              cases MA with
              | nil => simp at hn
              | cons n MA =>
                  have hh : (A ++ [v]) ≠ [] := by simp
                  have hh' : (A ++ v :: C) ≠ [] := by simp
                  simp only [List.cons_append] at h ⊢
                  rw [pathBlocked_cons_cons_of_ne G Z a b m _ _ hh'] at h
                  rw [pathBlocked_cons_cons_of_ne G Z a b m _ _ hh]
                  simp only [List.head?_cons, Option.map_some,
                    Option.getD_some, Bool.or_eq_false_iff] at h ⊢
                  exact ⟨h.1, ih _ (by simpa using hn) h.2⟩

private lemma segmentBlocked_extract (G : ADMG V) (Z : Finset V)
    (A : List V) (a v b : V) (C : List V) (MA : List Mark) (m n : Mark) (MC : List Mark)
    (hlen : MA.length = A.length)
    (h : G.pathBlocked Z (A ++ a :: v :: b :: C) (MA ++ m :: n :: MC) = false) :
    G.segmentBlocked Z v m n = false :=
  (Bool.or_eq_false_iff.mp (pathBlocked_suffix G Z A _ MA _ hlen h)).1

/-- Find the first blocked interior vertex, retaining its incoming and outgoing marks. -/
private lemma first_blocked_segment (G : ADMG V) (Z : Finset V) :
    ∀ (P : List V) (M : List Mark), G.pathBlocked Z P M = true →
      ∃ (A : List V) (a v b : V) (C : List V) (MA : List Mark) (m n : Mark) (MC : List Mark),
        P = A ++ a :: v :: b :: C ∧ M = MA ++ m :: n :: MC ∧ MA.length = A.length ∧
        G.pathBlocked Z (A ++ [a, v]) (MA ++ [m]) = false ∧
        G.segmentBlocked Z v m n = true := by
  intro P M
  match P, M with
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _, [] | _ :: _ :: _ :: _, [_] =>
      intro h; contradiction
  | a :: b :: c :: L, m :: n :: MS =>
      intro hb
      by_cases hs : G.segmentBlocked Z b m n = true
      · exact ⟨[], a, b, c, L, [], m, n, MS, rfl, rfl, rfl, rfl, hs⟩
      · have hsf : G.segmentBlocked Z b m n = false := by simpa using hs
        have ht : G.pathBlocked Z (b :: c :: L) (n :: MS) = true := by
          change (G.segmentBlocked Z b m n || G.pathBlocked Z (b :: c :: L) (n :: MS)) = true at hb
          simpa only [hsf, Bool.false_or] using hb
        obtain ⟨A, p, q, r, C, MA, i, j, MC, heq, hmeq, hlen, hpre, hseg⟩ :=
          first_blocked_segment G Z (b :: c :: L) (n :: MS) ht
        refine ⟨a :: A, p, q, r, C, m :: MA, i, j, MC, ?_, ?_, ?_, ?_, hseg⟩
        · simp only [List.cons_append]; rw [heq]
        · simp only [List.cons_append]; rw [hmeq]
        · simpa using hlen
        · cases A with
          | nil =>
              have : MA = [] := List.length_eq_zero_iff.mp hlen
              subst MA
              simp only [List.nil_append, List.cons.injEq] at heq hmeq
              simp only [List.cons_append, List.nil_append, pathBlocked]
              simpa only [← heq.1, ← hmeq.1, Bool.or_false] using hsf
          | cons d A =>
              cases MA with
              | nil => simp at hlen
              | cons k MA =>
                  have hd : d = b := by simpa using (congrArg List.head? heq).symm
                  have hk : k = n := by simpa using (congrArg List.head? hmeq).symm
                  simp only [List.cons_append] at hpre ⊢
                  rw [pathBlocked_cons_cons_of_ne G Z a d m _ _ (by simp)]
                  simp only [List.head?_cons, Option.map_some, Option.getD_some, hd, hk]
                  exact Bool.or_eq_false_iff.mpr ⟨hsf, by simpa only [hd, hk] using hpre⟩
  termination_by P => P.length
  decreasing_by simp_wf

private lemma prefix_marks_length (G : ADMG V) (A : List V) (v : V) (C : List V)
    (M : List Mark) (hp : G.IsPath (A ++ v :: C) M) :
    (M.take A.length).length = A.length := by
  have hl := validSteps_length' G hp.1 (by simp)
  simp only [List.length_append, List.length_cons] at hl
  simp only [List.length_take]
  omega

private lemma isPath_prefix_take (G : ADMG V) (A : List V) (v : V) (C : List V)
    (M : List Mark) (hp : G.IsPath (A ++ v :: C) M) :
    G.IsPath (A ++ [v]) (M.take A.length) := by
  apply isPath_prefix G A v C _ (M.drop A.length) (prefix_marks_length G A v C M hp)
  simpa using hp

private lemma not_self_descendant (G : ADMG V) (v : V) : v ∉ G.descendants v := by
  intro h
  have ht : G.toDAG.canReach v v = true := decide_eq_true h
  rw [G.toDAG.canReach_self v] at ht
  contradiction

/-- Every vertex after the first on a directed chain is a descendant. -/
private lemma mem_directed_chain_descendant (G : ADMG V) :
    ∀ (L : List V) (a b : V), (a :: L).IsChain (fun u v => G.hasEdge u v = true) →
      b ∈ L → b ∈ G.descendants a := by
  intro L
  induction L with
  | nil => intro a b _ hb; simp at hb
  | cons c L ih =>
      intro a b hd hb
      obtain ⟨hac, ht⟩ := List.isChain_cons_cons.mp hd
      rcases List.mem_cons.mp hb with rfl | hb
      · exact DAG.hasEdge_mem_descendants G.toDAG hac
      · exact DAG.descendants_trans G.toDAG (DAG.hasEdge_mem_descendants G.toDAG hac) (ih c b ht hb)

/-- A directed chain in a DAG cannot repeat a vertex. -/
private lemma directed_chain_nodup (G : ADMG V) :
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
private lemma directed_chain_of_reachable (G : ADMG V) :
    ∀ (n : ℕ) (a b : V), b ∈ G.reachableN n a →
      ∃ L : List V, (a :: L).IsChain (fun u v => G.hasEdge u v = true) ∧
        (a :: L).getLast? = some b := by
  intro n
  induction n with
  | zero => intro a b hb; simp at hb
  | succ n ih =>
      intro a b hb
      rcases (DAG.mem_reachableN_succ G.toDAG n a b).mp hb with hab | ⟨c, hac, hcb⟩
      · exact ⟨[b], List.isChain_cons_cons.mpr
          ⟨(DAG.mem_outNeighbors G.toDAG a b).mp hab, List.isChain_singleton b⟩, rfl⟩
      · obtain ⟨L, hd, hl⟩ := ih c b hcb
        exact ⟨c :: L, List.isChain_cons_cons.mpr ⟨(DAG.mem_outNeighbors G.toDAG a c).mp hac, hd⟩,
          by simpa using hl⟩

private lemma directed_chain_valid (G : ADMG V) :
    ∀ (L : List V) (a : V), (a :: L).IsChain (fun u v => G.directed u v = true) →
      G.ValidSteps (a :: L) (List.replicate L.length Mark.dirFwd) := by
  intro L
  induction L with
  | nil => intro a _; trivial
  | cons b L ih =>
      intro a hd
      exact ⟨(List.isChain_cons_cons.mp hd).1, ih b hd.tail⟩

private lemma directed_chain_active (G : ADMG V) (Z : Finset V) :
    ∀ (L : List V) (a : V), (∀ v ∈ a :: L, v ∉ Z) →
      G.pathBlocked Z (a :: L) (List.replicate L.length Mark.dirFwd) = false := by
  intro L
  induction L with
  | nil => intro _ _; rfl
  | cons b L ih =>
      intro a hz
      cases L with
      | nil => rfl
      | cons c L =>
          exact Bool.or_eq_false_iff.mpr
            ⟨segmentBlocked_chain G Z b _ (hz b (by simp)),
              ih b (fun v hv => hz v (by simp [hv]))⟩

private lemma pathBlocked_append_directed (G : ADMG V) (Z : Finset V)
    (A : List V) (v : V) (R : List V) (MA : List Mark) (hlen : MA.length = A.length)
    (hp : G.pathBlocked Z (A ++ [v]) MA = false)
    (hz : ∀ u ∈ v :: R, u ∉ Z) :
    G.pathBlocked Z (A ++ v :: R) (MA ++ List.replicate R.length Mark.dirFwd) = false := by
  induction A generalizing MA with
  | nil =>
      have : MA = [] := List.length_eq_zero_iff.mp hlen
      subst MA
      exact directed_chain_active G Z R v hz
  | cons a A ih =>
      cases MA with
      | nil => simp at hlen
      | cons m MA =>
          have hn : MA.length = A.length := by simpa using hlen
          cases A with
          | nil =>
              have : MA = [] := List.length_eq_zero_iff.mp hn
              subst MA
              cases R with
              | nil => rfl
              | cons b R =>
                  exact Bool.or_eq_false_iff.mpr
                    ⟨segmentBlocked_chain G Z v m (hz v (by simp)),
                      directed_chain_active G Z (b :: R) v hz⟩
          | cons b A =>
              cases MA with
              | nil => simp at hn
              | cons n MA =>
                  simp only [List.cons_append] at hp ⊢
                  rw [pathBlocked_cons_cons_of_ne G Z a b m _ _ (by simp)] at hp ⊢
                  simp only [List.head?_cons, Option.map_some,
                    Option.getD_some, Bool.or_eq_false_iff] at hp ⊢
                  exact ⟨hp.1, ih _ hn hp.2⟩

/-- Resolve overlaps by cutting the original simple prefix and shortening the
remaining directed continuation. The mark at the splice is always `dirFwd`. -/
private lemma splice_directed_path (G : ADMG V) (Z : Finset V) :
    ∀ (A : List V) (v : V) (R : List V) (MA : List Mark), G.IsPath (A ++ [v]) MA →
      G.pathBlocked Z (A ++ [v]) MA = false →
      (v :: R).IsChain (fun a b => G.directed a b = true) →
      (∀ u ∈ v :: R, u ∉ Z) →
      ∃ (P : List V) (M : List Mark), G.IsPath P M ∧ P.head? = (A ++ [v]).head? ∧
        P.getLast? = (v :: R).getLast? ∧ G.pathBlocked Z P M = false := by
  intro A v R MA hp hb hd hz
  by_cases hover : ∃ u, u ∈ R ∧ u ∈ A ++ [v]
  · obtain ⟨u, huR, huA⟩ := hover
    obtain ⟨B, C, hR⟩ := List.append_of_mem huR
    obtain ⟨A', E, hA⟩ := List.append_of_mem huA
    have hp' := isPath_prefix_take G A' u E MA (hA ▸ hp)
    have hb' := pathBlocked_prefix G Z A' u E (MA.take A'.length) (MA.drop A'.length)
      (prefix_marks_length G A' u E MA (hA ▸ hp)) (by simpa only [List.take_append_drop] using hA ▸ hb)
    have hd' : (u :: C).IsChain (fun a b => G.directed a b = true) := by
      apply List.IsChain.right_of_append (l₁ := v :: B)
      simpa only [hR, List.cons_append] using hd
    have hz' : ∀ w ∈ u :: C, w ∉ Z := by
      intro w hw
      apply hz w
      simp only [hR, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (List.mem_cons.mp hw))
    obtain ⟨P, M, hP, hh, hl, hactive⟩ :=
      splice_directed_path G Z A' u C _ hp' hb' hd' hz'
    refine ⟨P, M, hP, ?_, ?_, hactive⟩
    · rw [hh, hA]; cases A' <;> rfl
    · rw [hl, hR]
      exact (List.getLast?_append_of_ne_nil (v :: B) (by simp : u :: C ≠ [])).symm
  · have hlen : MA.length = A.length := by
      have h := validSteps_length' G hp.1 (by simp)
      simpa using h
    refine ⟨A ++ v :: R, MA ++ List.replicate R.length Mark.dirFwd, ?_, ?_, ?_,
      pathBlocked_append_directed G Z A v R MA hlen hb hz⟩
    · refine ⟨(validSteps_split G A v R _ _ hlen).mpr
        ⟨hp.1, directed_chain_valid G R v hd⟩, ?_⟩
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

/-- An active simple path to `Y` given `Z ∪ W` supplies an active simple path
with the same head to `Y ∪ W` given `Z`. Newly blocked colliders are truncated
or spliced to a directed descendant in `W`, resolving every overlap. -/
theorem active_path_lemma (G : ADMG V) (Y W Z : Finset V) (P : List V) (M : List Mark) (y : V)
    (hp : G.IsPath P M) (hl : P.getLast? = some y) (hy : y ∈ Y)
    (hb : G.pathBlocked (Z ∪ W) P M = false) :
    ∃ (Q : List V) (N : List Mark) (b : V), G.IsPath Q N ∧ Q.getLast? = some b ∧ b ∈ Y ∪ W ∧
      G.pathBlocked Z Q N = false ∧ Q.head? = P.head? := by
  by_cases hZ : G.pathBlocked Z P M = false
  · exact ⟨P, M, y, hp, hl, Finset.mem_union.mpr (.inl hy), hZ, rfl⟩
  · have hZtrue : G.pathBlocked Z P M = true := by simpa using hZ
    obtain ⟨A, a, v, b, C, MA, m, n, MC, rfl, rfl, hlen, hpre, hseg⟩ :=
      first_blocked_segment G Z P M hZtrue
    have hp' : G.IsPath (A ++ [a, v]) (MA ++ [m]) := by
      simpa using isPath_prefix G (A ++ [a]) v (b :: C) (MA ++ [m]) (n :: MC)
        (by simpa using hlen) (by simpa using hp)
    have hh' : (A ++ [a, v]).head? = (A ++ a :: v :: b :: C).head? := by
      cases A <;> rfl
    have hsU := segmentBlocked_extract G (Z ∪ W) A a v b C MA m n MC hlen hb
    by_cases hc : isCollider m n = true
    · have hnoZ : ¬ G.hasReflDescIn v Z := by
        intro hv
        have hf := (collider_seg_false_iff G Z v m n hc).mpr hv
        rw [hf] at hseg
        contradiction
      have hW : G.hasReflDescIn v W := by
        have hU := (collider_seg_false_iff G (Z ∪ W) v m n hc).mp hsU
        exact ((hasReflDescIn_union G v Z W).mp hU).resolve_left hnoZ
      rcases hW with hvW | ⟨w, hw⟩
      · refine ⟨A ++ [a, v], MA ++ [m], v, hp', ?_,
          Finset.mem_union.mpr (.inr hvW), hpre, hh'⟩
        simp [List.getLast?_append, List.getLast?_cons]
      · obtain ⟨hwdesc, hwW⟩ := Finset.mem_inter.mp hw
        obtain ⟨R, hd, hlast⟩ := directed_chain_of_reachable G (Fintype.card V) v w hwdesc
        have hz : ∀ u ∈ v :: R, u ∉ Z := by
          intro u hu huZ
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hnoZ (Or.inl huZ)
          · exact hnoZ (Or.inr ⟨u, Finset.mem_inter.mpr
              ⟨mem_directed_chain_descendant G R v u hd hu, huZ⟩⟩)
        obtain ⟨Q, N, hQ, hhead, hlast', hactive⟩ :=
          splice_directed_path G Z (A ++ [a]) v R (MA ++ [m])
            (by simpa using hp') (by simpa using hpre) hd hz
        refine ⟨Q, N, w, hQ, hlast'.trans hlast, Finset.mem_union.mpr (.inr hwW), hactive, ?_⟩
        exact hhead.trans (by simp only [List.append_assoc, List.singleton_append]; exact hh')
    · have hcf : isCollider m n = false := by simpa using hc
      have hvZ : v ∈ Z := by simpa [segmentBlocked, hcf] using hseg
      have hvU := (noncollider_seg_false_iff G (Z ∪ W) v m n hcf).mp hsU
      exact False.elim (hvU (Finset.mem_union.mpr (.inl hvZ)))

/-- Enlarging the conditioning set either preserves activity, or exposes a
strictly shorter active simple prefix ending at a newly conditioned non-collider. -/
theorem contraction_path (G : ADMG V) (Y Z : Finset V) (P : List V) (M : List Mark)
    (hp : G.IsPath P M) (hb : G.pathBlocked Z P M = false) :
    G.pathBlocked (Z ∪ Y) P M = false ∨
      ∃ (Q : List V) (N : List Mark) (y : V), G.IsPath Q N ∧ Q.head? = P.head? ∧ Q.getLast? = some y ∧
        y ∈ Y ∧ G.pathBlocked Z Q N = false ∧ Q <+: P ∧ Q.length < P.length := by
  by_cases hU : G.pathBlocked (Z ∪ Y) P M = false
  · exact Or.inl hU
  · have hUtrue : G.pathBlocked (Z ∪ Y) P M = true := by simpa using hU
    obtain ⟨A, a, v, b, C, MA, m, n, MC, rfl, rfl, hlen, _, hsU⟩ :=
      first_blocked_segment G (Z ∪ Y) P M hUtrue
    have hsZ := segmentBlocked_extract G Z A a v b C MA m n MC hlen hb
    have hcf : isCollider m n = false := by
      by_contra hc
      have hct : isCollider m n = true := by simpa using hc
      have hvZ := (collider_seg_false_iff G Z v m n hct).mp hsZ
      have hvU := (hasReflDescIn_union G v Z Y).mpr (Or.inl hvZ)
      have hf := (collider_seg_false_iff G (Z ∪ Y) v m n hct).mpr hvU
      rw [hf] at hsU
      contradiction
    have hvU : v ∈ Z ∪ Y := by simpa [segmentBlocked, hcf] using hsU
    have hvZ := (noncollider_seg_false_iff G Z v m n hcf).mp hsZ
    have hvY := (Finset.mem_union.mp hvU).resolve_left hvZ
    refine Or.inr ⟨A ++ [a, v], MA ++ [m], v, ?_, ?_, ?_, hvY, ?_, ?_, ?_⟩
    · simpa using isPath_prefix G (A ++ [a]) v (b :: C) (MA ++ [m]) (n :: MC)
        (by simpa using hlen) (by simpa using hp)
    · cases A <;> rfl
    · simp [List.getLast?_append, List.getLast?_cons]
    · simpa using pathBlocked_prefix G Z (A ++ [a]) v (b :: C) (MA ++ [m]) (n :: MC)
        (by simpa using hlen) (by simpa using hb)
    · exact ⟨b :: C, by simp⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- **Intersection helper.**  An active path given `Z` ending in `Y ∪ W` can be
    re-routed (by alternately applying `contraction_path` to `W` and to `Y`) into
    either an active path to `Y` given `Z ∪ W`, or an active path to `W` given
    `Z ∪ Y`, with the same head.  The alternation terminates because each
    `contraction_path` cut produces a strictly shorter path. -/
theorem intersection_path (G : ADMG V) (Y W Z : Finset V) :
    ∀ (π : List V) (M : List Mark) (t : V), G.IsPath π M → G.pathBlocked Z π M = false →
      π.getLast? = some t → t ∈ Y ∪ W →
      (∃ (πa : List V) (Ma : List Mark) (a : V), G.IsPath πa Ma ∧ πa.head? = π.head? ∧
          πa.getLast? = some a ∧ a ∈ Y ∧ G.pathBlocked (Z ∪ W) πa Ma = false) ∨
      (∃ (πb : List V) (Mb : List Mark) (b : V), G.IsPath πb Mb ∧ πb.head? = π.head? ∧
          πb.getLast? = some b ∧ b ∈ W ∧ G.pathBlocked (Z ∪ Y) πb Mb = false) := by
  intro π M t hpath hactive hlast htYW
  rcases Finset.mem_union.mp htYW with hY | hW
  · -- last node in Y: try to keep it active given Z ∪ W (enlarge by W).
    rcases contraction_path G W Z π M hpath hactive with
      hZW | ⟨π', M', w', hw', hhead', hlast', hw'W, hblk', _, hlen'⟩
    · exact Or.inl ⟨π, M, t, hpath, rfl, hlast, hY, hZW⟩
    · rcases intersection_path G Y W Z π' M' w' hw' hblk' hlast'
          (Finset.mem_union.mpr (Or.inr hw'W)) with
        ⟨πa, Ma, a, hwa, hha, hla, haY, hba⟩ | ⟨πb, Mb, b, hwb, hhb, hlb, hbW, hbb⟩
      · exact Or.inl ⟨πa, Ma, a, hwa, hha.trans hhead', hla, haY, hba⟩
      · exact Or.inr ⟨πb, Mb, b, hwb, hhb.trans hhead', hlb, hbW, hbb⟩
  · -- last node in W: try to keep it active given Z ∪ Y (enlarge by Y).
    rcases contraction_path G Y Z π M hpath hactive with
      hZY | ⟨π', M', y', hw', hhead', hlast', hy'Y, hblk', _, hlen'⟩
    · exact Or.inr ⟨π, M, t, hpath, rfl, hlast, hW, hZY⟩
    · rcases intersection_path G Y W Z π' M' y' hw' hblk' hlast'
          (Finset.mem_union.mpr (Or.inl hy'Y)) with
        ⟨πa, Ma, a, hwa, hha, hla, haY, hba⟩ | ⟨πb, Mb, b, hwb, hhb, hlb, hbW, hbb⟩
      · exact Or.inl ⟨πa, Ma, a, hwa, hha.trans hhead', hla, haY, hba⟩
      · exact Or.inr ⟨πb, Mb, b, hwb, hhb.trans hhead', hlb, hbW, hbb⟩
  termination_by π => π.length
  decreasing_by all_goals omega

/-- Symmetry of simple-path d-separation. -/
theorem dSep_symm (G : ADMG V) (X Y : V) (Z : Finset V)
    (h : G.dSep X Y Z) : G.dSep Y X Z := by
  intro P M hp hh hl
  rw [← pathBlocked_reverse G Z P M hp]
  exact h P.reverse (reverseMarks M) (isPath_reverse G P M hp)
    (by simpa using hl) (by simpa using hh)

theorem dSepSet_symm (G : ADMG V) (X Y Z : Finset V) :
    G.dSepSet X Y Z ↔ G.dSepSet Y X Z := by
  constructor
  · intro h y hy x hx; exact dSep_symm G x y Z (h x hx y hy)
  · intro h x hx y hy; exact dSep_symm G y x Z (h y hy x hx)

theorem dSepSet_decomp (G : ADMG V) (X Y W Z : Finset V) :
    G.dSepSet X (Y ∪ W) Z → G.dSepSet X Y Z ∧ G.dSepSet X W Z := by
  intro h
  exact ⟨fun x hx y hy => h x hx y (Finset.mem_union.mpr (.inl hy)),
    fun x hx w hw => h x hx w (Finset.mem_union.mpr (.inr hw))⟩

/-- One direction of Weak Union, proved by the contrapositive through the
    Active Path Lemma: an active simple path from `X` to `Y` given `Z ∪ W` yields an
    active simple path from `X` to `Y ∪ W` given `Z`, contradicting `X ⊥ Y ∪ W | Z`. -/
private lemma weak_union_path_half (G : ADMG V) (X Y W Z : Finset V)
    (h : G.dSepSet X (Y ∪ W) Z) : G.dSepSet X Y (Z ∪ W) := by
  intro x hx y hy π M hpath hhead hlast
  by_contra hne
  rw [Bool.not_eq_true] at hne
  obtain ⟨π', M', b, hw', hlast', hb', hblk', hhead'⟩ :=
    active_path_lemma G Y W Z π M y hpath hlast hy hne
  have hxb : G.dSep x b Z := h x hx b hb'
  have hcontra : G.pathBlocked Z π' M' = true := hxb π' M' hw' (by rw [hhead', hhead]) hlast'
  rw [hblk'] at hcontra
  exact absurd hcontra (by simp)

/-- **Weak Union** for d-separation: X ⊥ Y ∪ W | Z → X ⊥ Y | Z ∪ W ∧ X ⊥ W | Z ∪ Y.
    Proved directly from the d-separation definition via Verma's Active Path
    Lemma (`active_path_lemma`). Both conjuncts
    follow from `weak_union_path_half`, the second by swapping the roles of Y and W. -/
theorem dSepSet_weak_union (G : ADMG V) (X Y W Z : Finset V) :
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
theorem dSepSet_contraction (G : ADMG V) (X Y W Z : Finset V) :
    G.dSepSet X Y Z → G.dSepSet X W (Z ∪ Y) → G.dSepSet X (Y ∪ W) Z := by
  intro h1 h2 x hx yw hyw
  rcases Finset.mem_union.mp hyw with hy | hw
  · exact h1 x hx yw hy
  · intro π M hpath hhead hlast
    by_contra hne
    rw [Bool.not_eq_true] at hne
    rcases contraction_path G Y Z π M hpath hne with
      hZY | ⟨π', M', y', hw', hhead', hlast', hyY, hblk', _, _⟩
    · have hc : G.pathBlocked (Z ∪ Y) π M = true := h2 x hx yw hw π M hpath hhead hlast
      rw [hZY] at hc; exact absurd hc (by simp)
    · have hc : G.pathBlocked Z π' M' = true :=
        h1 x hx y' hyY π' M' hw' (by rw [hhead', hhead]) hlast'
      rw [hblk'] at hc; exact absurd hc (by simp)

/-- **Intersection**: X ⊥ Y | Z ∪ W ∧ X ⊥ W | Z ∪ Y → X ⊥ Y ∪ W | Z.

    Unlike *probabilistic* independence (which needs strict positivity for
    Intersection), the graphical d-separation relation satisfies Intersection
    unconditionally — d-separation is a (compositional) graphoid.  An active simple path
    `x → (Y ∪ W)` given `Z` is re-routed by `intersection_path` into an active
    simple path to `Y` given `Z ∪ W` or to `W` given `Z ∪ Y`, contradicting one of the
    hypotheses; hence no such path exists. -/
theorem dSepSet_intersection (G : ADMG V) (X Y W Z : Finset V) :
    G.dSepSet X Y (Z ∪ W) → G.dSepSet X W (Z ∪ Y) → G.dSepSet X (Y ∪ W) Z := by
  intro h1 h2 x hx yw hyw π M hpath hhead hlast
  by_contra hne
  rw [Bool.not_eq_true] at hne
  rcases intersection_path G Y W Z π M yw hpath hne hlast hyw with
    ⟨πa, Ma, a, hwa, hheada, hlasta, haY, hblka⟩ | ⟨πb, Mb, b, hwb, hheadb, hlastb, hbW, hblkb⟩
  · have hc : G.pathBlocked (Z ∪ W) πa Ma = true :=
      h1 x hx a haY πa Ma hwa (by rw [hheada, hhead]) hlasta
    rw [hblka] at hc; exact absurd hc (by simp)
  · have hc : G.pathBlocked (Z ∪ Y) πb Mb = true :=
      h2 x hx b hbW πb Mb hwb (by rw [hheadb, hhead]) hlastb
    rw [hblkb] at hc; exact absurd hc (by simp)

/-- All four semigraphoid axioms for simple-path d-separation. -/
theorem dSep_semigraphoid (G : ADMG V) :
    (∀ X Y Z : Finset V, G.dSepSet X Y Z ↔ G.dSepSet Y X Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X (Y ∪ W) Z → G.dSepSet X Y Z ∧ G.dSepSet X W Z) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X (Y ∪ W) Z →
      G.dSepSet X Y (Z ∪ W) ∧ G.dSepSet X W (Z ∪ Y)) ∧
    (∀ X Y W Z : Finset V, G.dSepSet X Y Z → G.dSepSet X W (Z ∪ Y) →
      G.dSepSet X (Y ∪ W) Z) :=
  ⟨dSepSet_symm G, dSepSet_decomp G, dSepSet_weak_union G, dSepSet_contraction G⟩

/-- All five graphoid axioms hold for d-separation over simple paths. -/
theorem dSep_full_graphoid (G : ADMG V) :
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

end ADMG
namespace DAG

/-- Embed a DAG with no bidirected edges. -/
def toADMG (D : DAG V) : ADMG V where
  toDAG := D
  bidirected := fun _ _ => false
  bid_no_loop := fun _ => rfl
  bid_symm := fun _ _ => rfl

open ADMG (Mark)

/-- The unique valid mark for an edge of the embedded DAG. -/
def toADMGMark (D : DAG V) (a b : V) : Mark :=
  if D.hasEdge a b then Mark.dirFwd else Mark.dirBack

/-- Canonical marks for a vertex sequence in a DAG. -/
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

private lemma toADMG_chain (D : DAG V) : ∀ l : List V, l.IsChain D.Adj →
    D.toADMG.ValidSteps l (D.toADMGMarks l)
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, h => by
      rw [List.isChain_cons_cons] at h
      exact ⟨toADMGMark_valid D h.1, toADMG_chain D (b :: l) h.2⟩

private lemma toADMG_marks_unique (D : DAG V) :
    ∀ (verts : List V) (marks : List Mark), D.toADMG.ValidSteps verts marks →
      marks = D.toADMGMarks verts := by
  intro verts
  induction verts with
  | nil => intro marks h; cases marks with
      | nil => rfl
      | cons m ms => exact absurd h (by simp [ADMG.ValidSteps])
  | cons a vs ih =>
    intro marks h
    cases vs with
    | nil => cases marks with
        | nil => rfl
        | cons m ms => exact absurd h (by simp [ADMG.ValidSteps])
    | cons b vs' =>
      cases marks with
      | nil => exact absurd h (by simp [ADMG.ValidSteps])
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
    ADMG.isCollider (D.toADMGMark a b) (D.toADMGMark b c) = D.isCollider a b c := by
  unfold ADMG.isCollider DAG.isCollider
  rw [toADMGMark_intoRight, toADMGMark_intoLeft D hbc]

lemma toADMG_descendants (D : DAG V) (v : V) :
    D.toADMG.descendants v = D.descendants v := rfl

lemma toADMG_segmentBlocked (D : DAG V) (Z : Finset V) {a b c : V} (hbc : D.Adj b c) :
    D.toADMG.segmentBlocked Z b (D.toADMGMark a b) (D.toADMGMark b c) = D.segmentBlocked Z a b c := by
  simp only [ADMG.segmentBlocked, DAG.segmentBlocked, toADMG_isCollider D hbc, toADMG_descendants]
  rfl

private lemma toADMG_chain_blocked (D : DAG V) (Z : Finset V) :
    ∀ l : List V, l.IsChain D.Adj → D.toADMG.pathBlocked Z l (D.toADMGMarks l) = D.pathBlocked Z l
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | a :: b :: c :: rest, hw => by
      rw [List.isChain_cons_cons] at hw
      obtain ⟨_, hw2⟩ := hw
      have hw2' := hw2
      rw [List.isChain_cons_cons] at hw2'
      obtain ⟨hbc, _⟩ := hw2'
      show (D.toADMG.segmentBlocked Z b (D.toADMGMark a b) (D.toADMGMark b c) ||
          D.toADMG.pathBlocked Z (b :: c :: rest) (D.toADMGMarks (b :: c :: rest)))
        = (D.segmentBlocked Z a b c || D.pathBlocked Z (b :: c :: rest))
      rw [toADMG_segmentBlocked D Z hbc, toADMG_chain_blocked D Z (b :: c :: rest) hw2]

private lemma toADMG_chain_recover (D : DAG V) :
    ∀ (verts : List V) (marks : List Mark), D.toADMG.ValidSteps verts marks → verts.IsChain D.Adj := by
  intro verts
  induction verts with
  | nil => intro _ _; exact List.isChain_nil
  | cons a vs ih =>
    intro marks h
    cases vs with
    | nil => exact List.isChain_singleton a
    | cons b vs' =>
      cases marks with
      | nil => exact absurd h (by simp [ADMG.ValidSteps])
      | cons m ms =>
        obtain ⟨hvalid, htail⟩ := h
        rw [List.isChain_cons_cons]
        refine ⟨?_, ih ms htail⟩
        unfold Mark.valid at hvalid
        cases m with
        | dirFwd => exact Or.inl hvalid
        | dirBack => exact Or.inr hvalid
        | bidir => simp [toADMG] at hvalid

/-- Canonical marks turn every DAG simple path into an ADMG simple path. -/
lemma toADMG_isPath (D : DAG V) (P : List V) (h : D.IsPath P) :
    D.toADMG.IsPath P (D.toADMGMarks P) := ⟨toADMG_chain D P h.1, h.2⟩

lemma toADMG_isPath_recover (D : DAG V) (P : List V) (M : List Mark)
    (h : D.toADMG.IsPath P M) : D.IsPath P := ⟨toADMG_chain_recover D P M h.1, h.2⟩

lemma toADMG_pathBlocked (D : DAG V) (Z : Finset V) (P : List V) (M : List Mark)
    (h : D.toADMG.IsPath P M) : D.toADMG.pathBlocked Z P M = D.pathBlocked Z P := by
  rw [toADMG_marks_unique D P M h.1]
  exact toADMG_chain_blocked D Z P (toADMG_chain_recover D P M h.1)

/-- Marked simple-path separation on the embedding agrees with DAG separation. -/
@[simp] theorem toADMG_dSep_iff (D : DAG V) (X Y : V) (Z : Finset V) :
    D.toADMG.dSep X Y Z ↔ D.dSep X Y Z := by
  constructor
  · intro h P hp hh hl
    rw [← toADMG_chain_blocked D Z P hp.1]
    exact h P (D.toADMGMarks P) (toADMG_isPath D P hp) hh hl
  · intro h P M hp hh hl
    rw [toADMG_pathBlocked D Z P M hp]
    exact h P (toADMG_isPath_recover D P M hp) hh hl

@[simp] theorem toADMG_dSepSet_iff (D : DAG V) (X Y Z : Finset V) :
    D.toADMG.dSepSet X Y Z ↔ D.dSepSet X Y Z := by
  simp only [ADMG.dSepSet, DAG.dSepSet, toADMG_dSep_iff]

@[simp] theorem toADMG_dConnected_iff (D : DAG V) (X Y : V) (Z : Finset V) :
    D.toADMG.dConnected X Y Z ↔ D.dConnected X Y Z := by
  rw [ADMG.dConnected_iff_not_dSep, DAG.dConnected_iff_not_dSep, toADMG_dSep_iff]

end DAG

end CausalLib

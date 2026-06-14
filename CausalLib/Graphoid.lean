-- ─────────────────────────────────────────────────────────────────────────────
-- Graphoid.lean
-- Formal definition of dependency models and the graphoid axioms in Lean 4.
--
-- Reference: Pearl (1988), Studený (2005)
-- ─────────────────────────────────────────────────────────────────────────────

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace CausalLib

-- ─────────────────────────────────────────────────────────────────────────────
-- §1. Dependency Model
-- ─────────────────────────────────────────────────────────────────────────────

-- V is the type of variables (nodes in the graph).
-- We work with Finset V for all variable sets X, Y, Z, W.
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An independence predicate over sets of variables.
    `I X Z Y` reads: "X is independent of Y given Z".
    X, Y, Z are disjoint sets of variables from V. -/
def IndependencePredicate (V : Type*) :=
  Finset V → Finset V → Finset V → Prop

/-- A dependency model M is a set of triplets (X, Z, Y) for which
    the independence predicate I(X, Z, Y) holds.
    We represent it as a function I : Finset V → Finset V → Finset V → Prop. -/
structure DependencyModel (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The independence predicate: I X Z Y means X ⊥ Y | Z -/
  I : Finset V → Finset V → Finset V → Prop


-- ─────────────────────────────────────────────────────────────────────────────
-- §2. The Five Graphoid Axioms
-- ─────────────────────────────────────────────────────────────────────────────

namespace DependencyModel

/-- AXIOM 1 — Symmetry
    I(X, Z, Y) ⟺ I(Y, Z, X)
    Independence is symmetric: if X is independent of Y given Z,
    then Y is independent of X given Z. -/
def AxiomSymmetry (M : DependencyModel V) : Prop :=
  ∀ (X Z Y : Finset V),
    M.I X Z Y ↔ M.I Y Z X

/-- AXIOM 2 — Decomposition
    I(X, Z, Y ∪ W) ⟹ I(X, Z, Y) ∧ I(X, Z, W)
    If X is independent of a larger set Y ∪ W given Z,
    then X is independent of each part individually. -/
def AxiomDecomposition (M : DependencyModel V) : Prop :=
  ∀ (X Z Y W : Finset V),
    M.I X Z (Y ∪ W) → M.I X Z Y ∧ M.I X Z W

/-- AXIOM 3 — Weak Union
    I(X, Z, Y ∪ W) ⟹ I(X, Z ∪ W, Y) ∧ I(X, Z ∪ Y, W)
    Learning irrelevant information W cannot make a previously
    independent Y relevant — conditioning on more can only help. -/
def AxiomWeakUnion (M : DependencyModel V) : Prop :=
  ∀ (X Z Y W : Finset V),
    M.I X Z (Y ∪ W) → M.I X (Z ∪ W) Y ∧ M.I X (Z ∪ Y) W

/-- AXIOM 4 — Contraction
    I(X, Z, Y) ∧ I(X, Z ∪ Y, W) ⟹ I(X, Z, Y ∪ W)
    The inverse of weak union: if W is irrelevant even after
    learning Y, then both Y and W are jointly irrelevant. -/
def AxiomContraction (M : DependencyModel V) : Prop :=
  ∀ (X Z Y W : Finset V),
    M.I X Z Y → M.I X (Z ∪ Y) W → M.I X Z (Y ∪ W)

/-- AXIOM 5 — Intersection
    I(X, Z ∪ W, Y) ∧ I(X, Z ∪ Y, W) ⟹ I(X, Z, Y ∪ W)
    If Y and W are each irrelevant when the other is known,
    then both are jointly irrelevant given Z alone.
    Note: this axiom holds for strictly positive distributions
    but NOT for all probability distributions. -/
def AxiomIntersection (M : DependencyModel V) : Prop :=
  ∀ (X Z Y W : Finset V),
    M.I X (Z ∪ W) Y → M.I X (Z ∪ Y) W → M.I X Z (Y ∪ W)


-- ─────────────────────────────────────────────────────────────────────────────
-- §3. Graphoid and Semi-graphoid
-- ─────────────────────────────────────────────────────────────────────────────

/-- A SEMI-GRAPHOID is a dependency model closed under the first four axioms:
    Symmetry, Decomposition, Weak Union, Contraction.
    Most probabilistic independence models are semi-graphoids.
    d-Separation in DAGs satisfies exactly these four axioms. -/
structure Semigraphoid (V : Type*) [Fintype V] [DecidableEq V]
    extends DependencyModel V where
  symmetry     : AxiomSymmetry     toDepMod
  decomp       : AxiomDecomposition toDepMod
  weak_union   : AxiomWeakUnion    toDepMod
  contraction  : AxiomContraction  toDepMod
where
  toDepMod : DependencyModel V := { I := I }

-- Note: the above `where` clause is a workaround — in practice
-- we unfold this directly. Here is the clean version:

/-- A SEMI-GRAPHOID (clean definition) -/
def isSemigraphoid (M : DependencyModel V) : Prop :=
  M.AxiomSymmetry   ∧
  M.AxiomDecomposition ∧
  M.AxiomWeakUnion  ∧
  M.AxiomContraction

/-- A GRAPHOID is a semi-graphoid that additionally satisfies Intersection.
    Graphoids correspond to independence models of strictly positive
    probability distributions. -/
def isGraphoid (M : DependencyModel V) : Prop :=
  isSemigraphoid M ∧ M.AxiomIntersection


-- ─────────────────────────────────────────────────────────────────────────────
-- §4. Consequences of the axioms
-- ─────────────────────────────────────────────────────────────────────────────

section Consequences

variable (M : DependencyModel V)

/-- From Symmetry + Decomposition:
    I(X, Z, Y ∪ W) ⟹ I(Y, Z, X) (via symmetry then decomposition) -/
lemma symm_decomp
    (hsymm  : M.AxiomSymmetry)
    (hdecomp : M.AxiomDecomposition)
    (X Z Y W : Finset V)
    (h : M.I X Z (Y ∪ W)) : M.I Y Z X := by
  exact (hsymm Y Z X).mpr ((hdecomp X Z Y W h).1 |> (hsymm X Z Y).mp)

/-- Decomposition gives left component -/
lemma decomp_left
    (hdecomp : M.AxiomDecomposition)
    (X Z Y W : Finset V)
    (h : M.I X Z (Y ∪ W)) : M.I X Z Y :=
  (hdecomp X Z Y W h).1

/-- Decomposition gives right component -/
lemma decomp_right
    (hdecomp : M.AxiomDecomposition)
    (X Z Y W : Finset V)
    (h : M.I X Z (Y ∪ W)) : M.I X Z W :=
  (hdecomp X Z Y W h).2

/-- Weak Union gives left component -/
lemma weak_union_left
    (hwu : M.AxiomWeakUnion)
    (X Z Y W : Finset V)
    (h : M.I X Z (Y ∪ W)) : M.I X (Z ∪ W) Y :=
  (hwu X Z Y W h).1

/-- Weak Union gives right component -/
lemma weak_union_right
    (hwu : M.AxiomWeakUnion)
    (X Z Y W : Finset V)
    (h : M.I X Z (Y ∪ W)) : M.I X (Z ∪ Y) W :=
  (hwu X Z Y W h).2

/-- Contraction + Weak Union are inverses:
    In a semi-graphoid, I(X,Z,Y∪W) ↔ I(X,Z,Y) ∧ I(X,Z∪Y,W) -/
theorem contraction_weak_union_iff
    (hsg : isSemigraphoid M)
    (X Z Y W : Finset V) :
    M.I X Z (Y ∪ W) ↔ M.I X Z Y ∧ M.I X (Z ∪ Y) W := by
  obtain ⟨hsymm, hdecomp, hwu, hcontr⟩ := hsg
  constructor
  · intro h
    exact ⟨decomp_left M hdecomp X Z Y W h,
           weak_union_right M hwu X Z Y W h⟩
  · intro ⟨h1, h2⟩
    exact hcontr X Z Y W h1 h2

end Consequences


-- ─────────────────────────────────────────────────────────────────────────────
-- §5. d-Separation is a semi-graphoid (statement)
-- ─────────────────────────────────────────────────────────────────────────────

-- We import DAG to access dSep and state the main theorem.
-- The proofs are the research — each is a sorry to be filled in.

/-- The d-separation model of a DAG:
    the independence predicate is exactly dSep. -/
def dSepModel (G : DAG V) : DependencyModel V where
  I := fun X Z Y =>
    ∀ x ∈ X, ∀ y ∈ Y, DAG.dSep G x y Z

/-- d-Separation satisfies Symmetry -/
theorem dSep_symmetry (G : DAG V) :
    (dSepModel G).AxiomSymmetry := by
  intro X Z Y
  simp [dSepModel]
  constructor
  · intro h x hx y hy
    exact (DAG.dSep_symm G y x Z (h y hy x hx))
  · intro h y hy x hx
    exact (DAG.dSep_symm G x y Z (h x hx y hy))

/-- d-Separation satisfies Decomposition -/
theorem dSep_decomposition (G : DAG V) :
    (dSepModel G).AxiomDecomposition := by
  intro X Z Y W h
  simp [dSepModel] at *
  constructor
  · intro x hx y hy
    exact h x hx y (Finset.mem_union_left W hy)
  · intro x hx w hw
    exact h x hx w (Finset.mem_union_right Y hw)

/-- d-Separation satisfies Weak Union -/
theorem dSep_weak_union (G : DAG V) :
    (dSepModel G).AxiomWeakUnion := by
  intro X Z Y W h
  simp [dSepModel] at *
  constructor
  · intro x hx y hy
    -- Conditioning on more (Z ∪ W) can only block more paths
    sorry
  · intro x hx w hw
    sorry

/-- d-Separation satisfies Contraction -/
theorem dSep_contraction (G : DAG V) :
    (dSepModel G).AxiomContraction := by
  intro X Z Y W h1 h2
  simp [dSepModel] at *
  intro x hx yw hyw
  rcases Finset.mem_union.mp hyw with hy | hw
  · exact h1 x hx yw hy
  · sorry

/-- d-Separation forms a semi-graphoid -/
theorem dSep_is_semigraphoid (G : DAG V) :
    isSemigraphoid (dSepModel G) :=
  ⟨dSep_symmetry G,
   dSep_decomposition G,
   dSep_weak_union G,
   dSep_contraction G⟩

/-- d-Separation does NOT generally satisfy Intersection
    (requires strictly positive distribution — a graph property alone
    is insufficient). -/
theorem dSep_not_graphoid_in_general :
    ∃ (G : DAG (Fin 4)),
      ¬ (dSepModel G).AxiomIntersection := by
  sorry
  -- Counterexample: a DAG where conditioning on a collider
  -- opens a path, violating intersection.


-- ─────────────────────────────────────────────────────────────────────────────
-- §6. m-Separation in MAGs is also a semi-graphoid (statement)
-- ─────────────────────────────────────────────────────────────────────────────

/-- The m-separation model of a MAG -/
def mSepModel (G : MAG V) : DependencyModel V where
  I := fun X Z Y =>
    ∀ x ∈ X, ∀ y ∈ Y, MAG.mSep G x y Z

/-- m-Separation satisfies Symmetry -/
theorem mSep_symmetry (G : MAG V) :
    (mSepModel G).AxiomSymmetry := by
  intro X Z Y
  simp [mSepModel]
  constructor
  · intro h x hx y hy
    exact MAG.mSep_symm G y x Z (h y hy x hx)
  · intro h y hy x hx
    exact MAG.mSep_symm G x y Z (h x hx y hy)

/-- m-Separation satisfies Decomposition -/
theorem mSep_decomposition (G : MAG V) :
    (mSepModel G).AxiomDecomposition := by
  intro X Z Y W h
  simp [mSepModel] at *
  exact ⟨fun x hx y hy => h x hx y (Finset.mem_union_left W hy),
         fun x hx w hw => h x hx w (Finset.mem_union_right Y hw)⟩

/-- m-Separation forms a semi-graphoid -/
theorem mSep_is_semigraphoid (G : MAG V) :
    isSemigraphoid (mSepModel G) := by
  refine ⟨mSep_symmetry G, mSep_decomposition G, ?_, ?_⟩
  · -- Weak Union
    intro X Z Y W h
    simp [mSepModel] at *
    exact ⟨fun x hx y hy => sorry, fun x hx w hw => sorry⟩
  · -- Contraction
    intro X Z Y W h1 h2
    simp [mSepModel] at *
    intro x hx yw hyw
    rcases Finset.mem_union.mp hyw with hy | hw
    · exact h1 x hx yw hy
    · sorry

end DependencyModel
end CausalLib

import CausalLib

/- Regression checks for the direct simple-path graphoid proofs. -/
namespace CausalLibTest

open CausalLib

-- General directed graphs admit cycles, and bounded reachability detects them.
private def twoCycle : DirectedGraph (Fin 2) where
  adj a b := decide (a ≠ b)
  no_self_loop := by decide

example : twoCycle.reachableN 0 0 = ∅ := by decide
example : twoCycle.reachableN 1 0 = {1} := by decide
example : twoCycle.reachableN 2 0 = {0, 1} := by decide
example : twoCycle.canReach 0 0 = true := by decide
example : twoCycle.canReach 1 1 = true := by decide

-- The same graph cannot underlie a DAG.
example : ¬ ∃ G : DAG (Fin 2), G.toDirectedGraph = twoCycle := by
  rintro ⟨G, hG⟩
  have h := G.acyclic 0
  rw [hG] at h
  have hcycle : twoCycle.canReach 0 0 = true := by decide
  rw [hcycle] at h
  contradiction

-- The continuation 1 → 2 → 4 meets the original path at its head, 2.
private def overlapHead : DAG (Fin 5) where
  adj a b := decide ((a = 0 ∧ (b = 1 ∨ b = 2)) ∨ (a = 3 ∧ b = 1) ∨
    (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 4))
  no_self_loop := by decide
  acyclic := by decide

example : overlapHead.pathBlocked ∅ [2, 0, 1, 3] = true := by decide
example : overlapHead.pathBlocked {4} [2, 0, 1, 3] = false := by decide

example : ∃ (P : List (Fin 5)) (b : Fin 5), overlapHead.IsPath P ∧
    P.getLast? = some b ∧ b ∈ ({3} ∪ {4} : Finset (Fin 5)) ∧
    overlapHead.pathBlocked ∅ P = false ∧ P.head? = some 2 := by
  exact DAG.active_path_lemma overlapHead {3} {4} ∅ [2, 0, 1, 3] 3
    (by unfold DAG.IsPath DAG.Adj; decide) rfl (by decide) (by decide)

-- The continuation 1 → 2 → 5 meets the original path at an interior vertex, 2.
private def overlapInterior : DAG (Fin 6) where
  adj a b := decide ((a = 0 ∧ (b = 1 ∨ b = 2)) ∨ (a = 2 ∧ (b = 3 ∨ b = 5)) ∨
    (a = 4 ∧ b = 1) ∨ (a = 1 ∧ b = 2))
  no_self_loop := by decide
  acyclic := by decide

example : overlapInterior.pathBlocked ∅ [3, 2, 0, 1, 4] = true := by decide
example : overlapInterior.pathBlocked {5} [3, 2, 0, 1, 4] = false := by decide

example : ∃ (P : List (Fin 6)) (b : Fin 6), overlapInterior.IsPath P ∧
    P.getLast? = some b ∧ b ∈ ({4} ∪ {5} : Finset (Fin 6)) ∧
    overlapInterior.pathBlocked ∅ P = false ∧ P.head? = some 3 := by
  exact DAG.active_path_lemma overlapInterior {4} {5} ∅ [3, 2, 0, 1, 4] 4
    (by unfold DAG.IsPath DAG.Adj; decide) rfl (by decide) (by decide)

private def chain : DAG (Fin 3) where
  adj a b := decide ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2))
  no_self_loop := by decide
  acyclic := by decide

-- Flat constructors and the existing DAG query names still work.
example : chain.hasEdge 0 1 = true := by decide
example : chain.outNeighbors 1 = {2} := by decide
example : chain.inNeighbors 1 = {0} := by decide
example : chain.canReach 0 2 = true := by decide
example : chain.canReach 0 0 = false := chain.canReach_self 0
example : chain.ancestors 2 = {0, 1} := by decide
example : chain.descendants 0 = {1, 2} := by decide
example : chain.toDirectedGraph.canReach 0 2 = true := by decide

-- Conditioning on the middle vertex produces a proper simple prefix.
example : ∃ (P : List (Fin 3)) (y : Fin 3), chain.IsPath P ∧
    P.head? = some 0 ∧ P.getLast? = some y ∧ y ∈ ({1} : Finset (Fin 3)) ∧
    chain.pathBlocked ∅ P = false ∧ P <+: [0, 1, 2] ∧ P.length < 3 := by
  have h := DAG.contraction_path chain {1} ∅ [0, 1, 2]
    (by unfold DAG.IsPath DAG.Adj; decide) (by decide)
  rcases h with h | h
  · have hf : chain.pathBlocked (∅ ∪ {1}) [0, 1, 2] = true := by decide
    rw [hf] at h
    contradiction
  · exact h

-- Intersection must shorten the path when enlarging the conditioning set blocks it.
example : (∃ (P : List (Fin 3)) (a : Fin 3), chain.IsPath P ∧ P.head? = some 0 ∧
      P.getLast? = some a ∧ a ∈ ({2} : Finset (Fin 3)) ∧ chain.pathBlocked {1} P = false) ∨
    (∃ (P : List (Fin 3)) (b : Fin 3), chain.IsPath P ∧ P.head? = some 0 ∧
      P.getLast? = some b ∧ b ∈ ({1} : Finset (Fin 3)) ∧ chain.pathBlocked {2} P = false) := by
  simpa using DAG.intersection_path chain {2} {1} ∅ [0, 1, 2] 2
    (by unfold DAG.IsPath DAG.Adj; decide) (by decide) rfl (by decide)

-- Singleton paths and empty sets retain their existing endpoint conventions.
example {V : Type*} [Fintype V] [DecidableEq V] (G : DAG V) (v : V) (Z : Finset V) :
    ¬ G.dSep v v Z := by
  intro h
  have hf := h [v] (DAG.isPath_singleton G v) rfl rfl
  contradiction

example {V : Type*} [Fintype V] [DecidableEq V] (G : DAG V) (Y Z : Finset V) :
    G.dSepSet ∅ Y Z := by
  intro x hx
  simp at hx

-- Audit the transitive project dependencies, including private helper proofs.
-- Separation declarations must belong to the direct simple-path API.
open Lean in
run_cmd do
  let env ← getEnv
  let mut todo := [``DAG.dSep_full_graphoid, ``DAG.dSep_semigraphoid]
  let directDeclarations := ["IsPath", "dSep", "dConnected", "dSepSet",
    "dConnected_iff_not_dSep", "dSep_symm", "dSepSet_symm", "dSepSet_decomp",
    "dSepSet_weak_union", "dSepSet_contraction", "dSepSet_intersection",
    "dSep_semigraphoid", "dSep_full_graphoid", "active_path_lemma",
    "contraction_path", "intersection_path"]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail
    unless seen.contains name do
      seen := seen.insert name
      let leaf := (name.toString.splitOn ".").getLast!
      let separationDeclaration := leaf.startsWith "Is" || leaf.startsWith "dSep" ||
        leaf.startsWith "dConnected" || leaf.startsWith "active_" ||
        leaf.startsWith "contraction_" || leaf.startsWith "intersection_"
      if (separationDeclaration && !directDeclarations.contains leaf) ||
          leaf == "chainBuild" || leaf.startsWith "excise_" ||
          leaf == "seam_unblocked" || leaf == "chain_or_ancestor" then
        throwError "Simple-path graphoid proof uses an unapproved dependency: {name}"
      if let some info := env.find? name then
        for expr in info.type :: (info.value? (allowOpaque := true)).toList do
          for dep in expr.getUsedConstants do
            if dep == ``sorryAx then
              throwError "Unfinished proof in {name}"
            if (dep.toString.splitOn ".").contains "CausalLib" then
              todo := dep :: todo
  for required in [``DAG.active_path_lemma, ``DAG.contraction_path, ``DAG.intersection_path] do
    unless seen.contains required do
      throwError "Graphoid proof did not use its direct simple-path helper: {required}"

#print axioms DAG.dSep_full_graphoid

end CausalLibTest

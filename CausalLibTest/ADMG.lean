import CausalLib

/- Regression checks for marked simple paths, bows, direct graphoid proofs,
and the separation-preserving DAG embedding. -/
namespace CausalLibTest.ADMG

open CausalLib
open CausalLib.ADMG (Mark)
open CausalLib.ADMG.Mark

private def chainDAG : DAG (Fin 3) where
  adj a b := decide ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2))
  no_self_loop := by decide
  acyclic := by decide

private def chain := chainDAG.toADMG

example : chain.IsPath [0, 1, 2] [dirFwd, dirFwd] := by decide
example : chain.pathBlocked ∅ [0, 1, 2] [dirFwd, dirFwd] = false := by decide
example : chain.pathBlocked {1} [0, 1, 2] [dirFwd, dirFwd] = true := by decide
example : chain.dConnected 0 2 ∅ :=
  ⟨[0, 1, 2], [dirFwd, dirFwd], by decide, rfl, rfl, by decide⟩

private def fork : ADMG (Fin 3) where
  adj a b := decide (a = 1 ∧ (b = 0 ∨ b = 2))
  no_self_loop := by decide
  acyclic := by decide
  bidirected _ _ := false
  bid_no_loop := by decide
  bid_symm := by decide

example : fork.IsPath [0, 1, 2] [dirBack, dirFwd] := by decide
example : fork.pathBlocked ∅ [0, 1, 2] [dirBack, dirFwd] = false := by decide
example : fork.pathBlocked {1} [0, 1, 2] [dirBack, dirFwd] = true := by decide
example : fork.parents 0 = {1} := by decide
example : fork.children 1 = {0, 2} := by decide

-- 0 → 1 ↔ 2, with 1 → 3: conditioning on 3 activates the collider at 1.
private def mixedCollider : ADMG (Fin 4) where
  adj a b := decide ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 3))
  no_self_loop := by decide
  acyclic := by decide
  bidirected a b := decide ((a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1))
  bid_no_loop := by decide
  bid_symm := by decide

example : mixedCollider.IsPath [0, 1, 2] [dirFwd, bidir] := by decide
example : mixedCollider.pathBlocked ∅ [0, 1, 2] [dirFwd, bidir] = true := by decide
example : mixedCollider.pathBlocked {1} [0, 1, 2] [dirFwd, bidir] = false := by decide
example : mixedCollider.pathBlocked {3} [0, 1, 2] [dirFwd, bidir] = false := by decide
example : mixedCollider.pathBlocked {2} [0, 1, 2] [dirFwd, bidir] = true := by decide
example : mixedCollider.dConnected 0 2 {3} :=
  ⟨[0, 1, 2], [dirFwd, bidir], by decide, rfl, rfl, by decide⟩
example : mixedCollider.spouses 1 = {2} := by decide
example : mixedCollider.spouses 2 = {1} := by decide
example : mixedCollider.ancestors 2 = ∅ := by decide
example : mixedCollider.descendants 1 = {3} := by decide
example : mixedCollider.adjacent 1 2 = true := by decide
example : mixedCollider.hasEdge 1 2 = false := by decide
example : mixedCollider.hasBidirectedEdge 1 2 = true := by decide

-- A purely bidirected collider, again with a directed descendant.
private def bidirectedCollider : ADMG (Fin 4) where
  adj a b := decide (a = 1 ∧ b = 3)
  no_self_loop := by decide
  acyclic := by decide
  bidirected a b := decide ((a = 1 ∧ (b = 0 ∨ b = 2)) ∨ ((a = 0 ∨ a = 2) ∧ b = 1))
  bid_no_loop := by decide
  bid_symm := by decide

example : bidirectedCollider.IsPath [0, 1, 2] [bidir, bidir] := by decide
example : bidirectedCollider.pathBlocked ∅ [0, 1, 2] [bidir, bidir] = true := by decide
example : bidirectedCollider.pathBlocked {3} [0, 1, 2] [bidir, bidir] = false := by decide

-- The same vertices are a chain or a collider according to the edge chosen at the bow.
private def bow : ADMG (Fin 3) where
  toDAG := chainDAG
  bidirected a b := decide ((a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1))
  bid_no_loop := by decide
  bid_symm := by decide

example : bow.IsPath [0, 1, 2] [dirFwd, dirFwd] := by decide
example : bow.IsPath [0, 1, 2] [dirFwd, bidir] := by decide
example : CausalLib.ADMG.isCollider dirFwd dirFwd = false := rfl
example : CausalLib.ADMG.isCollider dirFwd bidir = true := rfl
example : bow.pathBlocked ∅ [0, 1, 2] [dirFwd, dirFwd] = false := by decide
example : bow.pathBlocked ∅ [0, 1, 2] [dirFwd, bidir] = true := by decide
example : bow.pathBlocked {1} [0, 1, 2] [dirFwd, dirFwd] = true := by decide
example : bow.pathBlocked {1} [0, 1, 2] [dirFwd, bidir] = false := by decide

example : CausalLib.ADMG.reverseMarks [dirFwd, bidir] = [bidir, dirBack] := rfl
example : bow.IsPath [2, 1, 0] [bidir, dirBack] :=
  bow.isPath_reverse [0, 1, 2] [dirFwd, bidir] (by decide)
example (Z : Finset (Fin 3)) :
    bow.pathBlocked Z [2, 1, 0] [bidir, dirBack] =
      bow.pathBlocked Z [0, 1, 2] [dirFwd, bidir] :=
  bow.pathBlocked_reverse Z [0, 1, 2] [dirFwd, bidir] (by decide)

-- Validation rejects missing/excess marks, nonexistent chosen edges, and repetitions.
example : ¬ chain.IsPath [0, 1, 2] [dirFwd] := by decide
example : ¬ chain.IsPath [0, 1] [dirFwd, dirFwd] := by decide
example : ¬ chain.IsPath [0, 1] [bidir] := by decide
example : ¬ chain.IsPath [0, 1] [dirBack] := by decide
example : ¬ chain.IsPath [0, 1, 0] [dirFwd, dirBack] := by decide
example : chain.IsPath [] [] := by decide
example : chain.IsPath [0] [] := by decide
example : ¬ chain.IsPath [] [dirFwd] := by decide
example : ¬ chain.IsPath [0] [dirFwd] := by decide

-- The continuation 1 → 2 → 4 overlaps the original marked path at its head, 2.
private def overlapHead : ADMG (Fin 5) where
  adj a b := decide ((a = 0 ∧ (b = 1 ∨ b = 2)) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 4))
  no_self_loop := by decide
  acyclic := by decide
  bidirected a b := decide ((a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1))
  bid_no_loop := by decide
  bid_symm := by decide

example : overlapHead.pathBlocked ∅ [2, 0, 1, 3] [dirBack, dirFwd, bidir] = true := by decide
example : overlapHead.pathBlocked {4} [2, 0, 1, 3] [dirBack, dirFwd, bidir] = false := by decide
example : ∃ (P : List (Fin 5)) (M : List Mark) (b : Fin 5), overlapHead.IsPath P M ∧
    P.getLast? = some b ∧ b ∈ ({3} ∪ {4} : Finset (Fin 5)) ∧
    overlapHead.pathBlocked ∅ P M = false ∧ P.head? = some 2 := by
  exact overlapHead.active_path_lemma {3} {4} ∅ [2, 0, 1, 3] [dirBack, dirFwd, bidir] 3
    (by decide) rfl (by decide) (by decide)

-- The continuation 1 → 2 → 5 overlaps at an interior vertex, 2.
private def overlapInterior : ADMG (Fin 6) where
  adj a b := decide ((a = 0 ∧ (b = 1 ∨ b = 2)) ∨ (a = 2 ∧ (b = 3 ∨ b = 5)) ∨ (a = 1 ∧ b = 2))
  no_self_loop := by decide
  acyclic := by decide
  bidirected a b := decide ((a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1))
  bid_no_loop := by decide
  bid_symm := by decide

example : overlapInterior.pathBlocked ∅ [3, 2, 0, 1, 4] [dirBack, dirBack, dirFwd, bidir] = true := by decide
example : overlapInterior.pathBlocked {5} [3, 2, 0, 1, 4] [dirBack, dirBack, dirFwd, bidir] = false := by decide
example : ∃ (P : List (Fin 6)) (M : List Mark) (b : Fin 6), overlapInterior.IsPath P M ∧
    P.getLast? = some b ∧ b ∈ ({4} ∪ {5} : Finset (Fin 6)) ∧
    overlapInterior.pathBlocked ∅ P M = false ∧ P.head? = some 3 := by
  exact overlapInterior.active_path_lemma {4} {5} ∅ [3, 2, 0, 1, 4]
    [dirBack, dirBack, dirFwd, bidir] 4 (by decide) rfl (by decide) (by decide)

-- Enlarging the conditioning set forces a strictly shorter marked prefix.
example : ∃ (P : List (Fin 3)) (M : List Mark) (y : Fin 3), chain.IsPath P M ∧
    P.head? = some 0 ∧ P.getLast? = some y ∧ y ∈ ({1} : Finset (Fin 3)) ∧
    chain.pathBlocked ∅ P M = false ∧ P <+: [0, 1, 2] ∧ P.length < 3 := by
  have h := chain.contraction_path {1} ∅ [0, 1, 2] [dirFwd, dirFwd] (by decide) (by decide)
  rcases h with h | h
  · have hf : chain.pathBlocked (∅ ∪ {1}) [0, 1, 2] [dirFwd, dirFwd] = true := by decide
    rw [hf] at h
    contradiction
  · exact h

example : (∃ (P : List (Fin 3)) (M : List Mark) (a : Fin 3), chain.IsPath P M ∧ P.head? = some 0 ∧
      P.getLast? = some a ∧ a ∈ ({2} : Finset (Fin 3)) ∧ chain.pathBlocked {1} P M = false) ∨
    (∃ (P : List (Fin 3)) (M : List Mark) (b : Fin 3), chain.IsPath P M ∧ P.head? = some 0 ∧
      P.getLast? = some b ∧ b ∈ ({1} : Finset (Fin 3)) ∧ chain.pathBlocked {2} P M = false) := by
  simpa using chain.intersection_path {2} {1} ∅ [0, 1, 2] [dirFwd, dirFwd] 2
    (by decide) (by decide) rfl (by decide)

section General
variable {V : Type*} [Fintype V] [DecidableEq V]

example (G : CausalLib.ADMG V) (v : V) (Z : Finset V) : G.dConnected v v Z :=
  ⟨[v], [], G.isPath_singleton v, rfl, rfl, rfl⟩

example (G : CausalLib.ADMG V) (v : V) (Z : Finset V) : ¬ G.dSep v v Z := by
  intro h
  have hf := h [v] [] (G.isPath_singleton v) rfl rfl
  contradiction

example (G : CausalLib.ADMG V) (Y Z : Finset V) : G.dSepSet ∅ Y Z := by
  intro x hx
  simp at hx

example (G : CausalLib.ADMG V) (X Z : Finset V) : G.dSepSet X ∅ Z := by
  intro _ _ y hy
  simp at hy

example (D : DAG V) : D.toADMG.toDAG = D := rfl
example (D : DAG V) (x y : V) (Z : Finset V) : D.toADMG.dSep x y Z ↔ D.dSep x y Z :=
  D.toADMG_dSep_iff x y Z
example (D : DAG V) (X Y Z : Finset V) : D.toADMG.dSepSet X Y Z ↔ D.dSepSet X Y Z :=
  D.toADMG_dSepSet_iff X Y Z
example (D : DAG V) (x y : V) (Z : Finset V) : D.toADMG.dConnected x y Z ↔ D.dConnected x y Z :=
  D.toADMG_dConnected_iff x y Z
end General

-- Traverse theorem bodies as well as types; reject unfinished or indirect proofs.
open Lean in
run_cmd do
  let env ← getEnv
  let mut todo := [``CausalLib.ADMG.dSep_full_graphoid, ``CausalLib.ADMG.dSep_semigraphoid]
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
      let parts := name.toString.splitOn "."
      let leaf := parts.getLast!
      let separationDeclaration := leaf.startsWith "Is" || leaf.startsWith "dSep" ||
        leaf.startsWith "dConnected" || leaf.startsWith "active_" ||
        leaf.startsWith "contraction_" || leaf.startsWith "intersection_"
      if (separationDeclaration && !directDeclarations.contains leaf) ||
          leaf == "chainBuild" || leaf.startsWith "excise_" ||
          leaf == "seam_unblocked" || leaf == "chain_or_ancestor" ||
          (parts.contains "DAG" && (leaf.startsWith "dSep" || leaf == "active_path_lemma" ||
            leaf == "contraction_path" || leaf == "intersection_path")) then
        throwError "ADMG graphoid proof uses indirect separation machinery: {name}"
      if let some info := env.find? name then
        if let .axiomInfo _ := info then
          throwError "Project axiom in ADMG proof: {name}"
        for expr in info.type :: (info.value? (allowOpaque := true)).toList do
          for dep in expr.getUsedConstants do
            if dep == ``sorryAx then
              throwError "Unfinished proof in {name}"
            if (dep.toString.splitOn ".").contains "CausalLib" then
              todo := dep :: todo
  for required in [``CausalLib.ADMG.active_path_lemma, ``CausalLib.ADMG.contraction_path,
      ``CausalLib.ADMG.intersection_path] do
    unless seen.contains required do
      throwError "Missing direct simple-path helper: {required}"
  for required in ["splice_directed_path", "first_blocked_segment"] do
    unless seen.toList.any (fun n => (n.toString.splitOn ".").getLast! == required) do
      throwError "Missing direct simple-path construction: {required}"

#print axioms CausalLib.ADMG.dSep_full_graphoid
#print axioms DAG.toADMG_dSep_iff

end CausalLibTest.ADMG

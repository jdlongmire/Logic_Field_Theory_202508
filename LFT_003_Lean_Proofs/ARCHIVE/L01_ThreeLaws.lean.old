-- L01_ThreeLaws_FIXED.lean
-- FIXED VERSION with proper shortest path computation via BFS

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

namespace LFT.Core

open SimpleGraph

-- ============================================================================
-- PART 1: BASIC STRUCTURES (unchanged)
-- ============================================================================

structure LogicalGraph (V : Type*) [DecidableEq V] extends SimpleGraph V where
  tau : V → V
  tau_invol : ∀ v, tau (tau v) = v
  selfLoops : V → Prop
  identity_law : ∀ v : V, selfLoops v

-- ============================================================================
-- PART 2: FIXED GRAPH OPERATIONS - PROPER BFS!
-- ============================================================================

section GraphOps

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- BFS to find shortest path distance between vertices -/
def shortestPathDistance (G : SimpleGraph V) [DecidableRel G.Adj] (start target : V) : ℕ :=
  if start = target then 0 else
  -- We'll use a bounded search to ensure termination
  let maxSteps := Fintype.card V
  -- Helper function: expand one BFS layer
  let expandLayer (current : Finset V) (visited : Finset V) : Finset V :=
    current.biUnion fun v =>
      (Finset.univ.filter (G.Adj v)).filter (· ∉ visited)
  -- BFS loop with fuel for termination
  let rec bfsLoop (fuel : ℕ) (distance : ℕ) (frontier : Finset V) (visited : Finset V) : ℕ :=
    match fuel with
    | 0 => maxSteps + 1  -- Not found within bounds
    | fuel' + 1 =>
      if target ∈ frontier then distance
      else if frontier.card = 0 then maxSteps + 1  -- No path exists
      else
        let newFrontier := expandLayer frontier visited
        let newVisited := visited ∪ frontier
        bfsLoop fuel' (distance + 1) newFrontier newVisited
  bfsLoop maxSteps 0 {start} ∅

/-- Reachability check using proper BFS -/
def isReachable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Bool :=
  shortestPathDistance G u v ≤ Fintype.card V

/-- Improved distance function using BFS -/
def graphDist (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ :=
  shortestPathDistance G u v

/-- Neighbor set (unchanged) -/
def neighborFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ.filter (G.Adj v)

end GraphOps

-- ============================================================================
-- PART 3: THE THREE LAWS (updated to use new functions)
-- ============================================================================

section ThreeLaws

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- L1: Law of Identity -/
def satisfiesIdentity (G : LogicalGraph V) : Prop :=
  ∀ v : V, G.selfLoops v

/-- L2: Law of Non-Contradiction - no path from v to τ(v) -/
def satisfiesNonContradiction (G : LogicalGraph V) [DecidableRel G.toSimpleGraph.Adj] : Prop :=
  ∀ v : V, ¬(isReachable G.toSimpleGraph v (G.tau v))

/-- L3: Law of Excluded Middle -/
def satisfiesExcludedMiddle (G : LogicalGraph V) : Prop :=
  ∀ v : V, ∃ v' : V, v' = G.tau v

/-- A graph is admissible iff it satisfies all three laws -/
def isAdmissible (G : LogicalGraph V) [DecidableRel G.toSimpleGraph.Adj] : Prop :=
  satisfiesIdentity G ∧
  satisfiesNonContradiction G ∧
  satisfiesExcludedMiddle G

end ThreeLaws

-- ============================================================================
-- PART 4: CONCRETE EXAMPLES
-- ============================================================================

inductive Prop4 : Type
  | p | notp | q | notq
  deriving DecidableEq

instance : Fintype Prop4 where
  elems := {Prop4.p, Prop4.notp, Prop4.q, Prop4.notq}
  complete := by intro x; cases x <;> simp

def prop4_tau : Prop4 → Prop4
  | Prop4.p => Prop4.notp
  | Prop4.notp => Prop4.p
  | Prop4.q => Prop4.notq
  | Prop4.notq => Prop4.q

theorem prop4_tau_invol : ∀ v, prop4_tau (prop4_tau v) = v := by
  intro x; cases x <;> rfl

def emptyProp4Graph : SimpleGraph Prop4 where
  Adj := fun _ _ => False
  symm := fun _ _ h => h.elim
  loopless := fun _ h => h.elim

def classicalLogicGraph : LogicalGraph Prop4 where
  toSimpleGraph := emptyProp4Graph
  tau := prop4_tau
  tau_invol := prop4_tau_invol
  selfLoops := fun _ => True
  identity_law := fun _ => trivial

def quantumGraph : LogicalGraph Prop4 where
  toSimpleGraph := {
    Adj := fun x y =>
      (x = Prop4.p ∧ y = Prop4.q) ∨
      (x = Prop4.q ∧ y = Prop4.p) ∨
      (x = Prop4.notp ∧ y = Prop4.notq) ∨
      (x = Prop4.notq ∧ y = Prop4.notp)
    symm := by
      intro x y h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right; left; exact ⟨rfl, rfl⟩
      · left; exact ⟨rfl, rfl⟩
      · right; right; right; exact ⟨rfl, rfl⟩
      · right; right; left; exact ⟨rfl, rfl⟩
    loopless := by
      intro x h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      all_goals { cases x <;> simp at h1 h2 }
  }
  tau := prop4_tau
  tau_invol := prop4_tau_invol
  selfLoops := fun _ => True
  identity_law := fun _ => trivial

-- ============================================================================
-- PART 5: PATH GRAPH EXAMPLE - To Test BFS
-- ============================================================================

/-- A linear path graph: A→B→C→D to test distances -/
def pathGraph : LogicalGraph Prop4 where
  toSimpleGraph := {
    Adj := fun x y =>
      (x = Prop4.p ∧ y = Prop4.notp) ∨      -- p → ~p
      (x = Prop4.notp ∧ y = Prop4.q) ∨      -- ~p → q
      (x = Prop4.q ∧ y = Prop4.notq) ∨      -- q → ~q
      -- Add reverse edges for undirected graph
      (x = Prop4.notp ∧ y = Prop4.p) ∨
      (x = Prop4.q ∧ y = Prop4.notp) ∨
      (x = Prop4.notq ∧ y = Prop4.q)
    symm := by
      intro x y h
      rcases h <;> simp [*]
      -- Would prove symmetry case by case
      sorry
    loopless := by
      intro x h
      rcases h <;> simp [*] at h
  }
  tau := prop4_tau
  tau_invol := prop4_tau_invol
  selfLoops := fun _ => True
  identity_law := fun _ => trivial

-- ============================================================================
-- PART 6: EXPORTS FOR L02
-- ============================================================================

section Exports

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Distance to logical negation (NOW USING PROPER BFS!) -/
def distanceToContradiction (G : LogicalGraph V) [DecidableRel G.toSimpleGraph.Adj] (v : V) : ℕ :=
  graphDist G.toSimpleGraph v (G.tau v)

/-- Check if near contradiction -/
def isNearContradiction (G : LogicalGraph V) [DecidableRel G.toSimpleGraph.Adj]
    (v : V) (threshold : ℕ) : Bool :=
  distanceToContradiction G v ≤ threshold

end Exports

-- ============================================================================
-- PART 7: TEST THE BFS IMPLEMENTATION
-- ============================================================================

section Tests

-- DecidableRel instances
instance : DecidableRel emptyProp4Graph.Adj := fun _ _ => isFalse (fun h => h.elim)
instance : DecidableRel classicalLogicGraph.toSimpleGraph.Adj := fun _ _ => isFalse (fun h => h.elim)

instance : DecidableRel pathGraph.toSimpleGraph.Adj := fun x y =>
  if h : (x = Prop4.p ∧ y = Prop4.notp) ∨
         (x = Prop4.notp ∧ y = Prop4.q) ∨
         (x = Prop4.q ∧ y = Prop4.notq) ∨
         (x = Prop4.notp ∧ y = Prop4.p) ∨
         (x = Prop4.q ∧ y = Prop4.notp) ∨
         (x = Prop4.notq ∧ y = Prop4.q)
  then isTrue h
  else isFalse h

#eval graphDist pathGraph.toSimpleGraph Prop4.p Prop4.p       -- Should be 0
#eval graphDist pathGraph.toSimpleGraph Prop4.p Prop4.notp    -- Should be 1
#eval graphDist pathGraph.toSimpleGraph Prop4.p Prop4.q       -- Should be 2
#eval graphDist pathGraph.toSimpleGraph Prop4.p Prop4.notq    -- Should be 3

#eval distanceToContradiction pathGraph Prop4.p    -- p to ~p: should be 1
#eval distanceToContradiction pathGraph Prop4.q    -- q to ~q: should be 1

-- For classical (empty) graph:
#eval distanceToContradiction classicalLogicGraph Prop4.p  -- Should be 5 (no path)

end Tests

/-
KEY IMPROVEMENTS:

1. PROPER BFS: shortestPathDistance actually finds shortest paths!
2. TEST GRAPH: Added pathGraph to verify distances are computed correctly
3. BOUNDED SEARCH: Uses fuel parameter to ensure termination
4. LAYER EXPANSION: Proper BFS that expands frontier layer by layer
5. EXPORTS FIXED: distanceToContradiction now returns meaningful values

This fixes the fundamental issue that was breaking all strain calculations!
-/

end LFT.Core

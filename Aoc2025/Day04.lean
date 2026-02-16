import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Aoc2025.Utils.Grid

namespace Day04

def parseLines (lines : Array String) : Option ((m : Nat) × (n : Nat) × Grid Bool m n) :=
  Grid.ofArrays (lines.map fun s => s.toList.toArray.map (· == '@'))

def accessible (grid : Grid Bool m n) (i : Fin m) (j : Fin n) : Bool :=
  grid[i][j] && (Grid.neighbors8 i j).countP (fun (i, j) => grid[i][j]) < 4

def countAccessible (grid : Grid Bool m n) : Nat :=
  (List.finRange m ×ˢ List.finRange n).countP fun (i, j) => accessible grid i j

def countRolls (grid : Grid Bool m n) : Nat :=
  (List.finRange m ×ˢ List.finRange n).countP fun (i, j) => grid[i][j]

structure RemovalState (m n) where
  grid : Grid Bool m n
  stack : List (Fin m × Fin n)
  stack_nodup : stack.Nodup
  mem_stack : ∀ i j, (i, j) ∈ stack ↔ accessible grid i j

namespace RemovalState

def ofGrid (grid : Grid Bool m n) : RemovalState m n where
  grid
  stack := (List.finRange m ×ˢ List.finRange n).filter fun (i, j) => accessible grid i j
  stack_nodup := ((List.nodup_finRange _).product (List.nodup_finRange _)).filter _
  mem_stack := by simp

lemma accessible_set
  {i : Fin m} {j : Fin n} {i' : Fin m} {j' : Fin n} {grid : Grid Bool m n}
  (h₁ : (i, j) ≠ (i', j'))
  (h₂ : accessible grid i' j')
: accessible (grid.set i j false) i' j' := by
  simp [accessible] at h₂ ⊢
  rcases h₂ with ⟨h₂, h₃⟩
  rw [Grid.getElem_set, ite_cond_eq_false _ _ (by grind)]
  refine ⟨h₂, lt_of_le_of_lt ?_ h₃⟩
  apply List.countP_mono_left
  intro (a, b) hx hy
  rw [Grid.getElem_set] at hy
  grind

lemma not_accessible_set
  {i : Fin m} {j : Fin n} {i' : Fin m} {j' : Fin n} {grid : Grid Bool m n}
  (h₁ : (i, j) ∉ Grid.neighbors8 i' j')
  (h₂ : accessible grid i' j' = false)
: accessible (grid.set i j false) i' j' = false := by
  simp [accessible] at h₂ ⊢
  intro h
  rw [Grid.getElem_set, ite_cond_eq_false _ _ (by grind)] at h
  specialize h₂ h
  apply le_trans h₂
  apply List.countP_mono_left
  intro (a, b) hx hy
  rw [Grid.getElem_set, hy, ite_cond_eq_false]
  grind

def remove (state : RemovalState m n) (h : state.stack ≠ []) : RemovalState m n :=
  let hd := state.stack.head h
  -- theoretically it may be possible for the compiler to figure out how to do
  -- this nonsense linearly, but i don't trust it to and i don't need it to.
  let inaccessibleBefore := Grid.neighbors8 hd.fst hd.snd |>.filter fun (i, j) => !accessible state.grid i j
  let grid' := state.grid.set hd.fst hd.snd false
  let accessibleAfter := inaccessibleBefore.filter fun (i, j) => accessible grid' i j
  {
    grid := grid'
    stack := accessibleAfter ++ state.stack.tail
    stack_nodup := by
      rw [List.nodup_append]
      refine ⟨(Grid.neighbors8_nodup.filter _).filter _ , state.stack_nodup.tail, ?_⟩
      rintro ⟨i, j⟩ h₁⟨_, _⟩ h₂ ⟨⟩
      replace h₂ := List.mem_of_mem_tail h₂
      rw [state.mem_stack] at h₂
      grind
    mem_stack := by
      subst hd inaccessibleBefore accessibleAfter grid'
      rcases state with ⟨grid, stack, stack_nodup, mem_stack⟩
      simp at h ⊢
      cases stack
      case nil =>
        contradiction
      case cons hd tl =>
        rcases hd with ⟨i, j⟩
        intro i' j'
        simp
        constructor
        case mp =>
          intro h
          cases h
          case inl h =>
            exact h.right.left
          case inr h =>
            apply accessible_set <;> grind
        case mpr =>
          intro h
          have h' : (i, j) ≠ (i', j') := by
            rintro ⟨⟩
            simp [accessible] at h
            replace h := h.left
            simp [Grid.getElem_set] at h
          specialize mem_stack i' j'
          rw [List.mem_cons] at mem_stack
          by_cases (i', j') ∈ tl
          case pos hmem =>
            exact Or.inr hmem
          replace mem_stack : accessible grid i' j' = false := by grind
          refine Or.inl ⟨?_, h, mem_stack⟩
          rw [Grid.mem_neighbors8_iff]
          by_contra
          have := not_accessible_set this mem_stack
          grind
  }

theorem grid_remove (state : RemovalState m n) (h : state.stack ≠ [])
: (state.remove h).grid = Grid.set state.grid (state.stack.head h).fst (state.stack.head h).snd false := rfl

theorem finRange_product_filter {m n} (i : Fin m) (j : Fin n)
: (List.finRange m ×ˢ List.finRange n).filter (· = (i, j)) = [(i, j)] := by
  rw [List.filter_eq]
  convert List.replicate_one
  apply List.count_eq_one_of_mem
  · exact (List.nodup_finRange _).product (List.nodup_finRange _)
  · simp

theorem countRolls_remove_lt (state : RemovalState m n) (h : state.stack ≠ [])
: countRolls (state.remove h).grid < countRolls state.grid := by
  simp [countRolls]
  rw [List.countP_eq_countP_filter_add _ _ (· = state.stack.head h)]
  rw (occs := .pos [3]) [List.countP_eq_countP_filter_add _ _ (· = state.stack.head h)]
  rw [finRange_product_filter, List.countP_singleton, List.countP_singleton, grid_remove]
  rw [ite_cond_eq_false]
  case h =>
    simp [Grid.getElem_set]
  rw [ite_cond_eq_true]
  case h =>
    have := state.mem_stack (state.stack.head h).fst (state.stack.head h).snd
    simp [accessible] at *
    exact this.left
  rw [Nat.zero_add, Nat.add_comm, Nat.lt_add_one_iff]
  apply le_of_eq
  rw [List.countP_filter, List.countP_filter]
  congr
  ext idx
  by_cases hidx : idx = state.stack.head h
  · subst hidx
    simp
  · simp [hidx]
    rw [Grid.getElem_set]
    grind

def countRemovals (state : RemovalState m n) : Nat :=
  if h : state.stack = [] then
    0
  else
    countRemovals (state.remove h) + 1
termination_by countRolls state.grid
decreasing_by apply countRolls_remove_lt

end RemovalState

def countRemovals (grid : Grid Bool m n) : Nat :=
  (RemovalState.ofGrid grid).countRemovals

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day04/test.txt")
  let ⟨_, _, grid⟩ ← (parseLines lines).getDM (throw (IO.userError "invalid file"))
  println! "Test: {countAccessible grid}"
  println! "Expected: {13}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day04/task.txt")
  let ⟨_, _, grid⟩ ← (parseLines lines).getDM (throw (IO.userError "invalid file"))
  println! "Task: {countAccessible grid}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day04/test.txt")
  let ⟨_, _, grid⟩ ← (parseLines lines).getDM (throw (IO.userError "invalid file"))
  println! "Test: {countRemovals grid}"
  println! "Expected: {43}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day04/task.txt")
  let ⟨_, _, grid⟩ ← (parseLines lines).getDM (throw (IO.userError "invalid file"))
  println! "Task: {countRemovals grid}"

end Task2

def main : IO Unit := do
  println! "Day 4"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day04

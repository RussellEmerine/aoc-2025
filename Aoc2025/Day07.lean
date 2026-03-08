import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.ReduceOption
import Aoc2025.Utils.Grid

namespace Day07

def neighbors (i : Fin n) : List (Fin n) :=
  [i.pred?, i.succ?].reduceOption

theorem neighbors_nodup : (neighbors i).Nodup := by
  rw [neighbors, Fin.pred?, Fin.succ?]
  split_ifs <;> simp

theorem mem_neighbors_iff
: i ∈ neighbors j ↔ j ∈ neighbors i := by
  unfold neighbors List.reduceOption
  simp
  conv => lhs ; lhs ; rw [eq_comm, Fin.pred?_succ?]
  conv => lhs ; rhs ; rw [eq_comm]
  conv => rhs ; lhs ; rw [eq_comm, Fin.pred?_succ?]
  conv => rhs ; rhs ; rw [eq_comm]
  rw [Or.comm]

def step (state : Vector Bool n) (splitters : Vector Bool n)
: Vector Bool n × Nat := (
  Vector.ofFn fun i =>
    state[i] && !splitters[i]
      || (neighbors i).any fun j => state[j] && splitters[j],
  (state.zip splitters).count (true, true)
)

structure Manifold (n : Nat) where
  start : Fin n
  splitters : List (Vector Bool n)

namespace Manifold

def parseLines (lines : Array String)
: Except String ((n : Nat) × Manifold n) := do
  let ⟨_, n, grid⟩ ← Grid.ofArrays (lines.map (·.toList.toArray))
    |>.getDM (throw "file lines were not uniform length")
  if let startRow :: rows := grid.toList then
    if let [start] := (List.finRange n).filter (startRow[·] = 'S') then
      return ⟨n, {
        start
        splitters := rows.map (·.map (· = '^'))
      }⟩
    else
      throw "file did not have a unique start"
  else
    throw "file had no lines"

def countSplits (manifold : Manifold n) :=
  (manifold.splitters.foldl
    (fun (state, c) splitters =>
      let (state', c') := step state splitters
      (state', c + c'))
    (Vector.ofFn (· == manifold.start), 0)).snd

def countTimelinesAux (i : Fin n) : List (Vector Bool n) → Nat
| [] => 1
| splitters :: tl =>
  if splitters[i] then
    ((neighbors i).map (countTimelinesAux · tl)).sum
  else
    countTimelinesAux i tl

-- the slow version
def countTimelines (manifold : Manifold n) :=
  countTimelinesAux manifold.start manifold.splitters

def countQuantumAux (state : Vector Nat n) : List (Vector Bool n) → Nat
| [] => state.sum
| splitters :: tl =>
  countQuantumAux
    (Vector.ofFn fun i =>
      (if splitters[i] then 0 else state[i])
      + ((neighbors i).map (fun j => if splitters[j] then state[j] else 0)).sum)
    tl

-- the fast version
def countQuantum (manifold : Manifold n) :=
  countQuantumAux (Vector.ofFn fun i => if i = manifold.start then 1 else 0) manifold.splitters

theorem countQuantumAux_eq {state : Vector Nat n} {splitters : List (Vector Bool n)}
: countQuantumAux state splitters = ∑ i, state[i] * countTimelinesAux i splitters := by
  induction splitters generalizing state
  case nil =>
    simp [countQuantumAux, countTimelinesAux]
    rcases state with ⟨⟨state⟩, rfl⟩
    simp
    congr
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      simp
  case cons splitters tl ih =>
    simp [countQuantumAux, countTimelinesAux, ih]
    simp [add_mul, Finset.sum_add_distrib, Finset.sum_ite]
    rw [add_comm]
    congr 1
    conv =>
      lhs
      arg 2
      ext i
      rw [← List.sum_toFinset _ neighbors_nodup]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      rw [Finset.sum_mul]
    conv =>
      rhs
      arg 2
      ext i
      rw [← List.sum_toFinset _ neighbors_nodup]
      rw [Finset.mul_sum]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    apply Finset.sum_bijective fun x => ⟨x.snd, x.fst⟩
    · apply Function.Involutive.bijective
      intro ⟨i, j⟩
      simp
    · intro ⟨i, j⟩
      simp
      rw [And.comm, mem_neighbors_iff]
    · intro ⟨i, j⟩ h
      simp

theorem countQuantum_eq : countQuantum manifold = countTimelines manifold := by
  simp [countQuantum, countTimelines, countQuantumAux_eq]

end Manifold

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day07/test.txt")
  let ⟨_, manifold⟩ ← IO.ofExcept (Manifold.parseLines lines)
  println! "Test: {manifold.countSplits}"
  println! "Expected: {21}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day07/task.txt")
  let ⟨_, manifold⟩ ← IO.ofExcept (Manifold.parseLines lines)
  println! "Task: {manifold.countSplits}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day07/test.txt")
  let ⟨_, manifold⟩ ← IO.ofExcept (Manifold.parseLines lines)
  println! "Test: {manifold.countQuantum}"
  println! "Expected: {40}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day07/task.txt")
  let ⟨_, manifold⟩ ← IO.ofExcept (Manifold.parseLines lines)
  println! "Task: {manifold.countQuantum}"

end Task2

def main : IO Unit := do
  println! "Day 7"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day07

import Std.Internal.Parsec.String
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Infix
import Batteries.Data.List.Scan
import Mathlib.Order.Lattice
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.MinMax
import Mathlib.Data.Vector.Basic

namespace Day03

universe u

lemma mono_map_maximum {α β} [LinearOrder α] [LinearOrder β] (f : α → β) (hf : Monotone f) (xs : List α)
: (xs.map f).maximum = xs.maximum.map f := by
  induction xs
  case nil =>
    simp
  case cons x xs ih =>
    rw [List.map_cons, List.maximum_cons, ih, List.maximum_cons]
    rw [Monotone.map_max (WithBot.monotone_map_iff.mpr hf)]
    rfl

def subvectors (n : ℕ) (xs : List α) : List (List.Vector α n) :=
  (xs.sublistsLen n).pmap (fun sl h => ⟨sl, h⟩) fun _ h => (List.mem_sublistsLen.mp h).right

@[simp]
theorem subvectors_zero : subvectors 0 (xs : List α) = [List.Vector.nil] := by
  rw [subvectors]
  conv =>
    lhs
    arg 2
    rw [List.sublistsLen_zero]
  simp
  rfl

@[simp]
theorem subvectors_succ_nil (n : ℕ) : subvectors (n + 1) ([] : List α) = [] := by
  simp [subvectors]

@[simp]
theorem subvectors_succ_cons (n : ℕ) (x : α) (xs : List α)
: subvectors (n + 1) (x :: xs) = subvectors (n + 1) xs ++ (subvectors n xs).map (x ::ᵥ ·) := by
  rw [subvectors, subvectors, subvectors]
  conv =>
    lhs
    arg 2
    rw [List.sublistsLen_succ_cons]
  simp [List.map_pmap, List.pmap_map]
  apply List.pmap_congr_left
  intro xs hxs h₁ h₂
  rfl

@[simp]
theorem mem_subvectors
: sl ∈ subvectors n xs ↔ sl.toList.Sublist xs := by
  simp [subvectors]
  constructor
  case mp =>
    rintro ⟨a, h, rfl⟩
    exact h.left
  case mpr =>
    intro hsl
    exact ⟨sl.toList, ⟨hsl, sl.toList_length⟩, rfl⟩

instance (n : ℕ) (α : Type u) [LinearOrder α] : LinearOrder (List.Vector α n) :=
  Subtype.instLinearOrder _

variable {α : Type u} [LinearOrder α] {x : α} {xs : List α}

-- has the desired behavior but is exponential time
def maxSubvector' : List α → (n : ℕ) → WithBot (List.Vector α n)
| _, 0 => WithBot.some List.Vector.nil
| [], _ + 1 => ⊥
| x :: xs, n + 1 => max (maxSubvector' xs (n + 1)) ((maxSubvector' xs n).map (x ::ᵥ ·))

theorem maxSubvector'_max (xs : List α) (n : ℕ)
: maxSubvector' xs n = (subvectors n xs).maximum := by
  fun_induction maxSubvector'
  case case1 =>
    simp
  case case2 =>
    simp [subvectors]
  case case3 x xs n ih₁ ih₂ =>
    rw [ih₁, ih₂, subvectors_succ_cons, List.maximum_append]
    congr
    rw [mono_map_maximum]
    intro v₁ v₂ h
    dsimp
    rw [← Subtype.coe_le_coe, List.Vector.cons_val, List.Vector.cons_val]
    apply List.cons_le_cons
    rw [Subtype.coe_le_coe]
    exact h

def maxSubvectorAux (xs : List α) : (n : ℕ) → List (WithBot (List.Vector α n))
| 0 => List.replicate (xs.length + 1) (WithBot.some List.Vector.nil)
| n + 1 => (xs.zipWith (fun x v => v.map (x ::ᵥ ·)) ((maxSubvectorAux xs n).tail ++ [⊥])).scanr max ⊥

theorem length_maxSubvectorAux : (maxSubvectorAux xs n).length = xs.length + 1 := by
  induction n
  case zero =>
    simp [maxSubvectorAux]
  case succ n ih =>
    simp [maxSubvectorAux, ih]

theorem maxSubvectorAux_ne_nil : maxSubvectorAux xs n ≠ [] := by
  rw [List.ne_nil_iff_length_pos, length_maxSubvectorAux]
  simp

def tail_maxSubvectorAux
: (maxSubvectorAux (x :: xs) n).tail = maxSubvectorAux xs n := by
  induction n generalizing x xs
  case zero =>
    simp [maxSubvectorAux]
  case succ n ih =>
    simp [maxSubvectorAux]
    rw [List.tail_scanr (by simp)]
    rw [ih]
    congr
    rw [List.tail_zipWith]
    congr
    rw [List.tail_append_of_ne_nil maxSubvectorAux_ne_nil]

def maxSubvector (xs : List α) (n : ℕ) : WithBot (List.Vector α n) :=
  (maxSubvectorAux xs n).head maxSubvectorAux_ne_nil

theorem maxSubvectorAux_cons_eq_cons
: maxSubvectorAux (x :: xs) n = maxSubvector (x :: xs) n :: maxSubvectorAux xs n := by
  rw [← List.cons_head_tail maxSubvectorAux_ne_nil]
  rw [tail_maxSubvectorAux]
  rfl

theorem maxSubvectorAux_eq_map_maxSubvector (xs : List α) (n : ℕ)
: maxSubvectorAux xs n = xs.tails.map (maxSubvector · n) := by
  induction xs
  case nil =>
    cases n <;> simp [maxSubvectorAux, maxSubvector]
  case cons x xs ih =>
    rw [maxSubvectorAux_cons_eq_cons, List.tails_cons, List.map_cons, ih]

@[simp]
theorem maxSubvector_zero (xs : List α) : maxSubvector xs 0 = WithBot.some List.Vector.nil := rfl

@[simp]
theorem maxSubvector_nil_succ : maxSubvector ([] : List α) (n + 1) = ⊥ := rfl

theorem maxSubvector_cons_succ'
: maxSubvector (x :: xs) (n + 1) = ((x :: xs).zipWith (fun x v => v.map (x ::ᵥ ·)) (maxSubvectorAux xs n ++ [⊥])).foldr max ⊥ := by
  simp [maxSubvector, maxSubvectorAux]
  congr
  induction n
  case zero =>
    simp [maxSubvectorAux]
  case succ n ih =>
    simp [maxSubvectorAux, List.tail_scanr, ih]
    congr 1
    conv =>
      rw [List.zipWith_eq_zipWith_take_min]
      rhs
      rw [List.zipWith_eq_zipWith_take_min]
    congr 1
    · simp [length_maxSubvectorAux]
    · simp [length_maxSubvectorAux]
      rw [List.take_eq_dropLast]
      · rw [← List.tail_dropLast, List.dropLast_concat]
      · rw [List.length_tail, List.length_append]
        simp [length_maxSubvectorAux]

@[simp]
theorem maxSubvector_cons_succ
: maxSubvector (x :: xs) (n + 1) = max ((maxSubvector xs n).map (x ::ᵥ ·)) (maxSubvector xs (n + 1)) := by
  induction xs generalizing x
  case nil =>
    cases n
    case zero =>
      simp [maxSubvector, maxSubvectorAux]
    case succ n =>
      simp
      unfold maxSubvector
      conv =>
        lhs
        congr
        rw [maxSubvectorAux]
      rw [List.head_scanr]
      rw [maxSubvectorAux_eq_map_maxSubvector]
      simp
  case cons x' xs ih =>
    rw [maxSubvector_cons_succ']
    rw [← List.cons_head_tail maxSubvectorAux_ne_nil]
    rw [List.cons_append]
    rw [List.zipWith_cons_cons]
    rw [List.foldr_cons]
    congr
    rw [maxSubvectorAux_cons_eq_cons]
    rw [List.tail_cons]
    rw [← maxSubvector_cons_succ']

theorem maxSubvector_eq_maxSubvector'
: maxSubvector xs n = maxSubvector' xs n := by
  fun_induction maxSubvector' xs n
  case case1 =>
    rw [maxSubvector_zero]
  case case2 =>
    rw [maxSubvector_nil_succ]
  case case3 x xs n ih₁ ih₂ =>
    simp
    rw [max_comm]
    congr

theorem maxSubvector_eq_maximum
: maxSubvector xs n = (subvectors n xs).maximum := by
  rw [maxSubvector_eq_maxSubvector']
  rw [maxSubvector'_max]

abbrev Digit : Type := Set.Ico 1 10

namespace Digit

def ofChar : Char → Except String Digit
| '1' => Except.ok ⟨1, by simp⟩
| '2' => Except.ok ⟨2, by simp⟩
| '3' => Except.ok ⟨3, by simp⟩
| '4' => Except.ok ⟨4, by simp⟩
| '5' => Except.ok ⟨5, by simp⟩
| '6' => Except.ok ⟨6, by simp⟩
| '7' => Except.ok ⟨7, by simp⟩
| '8' => Except.ok ⟨8, by simp⟩
| '9' => Except.ok ⟨9, by simp⟩
| c => Except.error s!"character {c} is invalid digit"

def toNat (d : Digit) : ℕ := d.val

end Digit

structure Batteries where
  banks : List (List Digit)

namespace Batteries

def ofLines (lines : List String) : Except String Batteries := do
  let banks ← lines.mapM (·.toList.mapM Digit.ofChar)
  return { banks }

def joltage (batteries : Batteries) (n : ℕ) : ℕ :=
  List.sum <| do
    let bank ← batteries.banks
    let v ← Option.toList (maxSubvector bank n)
    return v.toList.foldl (· * 10 + ·.toNat) 0

end Batteries

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day03/test.txt")
  let batteries ← IO.ofExcept (Batteries.ofLines lines.toList)
  println! "Test: {batteries.joltage 2}"
  println! "Expected: {357}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day03/task.txt")
  let batteries ← IO.ofExcept (Batteries.ofLines lines.toList)
  println! "Task: {batteries.joltage 2}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day03/test.txt")
  let batteries ← IO.ofExcept (Batteries.ofLines lines.toList)
  println! "Test: {batteries.joltage 12}"
  println! "Expected: {3121910778619}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day03/task.txt")
  let batteries ← IO.ofExcept (Batteries.ofLines lines.toList)
  println! "Task: {batteries.joltage 12}"

end Task2

def main : IO Unit := do
  println! "Day 3"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day03

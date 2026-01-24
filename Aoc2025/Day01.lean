import Std.Internal.Parsec.String
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Defs -- NOTE: defines ring on Fin

open Std.Internal.Parsec.String

namespace Day01

inductive Dir
| L
| R
deriving DecidableEq

namespace Dir

def delta : Dir → Fin 100
| .L => -1
| .R => 1

end Dir

structure Rot where
  dir : Dir
  dist : Nat

namespace Rot 

def delta (rot : Rot) : Fin 100 :=
  rot.dir.delta * Fin.ofNat _ rot.dist 

def parser : Parser Rot := do
  let dir ← (skipChar 'L' *> pure Dir.L) <|> (skipChar 'R' *> pure Dir.R)
  let dist ← digits
  return { dir, dist }

end Rot

structure Dial where
  pos : Fin 100
  count : Nat

namespace Dial

def new : Dial := { pos := 50, count := 0 }

def rotate (dial : Dial) (rot : Rot) : Dial :=
  let pos := dial.pos + rot.delta
  { pos, count := dial.count + if pos = 0 then 1 else 0 }

def step (dial : Dial) (dir : Dir) : Dial :=
  let pos := dial.pos + dir.delta
  { pos, count := dial.count + if pos = 0 then 1 else 0 }

def step_many (dial : Dial) (rot : Rot) : Dial :=
  let cycles := rot.dist / 100
  (step · rot.dir)^[rot.dist % 100] { pos := dial.pos, count := dial.count + cycles }

lemma range_countP_eq_one
  {n : ℕ} [NeZero n]
  (x : Fin n)
: (List.range n).countP (Fin.ofNat n · = x) = 1 := by
  have h : ∀ y ∈ List.range n, decide (Fin.ofNat n y = x) ↔ decide (y = x) = true := by
    intro y hy
    rw [Bool.decide_iff, Bool.decide_iff]
    rw [List.mem_range] at hy
    refine ⟨?_, ?_⟩
    · intro rfl
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt hy]
    · intro rfl
      rw [Fin.ofNat_val_eq_self]
  rw [List.countP_congr h]
  conv =>
    lhs
    congr
    ext
    rw [← beq_eq_decide]
  rw [← List.count_eq_countP, List.count_range]
  simp

lemma iterate_step
: (step · dir)^[n] dial = {
    pos := dial.pos + Fin.ofNat _ n * dir.delta,
    count := dial.count + (List.range n).countP (dial.pos + Fin.ofNat _ · * dir.delta + dir.delta = 0)
  }
:= by
  induction n
  case zero =>
    simp [-Fin.ofNat_eq_cast]
  case succ n hn =>
    rw [add_comm, Function.iterate_add_apply, Function.iterate_one, hn, step]
    congr 1
    · rw [add_comm 1 n]
      simp [-Fin.ofNat_eq_cast, Fin.ofNat_mul, Fin.ofNat_add, Fin.add_ofNat, add_mul, add_assoc]
    · simp [Nat.one_add, List.range_succ, List.countP_append, List.countP_singleton, add_assoc]

lemma iterate_step_100_eq_add_one
: (step · dir)^[100] dial = { pos := dial.pos, count := dial.count + 1 } := by
  rw [iterate_step]
  simp [-Fin.ofNat_eq_cast]
  cases dir
  case L =>
    simp [-Fin.ofNat_eq_cast, Dir.delta]
    conv =>
      lhs
      congr
      ext
      congr
      rw [add_eq_zero_iff_eq_neg, ← eq_sub_iff_add_eq', neg_eq_iff_eq_neg, neg_sub, neg_neg]
    rw [range_countP_eq_one]
  case R =>
    simp [-Fin.ofNat_eq_cast, Dir.delta]
    conv =>
      lhs
      congr
      ext
      congr
      rw [add_eq_zero_iff_eq_neg, ← eq_neg_add_iff_add_eq]
    rw [range_countP_eq_one]

lemma add_cycles_eq_iterate_step_mul_100
: { pos := dial.pos, count := dial.count + cycles } = (step · dir)^[cycles * 100] dial := by
  induction cycles
  case zero =>
    simp
  case succ n hn =>
    rw [add_mul, one_mul, add_comm _ 100, Function.iterate_add_apply, ← hn]
    rw [iterate_step_100_eq_add_one]
    simp [add_assoc]

theorem step_many_eq_iterate_step : step_many dial rot = (step · rot.dir)^[rot.dist] dial := by
  rcases rot with ⟨dir, dist⟩
  dsimp [step_many]
  conv =>
    rhs
    arg 2
    rw [← dist.mod_add_div 100, mul_comm]
  rw [Function.iterate_add_apply, add_cycles_eq_iterate_step_mul_100]

end Dial

namespace Task1

def task (rots : List Rot) : Nat :=
  (rots.foldl Dial.rotate Dial.new).count

def main : IO Unit := do
  let test ← IO.FS.lines (System.FilePath.mk "Data/Day01/test.txt")
  let rots ← test.mapM (IO.ofExcept ∘ Rot.parser.run)
  println! "Test: {task rots.toList}"
  println! "Expected: {3}"
  let data ← IO.FS.lines (System.FilePath.mk "Data/Day01/task.txt")
  let rots ← data.mapM (IO.ofExcept ∘ Rot.parser.run)
  println! "Task: {task rots.toList}"

end Task1

namespace Task2

def task (rots : List Rot) : Nat :=
  (rots.foldl Dial.step_many Dial.new).count

def main : IO Unit := do
  let test ← IO.FS.lines (System.FilePath.mk "Data/Day01/test.txt")
  let rots ← test.mapM (IO.ofExcept ∘ Rot.parser.run)
  println! "Test: {task rots.toList}"
  println! "Expected: {6}"
  let data ← IO.FS.lines (System.FilePath.mk "Data/Day01/task.txt")
  let rots ← data.mapM (IO.ofExcept ∘ Rot.parser.run)
  println! "Task: {task rots.toList}"

end Task2 

def main : IO Unit := do
  println! "Day 1"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""
  
end Day01

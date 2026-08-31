import Batteries.Data.List.Basic
import Std.Internal.Parsec.String
import Mathlib.Data.Nat.Dist

open Std.Internal.Parsec.String

namespace Day09

def parseTile : Parser (Nat × Nat) := do
  let x ← digits
  skipChar ','
  let y ← digits
  return (x, y)

def area (p₁ p₂ : Nat × Nat) : Nat := (p₁.fst.dist p₂.fst + 1) * (p₁.snd.dist p₂.snd + 1)

namespace Task1

def solve (tiles : Array (Nat × Nat)) : Nat :=
  ((tiles.toList.product tiles.toList).map (fun (p₁, p₂) => area p₁ p₂)).max?.getD 0

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day09/test.txt")
  let tiles ← IO.ofExcept <| lines.mapM parseTile.run
  println! "Test: {solve tiles}"
  println! "Expected: {50}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day09/task.txt")
  let tiles ← IO.ofExcept <| lines.mapM parseTile.run
  println! "Task: {solve tiles}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day09/test.txt")
  let tiles ← IO.ofExcept <| lines.mapM parseTile.run
  println! "Test: TODO"
  println! "Expected: {25272}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day09/task.txt")
  let tiles ← IO.ofExcept <| lines.mapM parseTile.run
  println! "Task: TODO"

end Task2

def main : IO Unit := do
  println! "Day 9"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day09

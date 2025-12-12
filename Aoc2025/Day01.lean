import Std.Internal.Parsec.String 

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
  (rot.dist % 100).repeat (step · rot.dir) { pos := dial.pos, count := dial.count + cycles }

-- TODO: 100.repeat (step · rot.dir) dial = { pos := dial.pos, count := dial.count + 1 }
-- TODO: step_many dial rot = rot.dist.repeat (step · rot.dir) dial 

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

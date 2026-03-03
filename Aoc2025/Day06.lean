import Std.Internal.Parsec.String
import Aoc2025.Utils.Grid

open Std.Internal.Parsec.String

namespace Day06


inductive Op where | Add | Mul deriving DecidableEq

namespace Op

def parser : Parser Op := (skipChar '+' *> pure Op.Add) <|> (skipChar '*' *> pure Op.Mul)

end Op

structure Problem where
  op : Op
  numbers : List Nat

namespace Problem

def parseLines (lines : Array String) : Except String (List Problem) := do
  let back ← lines.back?.getDM (throw "given array of lines was empty")
  let ops ← Parser.run (Std.Internal.Parsec.many (ws *> Op.parser <* ws)) back
  let lines := lines.pop
  let numbers ← lines.mapM (Parser.run (Std.Internal.Parsec.many (ws *> digits <* ws)))
  let numbers := (numbers.toList.map (·.toList)).transpose
  return ops.toList.zipWith Problem.mk numbers

def parseNatOption : Parser (Option Nat) := do
  ws
  let isEof ← Std.Internal.Parsec.isEof
  if isEof then
    return none
  else
    digits

def parseColumns (lines : Array String) : Except String (List Problem) := do
  let back ← lines.back?.getDM (throw "given array of lines was empty")
  let ops ← Parser.run (Std.Internal.Parsec.many (ws *> Op.parser <* ws)) back
  let lines := (lines.pop.map String.toList).toList.transpose.map String.ofList
  let numbers ← lines.mapM parseNatOption.run
  let numbers := (numbers.splitOn none).map List.reduceOption
  return ops.toList.zipWith Problem.mk numbers

def solve (p : Problem) : Nat :=
  match p.op with
  | .Add => p.numbers.sum
  | .Mul => p.numbers.prod

end Problem

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day06/test.txt")
  let problems ← IO.ofExcept (Problem.parseLines lines)
  println! "Test: {(problems.map Problem.solve).sum}"
  println! "Expected: {4277556}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day06/task.txt")
  let problems ← IO.ofExcept (Problem.parseLines lines)
  println! "Task: {(problems.map Problem.solve).sum}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day06/test.txt")
  let problems ← IO.ofExcept (Problem.parseColumns lines)
  println! "Test: {(problems.map Problem.solve).sum}"
  println! "Expected: {3263827}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day06/task.txt")
  let problems ← IO.ofExcept (Problem.parseColumns lines)
  println! "Task: {(problems.map Problem.solve).sum}"

end Task2

def main : IO Unit := do
  println! "Day 6"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day06

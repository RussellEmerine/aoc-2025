import Std.Internal.Parsec.String
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Finset.Nat

open Std.Internal.Parsec.String

-- an inclusive range
structure Range where
  start : ℕ
  stop : ℕ
  h : start ≤ stop
deriving DecidableEq

namespace Range

def toSet (range : Range) : Set ℕ := Set.Ico range.start range.stop.succ

instance : Membership ℕ Range where
  mem r i := i ∈ r.toSet

instance (range : Range) (n : ℕ) : Decidable (n ∈ range) :=
  Set.decidableMemIco

theorem mem_range_iff (range : Range) (n : ℕ)
: n ∈ range ↔ n ∈ Set.Ico range.start range.stop.succ := by rfl

def toFinset (range : Range) : Finset ℕ := Finset.Ico range.start range.stop.succ

theorem mem_toFinset_iff (range : Range) (n : ℕ)
: n ∈ range.toFinset ↔ n ∈ range := by simp [toFinset, mem_range_iff]

-- number of numbers in the range
def length (r : Range) : Nat := r.stop.succ - r.start

theorem card_toFinset (r : Range) : r.toFinset.card = r.length := Nat.card_Ico _ _

def parser : Parser Range := do
  let start ← digits
  skipString "-"
  let stop ← digits
  if h : start ≤ stop then
    return { start, stop, h }
  else
    Std.Internal.Parsec.fail "range was out of order"

end Range

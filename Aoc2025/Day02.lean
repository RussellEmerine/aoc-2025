import Std.Internal.Parsec.String
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Bool.AllAny
import Std.Data.HashSet.Lemmas

open Std.Internal.Parsec.String

namespace Day02

-- an inclusive range
structure Range where
  start : ℕ
  stop : ℕ
  h : start ≤ stop

namespace Range

def set (range : Range) : Set ℕ := Set.Ico range.start range.stop.succ

instance : Membership ℕ Range where
  mem r i := i ∈ r.set

instance (range : Range) (n : ℕ) : Decidable (n ∈ range) :=
  Set.decidableMemIco

theorem mem_range_iff (range : Range) (n : ℕ)
: n ∈ range ↔ n ∈ Set.Ico range.start range.stop.succ := by rfl

def parser : Parser (Array Range) :=
  Std.Internal.Parsec.many <| do
    let start ← digits
    skipString "-"
    let stop ← digits
    let () ← skipString "," <|> pure ()
    if h : start ≤ stop then
      return { start, stop, h }
    else
      Std.Internal.Parsec.fail "range was out of order"

end Range

def repeatDigits (n : ℕ) : ℕ → ℕ
| 0 => 0
| x + 1 => n + 10 ^ (Nat.digits 10 n).length * repeatDigits n x

lemma digits_getLast_ne_zero (b : ℕ) (n : ℕ) (h : 1 < b) (p : b.digits n ≠ [])
: (b.digits n).getLast p ≠ 0 := by
  rw [Nat.lt_iff_add_one_le, le_iff_exists_add] at h
  rcases h with ⟨b, h⟩
  rw [add_comm, ← add_assoc, Nat.add_one, Nat.add_one] at h
  subst h
  unfold Nat.digits at p ⊢
  simp [-ne_eq] at p ⊢
  fun_induction Nat.digitsAux
  case case1 =>
    contradiction
  case case2 n ih =>
    revert p
    by_cases h : (b + 2).digitsAux (by simp) ((n + 1) / (b + 2)) = []
    case pos =>
      rw [h]
      intro p
      rw [List.getLast_singleton]
      have hh := @Nat.digits_eq_nil_iff_eq_zero (b + 2) ((n + 1) / (b + 2))
      simp [Nat.digits] at hh
      rw [hh] at h
      rw [← Nat.pos_iff_ne_zero]
      apply Nat.emod_pos_of_not_dvd
      apply Nat.not_dvd_of_pos_of_lt
      · simp
      · simp [h]
    case neg =>
      intro p
      rw [List.getLast_cons h]
      exact ih h

theorem repeatDigits_digits (n : ℕ) (x : ℕ)
: Nat.digits 10 (repeatDigits n x) = (List.replicate x (Nat.digits 10 n)).flatten := by
  induction x
  case zero =>
    simp [repeatDigits]
  case succ x hx =>
    simp [repeatDigits, List.replicate_succ]
    have : Nat.ofDigits 10 (Nat.digits 10 (n + 10 ^ (Nat.digits 10 n).length * repeatDigits n x))
        = Nat.ofDigits 10 (Nat.digits 10 n ++ (List.replicate x (Nat.digits 10 n)).flatten) := by
      rw [Nat.ofDigits_digits, Nat.ofDigits_append, Nat.ofDigits_digits, ← hx, Nat.ofDigits_digits]
    replace this := congrArg (Nat.digits 10) this
    rw [Nat.digits_ofDigits _ (by simp), Nat.digits_ofDigits _ (by simp)] at this
    · exact this
    · intro l hl
      rw [List.mem_append, List.mem_flatten] at hl
      cases hl
      case inl hl =>
        exact Nat.digits_lt_base (by simp) hl
      case inr hl =>
        rcases hl with ⟨l₁, hl₁, hl⟩
        rw [List.mem_replicate] at hl₁
        rcases hl₁ with ⟨hl₁, rfl⟩
        exact Nat.digits_lt_base (by simp) hl
    · intro h
      rw [ne_eq, List.getLast_eq_iff_getLast?_eq_some, ← List.flatten_cons, ← List.replicate_succ]
      simp
      by_cases h : Nat.digits 10 n = []
      case pos =>
        rw [h]
        simp
      case neg =>
        rw [List.getLast?_eq_some_getLast h, Option.some_inj]
        exact digits_getLast_ne_zero _ _ (by simp) h
    · intro l hl
      exact Nat.digits_lt_base (by simp) hl
    · intro h
      exact digits_getLast_ne_zero _ _ (by simp) h

theorem repeatDigits_len (n : ℕ) (x : ℕ)
: (Nat.digits 10 (repeatDigits n x)).length = x * (Nat.digits 10 n).length := by
  rw [repeatDigits_digits, List.length_flatten, List.map_replicate, List.sum_replicate_nat]

def is_invalid (n : ℕ) (x : ℕ) := ∃ m, n = repeatDigits m x

theorem is_invalid_lt_iff (x : ℕ) (hx : 0 < x) (le : n < 10 ^ (x * k))
: is_invalid n x ↔ ∃ m < 10 ^ k, n = repeatDigits m x := by
  constructor
  case mp =>
    rintro ⟨m, rfl⟩
    refine ⟨m, ?_, rfl⟩
    suffices (Nat.digits 10 m).length ≤ k by
      apply lt_of_lt_of_le (Nat.lt_base_pow_length_digits (by simp : 1 < 10))
      exact Nat.pow_le_pow_of_le (by simp) this
    by_cases m = 0
    case pos hm =>
      subst hm
      simp
    case neg hm =>
      rw [← ne_eq, ← Nat.pos_iff_ne_zero] at hm
      rw [← Nat.digits_length_le_iff (by simp)] at le
      rw [repeatDigits_len] at le
      rw [Nat.mul_le_mul_left_iff hx] at le
      exact le
  case mpr =>
    rintro ⟨m, hm, rfl⟩
    use m

def maxLength (x : ℕ) (ranges : List Range) (h : ranges ≠ []) : ℕ :=
  ranges.map (fun r => (Nat.log 10 r.stop + 1) / x) |>.max (by simpa)

def getInvalid (x : ℕ) (ranges : List Range) (h : ranges ≠ []) : List ℕ :=
  (List.range (10 ^ maxLength x ranges h)).map (repeatDigits · x) |>.filter (fun n => ranges.any (n ∈ ·))

theorem getInvalid_complete (n : ℕ) (x : ℕ) (hx : 0 < x) (h : ranges ≠ [])
: n ∈ getInvalid x ranges h ↔ is_invalid n x ∧ ranges.any (n ∈ ·) := by
  constructor
  case mp =>
    rw [getInvalid, is_invalid, List.mem_filter, List.mem_map]
    rintro ⟨⟨m, hm, rfl⟩, hn⟩
    exact ⟨⟨m, rfl⟩, hn⟩
  case mpr =>
    rw [getInvalid, is_invalid, List.mem_filter, List.mem_map]
    rintro ⟨⟨m, rfl⟩, hn⟩
    refine ⟨⟨m, ?_, rfl⟩, hn⟩
    rw [List.mem_range, maxLength]
    rw [← Nat.digits_length_le_iff (by simp)]
    rw [List.any_iff_exists_prop] at hn
    rcases hn with ⟨r, hr, hn⟩
    refine le_trans ?_ (List.le_max_of_mem (List.mem_map.mpr ⟨r, hr, rfl⟩))
    rw [Range.mem_range_iff, Set.mem_Ico, Nat.lt_succ_iff] at hn
    rw [Nat.le_div_iff_mul_le hx, mul_comm]
    rw [← repeatDigits_len]
    by_cases r.stop = 0
    case pos hs =>
      rw [hs] at hn ⊢
      rw [Nat.le_zero] at hn
      rw [hn.right]
      simp
    case neg hs =>
      rw [← Nat.digits_len _ _ (by simp) hs]
      exact Nat.le_digits_len_le _ _ _ hn.right

namespace Task1

def main : IO Unit := do
  let test ← IO.FS.readFile (System.FilePath.mk "Data/Day02/test.txt")
  let ranges ← IO.ofExcept (Range.parser.run test)
  if h : ranges.toList ≠ [] then do
    println! "Test: {getInvalid 2 ranges.toList h |>.sum}"
    println! "Expected: {1227775554}"
  else do
    println! "list of ranges was empty - parsing error?"
  let data ← IO.FS.readFile (System.FilePath.mk "Data/Day02/task.txt")
  let ranges ← IO.ofExcept (Range.parser.run data)
  if h : ranges.toList ≠ [] then do
    println! "Task: {getInvalid 2 ranges.toList h |>.sum}"
  else do
    println! "list of ranges was empty - parsing error?"

end Task1

namespace Task2

-- if n = 0 then any x works, so we have to restrict it to be small enough
def is_invalid' (n : ℕ) := if n = 0 then True else ∃ x > 1, is_invalid n x

def maxLength' (ranges : List Range) (h : ranges ≠ []) : ℕ :=
  max 3 (ranges.map (fun r => (Nat.digits 10 r.stop.succ).length + 1) |>.max (by simpa))

def getInvalid' (ranges : List Range) (h : ranges ≠ []) : Std.HashSet ℕ :=
  Std.HashSet.ofList <| (2...maxLength' ranges h).toList.flatMap (getInvalid · ranges h)

theorem getInvalid'_complete (n : ℕ) (h : ranges ≠ [])
: n ∈ getInvalid' ranges h ↔ is_invalid' n ∧ ranges.any (n ∈ ·) := by
  simp [getInvalid', Std.Rco.mem_toList_iff_mem, Std.Rco.mem_iff]
  constructor
  case mp =>
    intro ⟨x, ⟨hx₁, hx₂⟩, hn⟩
    rw [getInvalid_complete _ _ (by linarith)] at hn
    simp at hn
    rcases hn with ⟨hn, r, hr₁, hr₂⟩
    cases n
    case zero =>
      simp [is_invalid']
      use r
    case succ n =>
      simp [is_invalid']
      refine ⟨⟨x, hx₁, hn⟩, r, hr₁, hr₂⟩
  case mpr =>
    rintro ⟨hn, r, hr₁, hr₂⟩
    cases n
    case zero =>
      refine ⟨2, ⟨le_rfl, by simp [maxLength']⟩, ?_⟩
      rw [getInvalid_complete _ _ (by simp)]
      simp [is_invalid]
      refine ⟨⟨0, ?_⟩, r, hr₁, hr₂⟩
      simp [repeatDigits]
    case succ n =>
      simp [is_invalid'] at hn
      rcases hn with ⟨x, hx₁, m, hm⟩
      rw [hm] at hr₂ ⊢
      replace hm : 0 < m := by
        by_contra!
        rw [nonpos_iff_eq_zero] at this
        subst this
        replace hm := congrArg (Nat.digits 10) hm
        rw [repeatDigits_digits] at hm
        simp at hm
      refine ⟨x, ⟨by linarith, ?_⟩, ?_⟩
      · by_contra!
        rw [maxLength', max_le_iff, List.max_le_iff] at this
        rcases this with ⟨hx₁, this⟩
        specialize this _ (List.mem_map.mpr ⟨r, hr₁, rfl⟩)
        rw [Range.mem_range_iff, Set.mem_Ico] at hr₂
        have hh := Nat.le_digits_len_le 10 _ _ (le_of_lt hr₂.right)
        rw [repeatDigits_len] at hh
        replace this := lt_of_le_of_lt hh this
        conv at this =>
          rhs
          rw [← Nat.mul_one x]
        rw [Nat.mul_lt_mul_left] at this
        · simp [Nat.digits_eq_nil_iff_eq_zero] at this
          linarith
        · linarith
      · rw [getInvalid_complete _ _ (by linarith)]
        simp [is_invalid]
        refine ⟨⟨m, rfl⟩, r, hr₁, hr₂⟩

def main : IO Unit := do
  let test ← IO.FS.readFile (System.FilePath.mk "Data/Day02/test.txt")
  let ranges ← IO.ofExcept (Range.parser.run test)
  if h : ranges.toList ≠ [] then do
    println! "Test: {getInvalid' ranges.toList h |>.toList.sum}"
    println! "Expected: {4174379265}"
  else do
    println! "list of ranges was empty - parsing error?"
  let data ← IO.FS.readFile (System.FilePath.mk "Data/Day02/task.txt")
  let ranges ← IO.ofExcept (Range.parser.run data)
  if h : ranges.toList ≠ [] then do
    println! "Task: {getInvalid' ranges.toList h |>.toList.sum}"
  else do
    println! "list of ranges was empty - parsing error?"

end Task2

def main : IO Unit := do
  println! "Day 2"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day02

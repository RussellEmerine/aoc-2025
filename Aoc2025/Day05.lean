import Mathlib.Data.List.Chain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Batteries.Data.List.Basic
import Aoc2025.Utils.Range

namespace Day05

def parse (lines: List String) : Except String (List Range × List Nat) := do
  if let [pre, suf] := lines.splitOn "" then
    let ranges ← pre.mapM Range.parser.run
    let ids ← suf.mapM Std.Internal.Parsec.String.digits.run
    return (ranges, ids)
  else
    Except.error "file did not split at empty line into two parts"

def countFresh (ranges : List Range) (ids : List Nat) : Nat :=
  ids.countP fun id => ranges.any (id ∈ ·)

namespace RangeList

-- equivalently could use IsChain
def is_rangeList (rs : List Range) : Prop :=
  rs.Pairwise (·.stop < ·.start)

theorem is_rangeList_nil : is_rangeList [] := List.Pairwise.nil

theorem is_rangeList_cons
: is_rangeList (r :: rs) ↔ (∀ r' ∈ rs, r.stop < r'.start) ∧ is_rangeList rs :=
  List.pairwise_cons

def merge (r₁ r₂ : Range) : Range where
  start := min r₁.start r₂.start
  stop := max r₁.stop r₂.stop
  h := (min_le_left _ _).trans (r₁.h.trans (le_max_left _ _))

theorem mem_merge_left (h : n ∈ r₁) (r₂) : n ∈ merge r₁ r₂ := by
  simp [Range.mem_range_iff, merge, Nat.lt_add_one_iff] at *
  exact ⟨Or.inl h.left, Or.inl h.right⟩

theorem mem_merge_right (r₁) (h : n ∈ r₂) : n ∈ merge r₁ r₂ := by
  simp [Range.mem_range_iff, merge, Nat.lt_add_one_iff] at *
  exact ⟨Or.inr h.left, Or.inr h.right⟩

def insert (r : Range) : List Range → List Range
| [] => [r]
| r' :: rs =>
  if r'.stop < r.start then
    r' :: insert r rs
  else if r.stop < r'.start then
    r :: r' :: rs
  else
    insert (merge r r') rs

theorem start_mem_insert (r : Range) (rs : List Range) (start : Nat)
  (h : start ∈ (insert r rs).map (·.start))
: start = r.start ∨ start ∈ rs.map (·.start) := by
  induction rs generalizing r
  case nil =>
    simp [insert] at h
    exact Or.inl h
  case cons r' rs ih =>
    rw [List.map_cons, List.mem_cons, List.mem_map]
    simp [insert] at h
    rcases h with ⟨a, ha, rfl⟩
    split_ifs at ha
    case pos h =>
      rw [List.mem_cons] at ha
      rcases ha with rfl | ha
      case inl =>
        exact Or.inr (Or.inl rfl)
      case inr =>
        specialize ih r ?_
        · rw [List.mem_map]
          exact ⟨a, ha, rfl⟩
        cases ih
        case inl ih =>
          exact Or.inl ih
        case inr ih =>
          rw [List.mem_map] at ih
          exact Or.inr (Or.inr ih)
    case pos h₁ h₂ =>
      rw [List.mem_cons, List.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      case inl =>
        exact Or.inl rfl
      case inr.inl =>
        exact Or.inr (Or.inl rfl)
      case inr.inr =>
        exact Or.inr (Or.inr ⟨a, ha, rfl⟩)
    case neg h₁ h₂ =>
      specialize ih _ (List.mem_map.mpr ⟨_, ha, rfl⟩)
      cases ih
      case inl ih =>
        simp [merge] at ih
        rw [ih]
        grind
      case inr ih =>
        rw [List.mem_map] at ih
        exact Or.inr (Or.inr ih)

theorem is_rangeList_insert (r : Range) (rs : List Range) (hrs : is_rangeList rs)
: is_rangeList (insert r rs) := by
  induction rs generalizing r
  case nil =>
    simp [is_rangeList, insert]
  case cons r' rs ih =>
    rw [is_rangeList_cons] at hrs
    rw [insert]
    split_ifs
    case pos h =>
      rw [is_rangeList_cons]
      refine ⟨?_, ih r hrs.right⟩
      intro a ha
      replace ha := start_mem_insert r rs a.start (List.mem_map.mpr ⟨a, ha, rfl⟩)
      cases ha
      case inl ha =>
        rw [ha]
        exact h
      case inr ha =>
        rw [List.mem_map] at ha
        rcases ha with ⟨a', ha', ha⟩
        rw [← ha]
        exact hrs.left _ ha'
    case pos h₁ h₂ =>
      simp [is_rangeList_cons]
      refine ⟨⟨h₂, ?_⟩, hrs⟩
      intro a ha
      exact h₂.trans (r'.h.trans_lt (hrs.left _ ha))
    case neg h₁ h₂ =>
      exact ih _ hrs.right

theorem mem_insert (n : Nat) (r : Range) (rs : List Range) (hrs : is_rangeList rs)
: (∃ a ∈ insert r rs, n ∈ a) ↔ n ∈ r ∨ ∃ a ∈ rs, n ∈ a := by
  induction rs generalizing r
  case nil =>
    simp [insert]
  case cons r' rs ih =>
    simp [insert]
    split_ifs
    case pos h =>
      constructor
      case mp =>
        rintro ⟨a, ha, hn⟩
        rw [List.mem_cons] at ha
        rcases ha with rfl | ha
        case inl =>
          exact Or.inr (Or.inl hn)
        case inr =>
          rw [is_rangeList_cons] at hrs
          specialize ih r hrs.right
          replace ih := ih.mp ⟨a, ha, hn⟩
          cases ih
          case inl hr =>
            exact Or.inl hr
          case inr hr =>
            exact Or.inr (Or.inr hr)
      case mpr =>
        intro hn
        conv =>
          congr
          ext
          rw [List.mem_cons]
        rw [is_rangeList_cons] at hrs
        specialize ih r hrs.right
        rcases hn with hn | hn | hn
        case inl =>
          replace ih := ih.mpr (Or.inl hn)
          rcases ih with ⟨a, ha, hn⟩
          exact ⟨a, Or.inr ha, hn⟩
        case inr.inl =>
          exact ⟨r', Or.inl rfl, hn⟩
        case inr.inr =>
          replace ih := ih.mpr (Or.inr hn)
          rcases ih with ⟨a, ha, hn⟩
          exact ⟨a, Or.inr ha, hn⟩
    case pos h₁ h₂ =>
      constructor
      case mp =>
        rintro ⟨a, ha, hn⟩
        rw [List.mem_cons, List.mem_cons] at ha
        rcases ha with rfl | rfl | ha
        case inl =>
          exact Or.inl hn
        case inr.inl =>
          exact Or.inr (Or.inl hn)
        case inr.inr =>
          exact Or.inr (Or.inr ⟨a, ha, hn⟩)
      case mpr =>
        intro hn
        conv =>
          congr
          ext
          rw [List.mem_cons, List.mem_cons]
        rcases hn with hn | hn | ⟨a, ha, hn⟩
        case inl =>
          exact ⟨r, Or.inl rfl, hn⟩
        case inr.inl =>
          exact ⟨r', Or.inr (Or.inl rfl), hn⟩
        case inr.inr =>
          exact ⟨a, Or.inr (Or.inr ha), hn⟩
    case neg h₁ h₂ =>
      rw [is_rangeList_cons] at hrs
      constructor
      case mp =>
        rintro ⟨a, ha, hn⟩
        replace ih := (ih _ hrs.right).mp ⟨a, ha, hn⟩
        rcases ih with hn | hn
        case inl =>
          simp [Range.mem_range_iff, Nat.lt_add_one_iff, merge] at hn
          rcases hn with ⟨hn₁ | hn₁, hn₂ | hn₂⟩
          case inl.inl =>
            left
            rw [Range.mem_range_iff, Set.mem_Ico, Nat.lt_succ_iff]
            exact ⟨hn₁, hn₂⟩
          case inl.inr =>
            by_cases n ≤ r.stop
            case pos hn₃ =>
              left
              rw [Range.mem_range_iff, Set.mem_Ico, Nat.lt_succ_iff]
              exact ⟨hn₁, hn₃⟩
            case neg hn₃ =>
              right ; left
              rw [Range.mem_range_iff, Set.mem_Ico, Nat.lt_succ_iff]
              push_neg at *
              exact ⟨le_of_lt (h₂.trans_lt hn₃), hn₂⟩
          case inr.inl =>
            push_neg at *
            by_cases n ≤ r'.stop
            case pos hn₃ =>
              right ; left
              rw [Range.mem_range_iff, Set.mem_Ico, Nat.lt_succ_iff]
              exact ⟨hn₁, hn₃⟩
            case neg hn₃ =>
              left
              rw [Range.mem_range_iff, Set.mem_Ico, Nat.lt_succ_iff]
              push_neg at *
              exact ⟨le_of_lt (h₁.trans_lt hn₃), hn₂⟩
          case inr.inr =>
            right ; left
            rw [Range.mem_range_iff, Set.mem_Ico, Nat.lt_succ_iff]
            exact ⟨hn₁, hn₂⟩
        case inr =>
          exact Or.inr (Or.inr hn)
      case mpr =>
        intro hn
        rcases hn with hn | hn | hn
        case inl =>
          exact (ih (merge r r') hrs.right).mpr (Or.inl (mem_merge_left hn _))
        case inr.inl =>
          exact (ih (merge r r') hrs.right).mpr (Or.inl (mem_merge_right _ hn))
        case inr.inr =>
          exact (ih (merge r r') hrs.right).mpr (Or.inr hn)

def joinRanges (rs : List Range) : List Range :=
  rs.foldr insert []

@[simp]
def joinRanges_nil : joinRanges [] = [] := rfl

@[simp]
def joinRanges_cons : joinRanges (r :: rs) = insert r (joinRanges rs) := rfl

theorem joinRanges_is_rangeList : is_rangeList (joinRanges rs) := by
  induction rs
  case nil =>
    simp [is_rangeList_nil]
  case cons r rs ih =>
    exact is_rangeList_insert _ _ ih

theorem mem_joinRanges
: (joinRanges rs).any (n ∈ ·) ↔ rs.any (n ∈ ·) := by
  induction rs
  case nil =>
    simp
  case cons r rs ih =>
    simp at *
    rw [mem_insert _ _ _ joinRanges_is_rangeList, ih]

def toFinset (rs : List Range) : Finset Nat :=
  rs.toFinset.biUnion Range.toFinset

theorem mem_toFinset (rs : List Range) (n : Nat)
: n ∈ toFinset rs ↔ rs.any (n ∈ ·) := by
  simp [toFinset, Range.mem_toFinset_iff]

def length (rs : List Range) : Nat := (rs.map (·.length)).sum

lemma pairwise_or {R : α → α → Prop} {l : List α}
  (h : l.Pairwise R) (h₁ : a₁ ∈ l) (h₂ : a₂ ∈ l) (ha : a₁ ≠ a₂)
: R a₁ a₂ ∨ R a₂ a₁ := by
  replace h : l.Pairwise fun x y => R x y ∨ R y x := by
    apply h.imp
    intro a b h
    exact Or.inl h
  apply h.forall _ h₁ h₂ ha
  intro a b h
  exact h.symm

theorem length_eq_card_toFinset (hrs : is_rangeList rs)
: length rs = (toFinset rs).card := by
  rw [length, toFinset, Finset.card_biUnion ?_, List.sum_toFinset]
  · congr
    ext r
    rw [Range.card_toFinset]
  · apply hrs.imp
    rintro r _ hr rfl
    exact (not_lt.mpr r.h) hr
  · rw [Finset.pairwiseDisjoint_iff]
    rintro r₁ hr₁ r₂ hr₂ ⟨n, hn⟩
    by_contra h
    rw [Finset.mem_coe, List.mem_toFinset] at hr₁ hr₂
    simp [Range.mem_toFinset_iff, Range.mem_range_iff] at hn
    have := pairwise_or hrs hr₁ hr₂ h
    cases this <;> grind

theorem length_joinRanges
: length (joinRanges rs) = (toFinset rs).card := by
  rw [length_eq_card_toFinset joinRanges_is_rangeList]
  congr 1
  ext n
  rw [mem_toFinset, mem_toFinset]
  rw [mem_joinRanges]

end RangeList

namespace Task1

def main : IO Unit := do
  let test ← IO.FS.lines (System.FilePath.mk "Data/Day05/test.txt")
  let (ranges, ids) ← IO.ofExcept (parse test.toList)
  println! "Test: {countFresh ranges ids}"
  println! "Expected: {3}"
  let task ← IO.FS.lines (System.FilePath.mk "Data/Day05/task.txt")
  let (ranges, ids) ← IO.ofExcept (parse task.toList)
  println! "Task: {countFresh ranges ids}"

end Task1

namespace Task2

def main : IO Unit := do
  let test ← IO.FS.lines (System.FilePath.mk "Data/Day05/test.txt")
  let (ranges, _) ← IO.ofExcept (parse test.toList)
  println! "Test: {RangeList.length (RangeList.joinRanges ranges)}"
  println! "Expected: {14}"
  let task ← IO.FS.lines (System.FilePath.mk "Data/Day05/task.txt")
  let (ranges, _) ← IO.ofExcept (parse task.toList)
  println! "Task: {RangeList.length (RangeList.joinRanges ranges)}"

end Task2

def main : IO Unit := do
  println! "Day 2"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day05

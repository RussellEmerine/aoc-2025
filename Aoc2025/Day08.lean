import Batteries.Data.Vector.Lemmas
import Aoc2025.Utils.UnionFind

namespace Day08

def vectorCount (f : α → Fin n) (xs : List α) : Vector Nat n :=
  xs.foldr (fun x v => v.set (f x) (v[f x] + 1)) (Vector.replicate n 0)

theorem vectorCount_nil {α n} {f : α → Fin n}
: vectorCount f [] = Vector.replicate n 0 := rfl

theorem vectorCount_cons {α n} {f : α → Fin n} {x xs}
: vectorCount f (x :: xs) = (vectorCount f xs).set (f x) ((vectorCount f xs)[f x] + 1) := rfl

theorem getElem_vectorCount {i : Fin n}
: (vectorCount f xs)[i] = xs.countP (f · = i) := by
  induction xs
  case nil =>
    simp [vectorCount_nil]
  case cons x xs ih =>
    rw [vectorCount_cons, Fin.getElem_fin, Vector.getElem_set, ← Fin.getElem_fin, List.countP_cons]
    simp only [decide_eq_true_iff, ← Fin.ext_iff]
    split_ifs
    case pos h =>
      subst h
      rw [ih]
    case neg h =>
      rw [ih, add_zero]

def rootComponentSizes (uf : UnionFind n) : Vector Nat n :=
  vectorCount uf.root (List.finRange n)

theorem getElem_rootComponentSizes' {i : Fin n}
: (rootComponentSizes uf)[i] = {j | uf.root j = i}.ncard := by
  rw [rootComponentSizes, getElem_vectorCount, List.countP_eq_length_filter, ← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  congr
  ext j
  simp

theorem getElem_rootComponentSizes {G : SimpleGraph (Fin n)} {i : Fin n} (h : uf.Equiv = G.Reachable)
: (rootComponentSizes uf)[i] = if i ∈ uf.roots then (G.connectedComponentMk i).supp.ncard else 0 := by
  rw [getElem_rootComponentSizes']
  split_ifs
  case pos hi =>
    rw [SimpleGraph.ConnectedComponent.supp]
    congr
    ext j
    rw [UnionFind.roots, Set.mem_ofPred, ← UnionFind.root_eq_self] at hi
    rw [SimpleGraph.ConnectedComponent.eq, ← h, UnionFind.Equiv, hi]
  case neg hi =>
    rw [Set.ncard_eq_zero]
    ext j
    rw [Set.mem_ofPred, Set.mem_empty_iff_false, iff_false]
    intro rfl
    rw [UnionFind.roots, Set.mem_ofPred, UnionFind.parent_root] at hi
    contradiction

def componentSizes (uf : UnionFind n) : List Nat :=
  let sizes := rootComponentSizes uf
  ((List.finRange n).filter (· ∈ uf.roots)).map (sizes[·])

structure JunctionBox where
  x : Int
  y : Int
  z : Int

namespace JunctionBox

def dist2 (a b : JunctionBox) : Nat :=
  ((a.x - b.x) ^ 2 + (a.y - b.y) ^ 2 + (a.z - b.z) ^ 2).natAbs

def parse (s : String) : Option JunctionBox :=
  if let some [x, y, z] := (s.splitOn ",").mapM String.toNat? then
    some { x, y, z }
  else
    none

def ofLines (lines : Array String) : Option (Array JunctionBox) :=
  lines.mapM parse

end JunctionBox

structure UnionFindComponents (n : Nat) where
  uf : UnionFind n
  components : Nat
  h : components = Fintype.card (Quotient uf.setoid)

namespace UnionFindComponents

def new (uf : UnionFind n) : UnionFindComponents n where
  uf
  components := (List.finRange n).countP (· ∈ uf.roots)
  h := by
    classical
    rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
    rw [← Nat.card_eq_finsetCard]
    simp only [List.toFinset_filter, decide_eq_true_eq, List.toFinset_finRange, Finset.mem_filter,
      Finset.mem_univ, true_and, Nat.card_eq_fintype_card]
    rw [Fintype.card_eq]
    refine ⟨⟨fun r => ⟦r⟧, Quotient.lift (fun i => ⟨uf.root i, ?_⟩) ?_, ?_, ?_⟩⟩
    · unfold UnionFind.roots
      rw [Set.mem_ofPred, UnionFind.parent_root]
    · intro i j hij
      simpa
    · intro ⟨r, hr⟩
      rw [UnionFind.roots, Set.mem_ofPred, ← UnionFind.root_eq_self] at hr
      simpa
    · intro a
      induction a using Quotient.ind
      case a i =>
        dsimp
        simp [Quotient.eq, UnionFind.setoid, UnionFind.equiv_root]

def union (self : UnionFindComponents n) (i j : Fin n) : UnionFindComponents n :=
  let p₁ := self.uf.find i
  let p₂ := p₁.fst.find j
  {
    uf := p₂.fst.union i j
    components := self.components - if p₁.snd = p₂.snd then 0 else 1
    h := by
      subst p₁ p₂
      split_ifs
      case pos h =>
        replace h : self.uf.Equiv i j := by
          apply (self.uf.find_equiv i).symm.trans
          rw [h, ← UnionFind.equiv_find i]
          apply UnionFind.find_equiv
        rw [Nat.sub_zero, self.h, Fintype.card_eq]
        refine ⟨⟨Quotient.lift (⟦·⟧) ?_, Quotient.lift (⟦·⟧) ?_, ?_, ?_⟩⟩
        · intro i' j' h'
          rw [UnionFind.setoid_equiv_iff] at h'
          rw [Quotient.eq, UnionFind.setoid]
          dsimp
          rw [UnionFind.equiv_union_of_equiv ?_]
          · rw [UnionFind.equiv_find, UnionFind.equiv_find]
            exact h'
          · rw [UnionFind.equiv_find, UnionFind.equiv_find]
            exact h
        · intro i' j' h'
          rw [UnionFind.setoid_equiv_iff] at h'
          rw [Quotient.eq, UnionFind.setoid]
          dsimp
          rw [UnionFind.equiv_union_of_equiv ?_] at h'
          . rw [UnionFind.equiv_find, UnionFind.equiv_find] at h'
            exact h'
          · rw [UnionFind.equiv_find, UnionFind.equiv_find]
            exact h
        · intro a
          induction a using Quotient.ind
          simp
        · intro a
          induction a using Quotient.ind
          simp
      case neg h =>
        replace h : ¬self.uf.Equiv i j := by
          contrapose h
          rw [UnionFind.find_root_2, UnionFind.find_root_2, UnionFind.find_root_1]
          exact h
        rw [self.h]
        rw [← Nat.add_one_inj, Nat.sub_one_add_one (by rw [Nat.ne_zero_iff_zero_lt, Fintype.card_pos_iff]; exact ⟨⟦i⟧⟩)]
        rw [← Fintype.card_option, Fintype.card_eq]
        refine ⟨⟨
          Quotient.lift (fun x => if self.uf.Equiv i x then none else some ⟦x⟧) ?_,
          Option.elim' ⟦i⟧ (Quotient.lift (fun x => if self.uf.Equiv i x then ⟦j⟧ else ⟦x⟧) ?_),
          ?_,
          ?_,
        ⟩⟩
        · intro i' j' h'
          split_ifs
          case pos hi' hj' =>
            rfl
          case neg hi' hj' =>
            exact hj' (hi'.trans h')
          case pos hi' hj' =>
            exact hi' (hj'.trans h'.symm)
          case neg hi' hj' =>
            congr 1
            rw [Quotient.eq, UnionFind.setoid]
            dsimp
            rw [UnionFind.equiv_union]
            left
            rw [UnionFind.equiv_find, UnionFind.equiv_find]
            assumption
        · intro i' j' h'
          rw [UnionFind.setoid_equiv_iff] at h'
          rw [UnionFind.equiv_union] at h'
          rcases h' with h' | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          case inl =>
            rw [UnionFind.equiv_find, UnionFind.equiv_find] at h'
            split_ifs
            case pos hi' hj' =>
              rfl
            case neg hi' hj' =>
              exact (hj' (hi'.trans h')).elim
            case pos hi' hj' =>
              exact (hi' (hj'.trans h'.symm)).elim
            case neg hi' hj' =>
              rw [Quotient.eq]
              exact h'
          case inr.inl =>
            rw [UnionFind.equiv_find, UnionFind.equiv_find] at h₁ h₂
            split_ifs
            case pos hi' hj' =>
              rfl
            case neg hi' hj' =>
              rw [Quotient.eq]
              exact h₂.symm
            case pos hi' hj' =>
              rw [Quotient.eq]
              exact h₁.trans (hj'.trans h₂)
            case neg hi' hj' =>
              exact (hi' h₁.symm).elim
          case inr.inr =>
            rw [UnionFind.equiv_find, UnionFind.equiv_find] at h₁ h₂
            split_ifs
            case pos hi' hj' =>
              rfl
            case neg hi' hj' =>
              exact (h (hi'.trans h₁)).elim
            case pos hi' hj' =>
              rw [Quotient.eq]
              exact h₁
            case neg hi' hj' =>
              exact (hj' h₂.symm).elim
        · intro a
          induction a using Quotient.ind
          case a i' =>
            rw [Quotient.lift_mk]
            split_ifs
            case pos h' =>
              rw [Option.elim'_none, Quotient.eq]
              exact h'
            case neg h' =>
              rw [Option.elim'_some, Quotient.lift_mk, ite_eq_right h']
        · intro o
          cases o
          case none =>
            simpa using UnionFind.Equiv.rfl
          case some a =>
            induction a using Quotient.ind
            case a i' =>
              dsimp
              split_ifs
              case pos h' =>
                rw [Quotient.lift_mk, ite_eq_right h, Option.some.injEq, Quotient.eq, UnionFind.setoid]
                dsimp
                rw [UnionFind.equiv_union]
                right ; right
                refine ⟨UnionFind.Equiv.rfl, ?_⟩
                rw [UnionFind.equiv_find, UnionFind.equiv_find]
                exact h'.symm
              case neg h' =>
                rw [Quotient.lift_mk, ite_eq_right h']
  }

end UnionFindComponents

def getPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun (i : Fin n) => (·, i) <$> (List.finRange i).map fun (j : Fin i) => j.castLE (le_of_lt i.is_lt)

def getSortedPairs (boxes : Array JunctionBox)
: List (Fin boxes.size × Fin boxes.size) :=
  let withDists := (getPairs boxes.size).map fun p => (boxes[p.fst].dist2 boxes[p.snd], p)
  let sortedWithDists := withDists.mergeSort (·.fst ≤ ·.fst)
  sortedWithDists.map Prod.snd

namespace Task1

def foldUnions (connections : List (Fin n × Fin n)) : UnionFind n :=
  (connections.foldl (fun uf p => uf.union p.fst p.snd) (UnionFind.empty n)).flatten

def solve (boxes : Array JunctionBox) (count : Nat) : Nat :=
  let pairs := (getSortedPairs boxes).take count
  let uf := foldUnions pairs
  let sizes := componentSizes uf
  let sorted := sizes.mergeSort (· ≥ ·)
  (sorted.take 3).prod

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day08/test.txt")
  let boxes ← IO.ofExcept <| (JunctionBox.ofLines lines).elim (Except.error "invalid file") Except.ok
  println! "Test: {solve boxes 10}"
  println! "Expected: {40}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day08/task.txt")
  let boxes ← IO.ofExcept <| (JunctionBox.ofLines lines).elim (Except.error "invalid file") Except.ok
  println! "Task: {solve boxes 1000}"

end Task1

namespace Task2

def solveFrom (uf : UnionFindComponents n) : List (Fin n × Fin n) → Option (Fin n × Fin n)
| [] => none
| (i, j) :: pairs =>
  let uf' := uf.union i j
  if uf'.components = 1 then
    (i, j)
  else
    solveFrom uf' pairs

def solve (boxes : Array JunctionBox) : Int :=
  -- TODO: doing this getSortedPairs twice is expensive and stupid - allow tasks to use the same input
  let pairs := getSortedPairs boxes
  let o := solveFrom (UnionFindComponents.new (UnionFind.empty boxes.size)) pairs
  o.elim 0 fun p => boxes[p.fst].x * boxes[p.snd].x

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day08/test.txt")
  let boxes ← IO.ofExcept <| (JunctionBox.ofLines lines).elim (Except.error "invalid file") Except.ok
  println! "Test: {solve boxes}"
  println! "Expected: {25272}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day08/task.txt")
  let boxes ← IO.ofExcept <| (JunctionBox.ofLines lines).elim (Except.error "invalid file") Except.ok
  println! "Task: {solve boxes}"

end Task2

def main : IO Unit := do
  println! "Day 8"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day08

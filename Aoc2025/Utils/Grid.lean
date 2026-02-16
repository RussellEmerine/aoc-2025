import Mathlib.Data.Nat.Dist

universe u

namespace Fin

def succ? (i : Fin n) : Option (Fin n) :=
  if h : i.val + 1 < n then some ⟨i.val + 1, h⟩ else none

def pred? (i : Fin n) : Option (Fin n) :=
  if i.val = 0 then none else some ⟨i.val.pred, lt_of_le_of_lt i.val.pred_le i.isLt⟩

theorem pred?_succ? (i j : Fin n) : i.pred? = some j ↔ j.succ? = some i := by
  simp [pred?, succ?]
  grind

end Fin

abbrev Grid (α : Type u) (m n : Nat) := Vector (Vector α n) m

namespace Grid

def ofArrays (arrays: Array (Array α))
: Option ((m : Nat) × (n : Nat) × Grid α m n) :=
  if h₁ : 0 < arrays.size then
    if h₂ : arrays.all (·.size = arrays[0].size) then
      let vec :=
        arrays.pmap
          (fun row h => row.toVector.cast h)
          (fun row h => of_decide_eq_true <| (Array.all_eq_true_iff_forall_mem.mp h₂) row h)
      some ⟨vec.size, arrays[0].size, vec.toVector⟩
    else
      none
  else
    none

def set (grid : Grid α m n) (i j : Nat) (a : α)
  (hi : i < m := by get_elem_tactic)
  (hj : j < n := by get_elem_tactic)
: Grid α m n :=
  Vector.set grid i (grid[i].set j a)

theorem getElem_set
  {grid : Grid α m n} {a : α}
  {i : Nat} (hi : i < m) {j : Nat} (hj : j < n)
  {i' : Nat} (hi' : i' < m) {j' : Nat} (hj : j' < n)
: (grid.set i j a)[i'][j'] = if (i, j) = (i', j') then a else grid[i'][j'] := by
  simp [Grid.set, Vector.getElem_set, apply_ite]
  grind

def neighbors4 (i : Fin m) (j : Fin n) : List (Fin m × Fin n) :=
  [
    (i.pred?, some j),
    (some i, j.succ?),
    (i.succ?, some j),
    (some i, j.pred?)
  ].filterMap fun (i, j) => i.bind fun i => j.map fun j => (i, j)

def neighbors8 (i : Fin m) (j : Fin n) : List (Fin m × Fin n) :=
  [
    (i.pred?, j.pred?),
    (i.pred?, some j),
    (i.pred?, j.succ?),
    (some i, j.succ?),
    (i.succ?, j.succ?),
    (i.succ?, some j),
    (i.succ?, j.pred?),
    (some i, j.pred?)
  ].filterMap fun (i, j) => i.bind fun i => j.map fun j => (i, j)

lemma neighbors8_nodup {m n} {i : Fin m} {j : Fin n} : (Grid.neighbors8 i j).Nodup := by
  unfold Grid.neighbors8 Fin.pred? Fin.succ?
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  by_cases h₁ : i + 1 < m
    <;> by_cases h₂ : j + 1 < n
    <;> cases i
    <;> cases j
    <;> simp [h₁, h₂]
    <;> grind

lemma mem_neighbors8_iff {m n} {i : Fin m} {j : Fin n} {i' : Fin m} {j' : Fin n}
: (i', j') ∈ Grid.neighbors8 i j ↔ (i, j) ∈ Grid.neighbors8 i' j' := by
  unfold Grid.neighbors8
  simp [List.mem_filterMap]
  constructor
  case mp =>
    intro h
    rcases h with h | h | h | h | h | h | h | h
      <;> simp [Option.bind_eq_some_iff, Option.map_eq_some_iff, Fin.pred?_succ?] at *
      <;> grind
  case mpr =>
    intro h
    rcases h with h | h | h | h | h | h | h | h
      <;> simp [Option.bind_eq_some_iff, Option.map_eq_some_iff, Fin.pred?_succ?] at *
      <;> grind

end Grid

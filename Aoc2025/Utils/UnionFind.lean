import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
import Mathlib.Combinatorics.SimpleGraph.Operations
import Batteries.Data.UnionFind.Lemmas

namespace SimpleGraph

variable {G : SimpleGraph V} {f : V → W}

theorem map_adj_inj (hf : f.Injective) (u v : W)
: (G.map f).Adj u v ↔ ∃ u' v', G.Adj u' v' ∧ f u' = u ∧ f v' = v := by
  rw [map_adj']
  simp
  intro x y h rfl rfl h'
  replace h' := hf h'
  subst h'
  exact G.ne_of_adj h rfl

theorem map_adj_inj_apply (hf : f.Injective) (u v : V)
: (G.map f).Adj (f u) (f v) ↔ G.Adj u v := by
  rw [map_adj_inj hf]
  constructor
  case mp =>
    rintro ⟨u', v', h, hu, hv⟩
    replace hu := hf hu
    replace hv := hf hv
    subst hu hv
    exact h
  case mpr =>
    intro h
    exact ⟨_, _, h, rfl, rfl⟩

theorem mem_range_of_adj (hf : f.Injective) (hfv : (G.map f).Adj x fv)
: fv ∈ Set.range f := by
  rw [SimpleGraph.map_adj_inj hf] at hfv
  rcases hfv with ⟨_, v, _, rfl, rfl⟩
  simp

noncomputable def unmapAdj (hf : f.Injective) (hfv : (G.map f).Adj x fv)
: V :=
  Classical.choose (mem_range_of_adj hf hfv)

theorem apply_unmapAdj (hf : f.Injective) (hfv : (G.map f).Adj x fv)
: f (unmapAdj hf hfv) = fv :=
  Classical.choose_spec (mem_range_of_adj hf hfv)

namespace Hom

def mapInj (G : SimpleGraph V) {f : V → W} (hf : f.Injective)
: G.Hom (G.map f) where
  toFun := f
  map_rel' := by
    intro u v h
    rw [map_adj_inj_apply hf]
    exact h

@[simp]
theorem coe_map {hf : f.Injective}
: (mapInj G hf : V → W) = f := rfl

end Hom

namespace Walk

noncomputable def unmap' (hf : f.Injective) (hu : fu = f u) (hv : fv = f v)
: (G.map f).Walk fu fv → G.Walk u v
| nil' fu => (nil' u).copy rfl (by subst hu ; exact hf hv)
| cons' fu fw fv h p =>
  cons' u (unmapAdj hf h) v
    (by
      subst hu hv
      rw [← apply_unmapAdj hf h, map_adj_inj_apply hf] at h
      exact h)
    (unmap' hf (apply_unmapAdj hf h).symm hv p)

noncomputable def unmap (hf : f.Injective)
: (G.map f).Walk (f u) (f v) → G.Walk u v :=
  unmap' hf rfl rfl

end Walk

namespace Reachable

theorem map_iff_apply (hf : f.Injective)
: (G.map f).Reachable (f u) (f v) ↔ G.Reachable u v := by
  constructor
  case mp =>
    intro ⟨w⟩
    exact ⟨Walk.unmap hf w⟩
  case mpr =>
    exact SimpleGraph.Reachable.map (Hom.mapInj G hf)

theorem map_iff (hf : f.Injective)
: (G.map f).Reachable fu fv ↔ fu = fv ∨ ∃ u v, G.Reachable u v ∧ f u = fu ∧ f v = fv := by
  constructor
  case mp =>
    intro ⟨w⟩
    by_cases w.Nil
    case pos hw =>
      cases hw
      exact Or.inl rfl
    case neg hw =>
      rcases SimpleGraph.Walk.not_nil_iff.mp hw with ⟨_, hu, _, _⟩
      rw [← SimpleGraph.Walk.nil_reverse] at hw
      rcases SimpleGraph.Walk.not_nil_iff.mp hw with ⟨_, hv, _, _⟩
      rcases (map_adj_inj hf _ _).mp hu with ⟨u', _, _, rfl, _⟩
      rcases (map_adj_inj hf _ _).mp hv with ⟨v', _, _, rfl, _⟩
      refine Or.inr ⟨_, _, ?_, rfl, rfl⟩
      exact ⟨Walk.unmap hf w⟩
  case mpr =>
    intro h
    cases h
    case inl h =>
      subst h
      exact SimpleGraph.Reachable.rfl
    case inr h =>
      rcases h with ⟨u, v, h, rfl, rfl⟩
      rw [map_iff_apply hf]
      exact h

theorem edge (u v : V)
: (SimpleGraph.edge u v).Reachable u v := by
  by_cases u = v
  case pos h =>
    subst h
    exact Reachable.rfl
  case neg h =>
    exact ((edge_adj u v u v).mpr ⟨Or.inl ⟨rfl, rfl⟩, h⟩).reachable

lemma sup_edge_of_notMem_support
  (hab : ¬G.Adj a b)
  (w : (G ⊔ SimpleGraph.edge a b).Walk u v)
  (hw : a ∉ w.support ∨ b ∉ w.support)
: G.Reachable u v := by
  have : (G ⊔ SimpleGraph.edge a b).deleteEdges {s(a, b)} = G := by
    simpa
  rw [← this, SimpleGraph.reachable_deleteEdges_iff_exists_walk]
  use w
  contrapose! hw
  exact ⟨w.mem_support_of_mem_edges hw (Sym2.mem_mk_left _ _), w.mem_support_of_mem_edges hw (Sym2.mem_mk_right _ _)⟩

theorem sup_edge (a b u v : V)
: (G ⊔ SimpleGraph.edge a b).Reachable u v ↔ G.Reachable u v ∨ G.Reachable u a ∧ G.Reachable v b ∨ G.Reachable u b ∧ G.Reachable v a := by
  classical
  by_cases G.Adj a b ∨ a = b
  case pos hab =>
    cases hab
    case inl hab =>
      rw [G.sup_edge_of_adj hab]
      constructor
      case mp =>
        intro h
        exact Or.inl h
      case mpr =>
        rintro (h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
        case inl =>
          exact h
        case inr.inl =>
          exact (h₁.trans hab.reachable).trans h₂.symm
        case inr.inr =>
          exact (h₁.trans hab.reachable.symm).trans h₂.symm
    case inr hab =>
      subst hab
      simp
      intro h₁ h₂
      exact h₁.trans h₂.symm
  case neg hab =>
    push Not at hab
    constructor
    case mp =>
      intro ⟨w⟩
      by_cases a ∈ w.support ∧ b ∈ w.support
      case pos hw =>
        rcases hw with ⟨ha, hb⟩
        have ha' : a ∈ w.reverse.support := by
          rwa [w.support_reverse, List.mem_reverse]
        have hb' : b ∈ w.reverse.support := by
          rwa [w.support_reverse, List.mem_reverse]
        by_cases h₁ : a ∈ (w.takeUntil b hb).support
        case pos =>
          replace h₁ := SimpleGraph.Walk.notMem_support_takeUntil_support_takeUntil_subset hab.right hb h₁
          by_cases h₂ : a ∈ (w.reverse.takeUntil b hb').support
          case pos =>
            replace h₂ := SimpleGraph.Walk.notMem_support_takeUntil_support_takeUntil_subset hab.right hb' h₂
            refine Or.inl (sup_edge_of_notMem_support hab.left ((w.takeUntil a ha).append (w.reverse.takeUntil a ha').reverse) ?_)
            simpa using ⟨h₁, h₂⟩
          case neg =>
            exact Or.inr (Or.inl ⟨sup_edge_of_notMem_support hab.left _ (Or.inr h₁), sup_edge_of_notMem_support hab.left _ (Or.inl h₂)⟩)
        case neg =>
          by_cases h₂ : a ∈ (w.reverse.takeUntil b hb').support
          case pos =>
            replace h₂ := SimpleGraph.Walk.notMem_support_takeUntil_support_takeUntil_subset hab.right hb' h₂
            exact Or.inr (Or.inr ⟨sup_edge_of_notMem_support hab.left _ (Or.inl h₁), sup_edge_of_notMem_support hab.left _ (Or.inr h₂)⟩)
          case neg =>
            refine Or.inl (sup_edge_of_notMem_support hab.left ((w.takeUntil b hb).append (w.reverse.takeUntil b hb').reverse) ?_)
            simpa using ⟨h₁, h₂⟩
      case neg hw =>
        rw [not_and_or] at hw
        exact Or.inl (sup_edge_of_notMem_support hab.left w hw)
    case mpr =>
      rintro (h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      case inl =>
        exact h.mono le_sup_left
      case inr.inl =>
        exact ((h₁.mono le_sup_left).trans ((edge a b).mono le_sup_right)).trans (h₂.mono le_sup_left).symm
      case inr.inr =>
        exact ((h₁.mono le_sup_left).trans ((edge a b).mono le_sup_right).symm).trans (h₂.mono le_sup_left).symm

end Reachable

end SimpleGraph

namespace Batteries.UnionFind.Equiv

theorem comm {self : UnionFind} (i j : Nat) : self.Equiv i j ↔ self.Equiv j i := ⟨symm, symm⟩

end Batteries.UnionFind.Equiv

structure UnionFind (n : Nat) where
  uf : Batteries.UnionFind
  huf : n = uf.size

namespace UnionFind

def push (self : UnionFind n) : UnionFind (n + 1) where
  uf := self.uf.push
  huf := by simp [Batteries.UnionFind.push, Batteries.UnionFind.size, self.huf]

def empty : (n : Nat) → UnionFind n
| 0 => { uf := Batteries.UnionFind.empty, huf := rfl }
| n + 1 => (empty n).push

def parent (self : UnionFind n) (i : Fin n) : Fin n where
  val := self.uf.parent i
  isLt := by
    rcases self with ⟨uf, rfl⟩
    simp [uf.parent_lt]

theorem parent_push_castSucc {self : UnionFind n} {i : Fin n}
: self.push.parent i.castSucc = (self.parent i).castSucc := by
  simp [parent, push]

theorem parent_push_last {self : UnionFind n}
: self.push.parent (Fin.last n) = Fin.last n := by
  rcases self with ⟨uf, rfl⟩
  ext
  simp [parent, push, Batteries.UnionFind.parent, Batteries.UnionFind.parentD]

theorem parent_empty {i : Fin n}
: (empty n).parent i = i := by
  induction n
  case zero =>
    simp [empty, parent]
  case succ n ih =>
    cases i using Fin.lastCases
    case last =>
      rw [empty, parent_push_last]
    case cast i =>
      rw [empty, parent_push_castSucc, ih]

def root (self : UnionFind n) (i : Fin n) : Fin n where
  val := self.uf.rootD i
  isLt := by
    rcases self with ⟨uf, rfl⟩
    simp [Batteries.UnionFind.rootD_lt]

theorem root_push_castSucc {self : UnionFind n} {i : Fin n}
: self.push.root i.castSucc = (self.root i).castSucc := by
  rcases self with ⟨uf, rfl⟩
  simp [root, push]

theorem root_push_last {self : UnionFind n}
: self.push.root (Fin.last n) = Fin.last n := by
  rcases self with ⟨uf, rfl⟩
  ext
  simp [root, push, Batteries.UnionFind.rootD_eq_self, Batteries.UnionFind.parent, Batteries.UnionFind.parentD]

theorem root_empty
: (empty n).root i = i := by
  induction n
  case zero =>
    simp [empty, root]
  case succ n ih =>
    cases i using Fin.lastCases
    case last =>
      simp [empty, root_push_last]
    case cast i =>
      simp [empty, root_push_castSucc, ih]

theorem parent_root (self : UnionFind n) (i : Fin n)
: self.parent (self.root i) = self.root i := by
  rcases self with ⟨uf, rfl⟩
  unfold parent root
  simp [Batteries.UnionFind.parent_rootD]

theorem root_parent (self : UnionFind n) (i : Fin n)
: self.root (self.parent i) = self.root i := by
  rcases self with ⟨uf, rfl⟩
  unfold parent root
  simp [Batteries.UnionFind.rootD_parent]

theorem root_eq_self (self : UnionFind n) (i : Fin n)
: self.root i = i ↔ self.parent i = i := by
  rcases self with ⟨uf, rfl⟩
  unfold parent root
  simp [Fin.ext_iff, uf.rootD_eq_self]

theorem root_root (self : UnionFind n) (i : Fin n)
: self.root (self.root i) = self.root i := by
  rcases self with ⟨uf, rfl⟩
  unfold root
  simp [uf.rootD_rootD]

def find (self : UnionFind n) (i : Fin n) : UnionFind n × Fin n :=
  match self with
  | { uf, huf } =>
    let pair := uf.findD i
    (
      {
        uf := pair.fst,
        huf := by
          subst pair huf
          simp [Batteries.UnionFind.findD]
      },
      {
        val := pair.snd
        isLt := by
          subst pair huf
          simp [Batteries.UnionFind.findD, uf.rootD_lt]
      }
    )

theorem find_root_1 (self : UnionFind n) (i j : Fin n)
: (self.find i).fst.root j = self.root j := by
  rcases self with ⟨uf, rfl⟩
  simp [find, root, Batteries.UnionFind.findD]

theorem find_root_2 (self : UnionFind n) (i : Fin n)
: (self.find i).snd = self.root i := by
  rcases self with ⟨uf, rfl⟩
  simp [find, root, Batteries.UnionFind.findD]

def union (self : UnionFind n) (i j : Fin n) : UnionFind n where
  uf := match self with | { uf, huf } => uf.unionN i j huf
  huf := by
    rcases self with ⟨uf, rfl⟩
    simp [Batteries.UnionFind.unionN, Batteries.UnionFind.union, Batteries.UnionFind.link, Batteries.UnionFind.size]

def flattenAux (self : UnionFind n) : List (Fin n) → UnionFind n
| [] => self
| i :: is => flattenAux (self.find i).fst is

theorem root_flattenAux (self : UnionFind n) (is : List (Fin n))
: (self.flattenAux is).root i = self.root i := by
  induction is generalizing self
  case nil =>
    simp [flattenAux]
  case cons j is ih =>
    simp [flattenAux, ih, find_root_1]

def flatten (self : UnionFind n) : UnionFind n :=
  self.flattenAux (List.finRange n)

theorem root_flatten (self : UnionFind n)
: self.flatten.root i = self.root i := self.root_flattenAux _

def Equiv (self : UnionFind n) (i j : Fin n) : Prop :=
  self.root i = self.root j

namespace Equiv

instance (self : UnionFind n) : DecidableRel self.Equiv := fun _ _ => decEq _ _

theorem rfl {self : UnionFind n} {i : Fin n}
: self.Equiv i i := Eq.refl _

theorem symm {self : UnionFind n} {i j : Fin n}
: self.Equiv i j → self.Equiv j i := Eq.symm

theorem trans {self : UnionFind n} {i j k : Fin n}
: self.Equiv i j → self.Equiv j k → self.Equiv i k := Eq.trans

theorem comm {self : UnionFind n} {i j : Fin n}
: self.Equiv i j ↔ self.Equiv j i := Eq.comm

theorem equivalence {self : UnionFind n} : Equivalence self.Equiv where
  refl _ := rfl
  symm
  trans

end Equiv

def setoid (self : UnionFind n) : Setoid (Fin n) where
  r := self.Equiv
  iseqv := UnionFind.Equiv.equivalence

instance (self : UnionFind n) : DecidableRel self.setoid.r := UnionFind.Equiv.instDecidableRelFin self

theorem setoid_equiv_iff (self : UnionFind n) (i j : Fin n)
: @HasEquiv.Equiv _ (@instHasEquivOfSetoid _ self.setoid) i j ↔ self.Equiv i j := by rfl

theorem equiv_empty {i j : Fin n}
: (empty n).Equiv i j ↔ i = j := by
  simp [Equiv, root_empty]

theorem equiv_push_cast {self : UnionFind n} {i j : Fin n}
: self.push.Equiv i.castSucc j.castSucc ↔ self.Equiv i j := by
  simp [Equiv, root_push_castSucc]

theorem not_equiv_push_cast_last {self : UnionFind n} {i : Fin n}
: ¬self.push.Equiv i.castSucc (Fin.last n) := by
  simp [Equiv, root_push_castSucc, root_push_last]

theorem equiv_push {self : UnionFind n} {i j : Fin (n + 1)}
: self.push.Equiv i j ↔ i = j ∨ ∃ u v, self.Equiv u v ∧ u.castSucc = i ∧ v.castSucc = j := by
  cases i using Fin.lastCases
  case last =>
    cases j using Fin.lastCases
    case last =>
      simp [Equiv.rfl]
    case cast j =>
      rw [Equiv.comm]
      simp [j.castSucc_ne_last.symm, not_equiv_push_cast_last]
  case cast i =>
    cases j using Fin.lastCases
    case last =>
      simp [not_equiv_push_cast_last]
    case cast j =>
      simp [equiv_push_cast]
      intro rfl
      exact Equiv.rfl

theorem equiv_flatten {self : UnionFind n}
: self.flatten.Equiv = self.Equiv := by
  unfold Equiv
  simp [root_flatten]

theorem equiv_root {self : UnionFind n} {i : Fin n}
: self.Equiv (self.root i) i := by
  simp [Equiv, root_root]

theorem equiv_iff {self : UnionFind n} {i j : Fin n}
: self.Equiv i j ↔ self.uf.Equiv i j := by
  simp [Equiv, Batteries.UnionFind.Equiv, root]

theorem equiv_find {self : UnionFind n} {i j : Fin n} (k : Fin n)
: (self.find k).fst.Equiv i j ↔ self.Equiv i j := by
  rcases self with ⟨uf, rfl⟩
  simp [find, equiv_iff, Batteries.UnionFind.findD, Batteries.UnionFind.equiv_find]

theorem find_equiv (self : UnionFind n) (i : Fin n)
: self.Equiv (self.find i).snd i := by
  unfold Equiv
  rw [find_root_2, root_root]

theorem equiv_union {self : UnionFind n} {i j x y : Fin n}
: (self.union x y).Equiv i j ↔ self.Equiv i j ∨ self.Equiv i x ∧ self.Equiv j y ∨ self.Equiv i y ∧ self.Equiv j x := by
  rcases self with ⟨uf, rfl⟩
  simp [equiv_iff, union, Batteries.UnionFind.unionN, Batteries.UnionFind.equiv_union, Batteries.UnionFind.Equiv.comm y j, Batteries.UnionFind.Equiv.comm x j]

theorem equiv_union_of_equiv {self : UnionFind n} {i j x y : Fin n} (h : self.Equiv x y)
: (self.union x y).Equiv i j ↔ self.Equiv i j := by
  rw [equiv_union]
  refine ⟨?_, Or.inl⟩
  intro hij
  rcases hij with hij | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  case inl =>
    assumption
  case inr.inl =>
    exact h₁.trans (h.trans h₂.symm)
  case inr.inr =>
    exact h₁.trans (h.symm.trans h₂.symm)

def roots (self : UnionFind n) : Set (Fin n) :=
  { i | self.parent i = i }

instance (uf : UnionFind n) (i : Fin n) : Decidable (i ∈ uf.roots) := by
  rw [roots, Set.mem_ofPred]
  apply decEq

theorem equiv_reachable_empty
: (UnionFind.empty n).Equiv = (SimpleGraph.emptyGraph (Fin n)).Reachable := by
  ext i j
  simp [equiv_empty]

theorem equiv_reachable_push {self : UnionFind n} {G : SimpleGraph (Fin n)} (h : self.Equiv = G.Reachable)
: self.push.Equiv = (G.map Fin.castSucc).Reachable := by
  ext i j
  simp [equiv_push, SimpleGraph.Reachable.map_iff (Fin.castSucc_injective _), h]

theorem equiv_reachable_union {self : UnionFind n} {G : SimpleGraph (Fin n)} (h : self.Equiv = G.Reachable)
: (self.union a b).Equiv = (G ⊔ SimpleGraph.edge a b).Reachable := by
  ext i j
  simp [equiv_union, SimpleGraph.Reachable.sup_edge, h]

theorem equiv_reachable_flatten {self : UnionFind n} {G : SimpleGraph (Fin n)} (h : self.Equiv = G.Reachable)
: self.flatten.Equiv = G.Reachable := by
  ext i j
  simp [equiv_flatten, h]

theorem roots_represents {self : UnionFind n} {G : SimpleGraph (Fin n)} (h : self.Equiv = G.Reachable)
: SimpleGraph.ConnectedComponent.Represents self.roots (Set.univ : Set G.ConnectedComponent) := by
  refine ⟨fun _ _ => by simp, ?_, ?_⟩
  · intro i hi j hj hij
    rw [roots, Set.mem_ofPred, ← root_eq_self] at hi hj
    rw [SimpleGraph.ConnectedComponent.eq, ← h, Equiv, hi, hj] at hij
    exact hij
  · intro c _
    induction c using SimpleGraph.ConnectedComponent.ind
    case h i hi =>
      refine ⟨self.root i, by simp [roots, self.parent_root], ?_⟩
      rw [SimpleGraph.ConnectedComponent.eq, ← h, Equiv, root_root]

def roots_equiv_quotient (self : UnionFind n)
: self.roots ≃ Quotient self.setoid where
  toFun r := ⟦r⟧
  invFun := Quotient.lift (fun i => ⟨self.root i, by simp [UnionFind.roots, UnionFind.parent_root]⟩) <| by
    intro i j h
    congr 1
  left_inv := by
    intro ⟨r, hr⟩
    rw [Quotient.lift_mk]
    congr
    rw [UnionFind.root_eq_self]
    exact hr
  right_inv := by
    intro a
    induction a using Quotient.ind
    case a i =>
      rw [Quotient.eq]
      unfold UnionFind.setoid
      simp [UnionFind.Equiv, UnionFind.root_root]

end UnionFind

-- Copyright 2022-2023 VMware, Inc.
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.DFinsupp.Defs
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Prod.Lex
/-!

# Z-sets

The type `Z[A]` is called a Z-set over elements of type A, which we can think of
as a collection of rows of type A. However, Z-sets are more general in that they
allow *integer multiplicities*; multiplicities greater than 1 correspond to
duplicates, while negative multiplicities correspond to retractions or
deletions. Hence `Z[A]` can be used not only to represent a table with rows of
type A but also changes to such a table.

Formally `Z[A]` is modeled as a function `A → ℤ` with finite support; that is,
only finitely many elements have non-zero multiplicity. This is necessary to
support well-defined summations over Z-sets.

`Z[A]` has a group structure that is essentially inherited from ℤ (the
operations are all pointwise). Similarly, it has a partial ordering where `m1 ≤
m2 := ∀ x, m1 x ≤ m2 x`.

Note that `Z[A]` is isomorphic to the free abelian group over `A`, so it is in a
formal sense the minimum needed to give `A` a group structure.

-/


-- SPDX-License-Identifier: BSD-2-Clause
variable {A B C : Type}

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- A Z-set is a function from A to ℤ with finite support.

This is implemented using dfinsupp; we use dfinsupp rather than finsupp since
its implementation is computable.
-/
def Zset (A : Type) :=
  Π₀ _ : A, ℤ

notation "Z[" T "]" => Zset T

namespace Zset

instance zsetGroup : AddCommGroup Z[A] := by
  unfold Zset;
  apply @DFinsupp.addCommGroup A (fun _ => ℤ) _

instance zsetFunLike : DFunLike Z[A] A fun _ : A => ℤ := by unfold Zset; infer_instance

omit [DecidableEq A] in
@[simp]
lemma Zset_zero_apply (a : A) : (0 : Z[A]) a = 0 := DFinsupp.zero_apply a

-- this next few definitions do some work to implement printing of Z-sets, which
-- is unused so far.
def graph (m : Z[A]) : Multiset (A × ℤ) :=
  m.support.val.map fun a => (a, m a)

def graphList [LinearOrder A] (m : Z[A]) : List (A ×ₗ ℤ) :=
  Multiset.sort (· ≤ ·) (graph m)

def elements [LinearOrder A] (m : Z[A]) : List A :=
  Multiset.sort (· ≤ ·) (m.sum fun a _ => {a})

instance hasToString [ToString A] [LinearOrder A] : ToString Z[A]
    where toString m := (List.map (fun xz : A × ℤ => xz) (graphList m)).toString

omit [DecidableEq A] in
@[simp]
theorem add_apply (m1 m2 : Z[A]) (a : A) : (m1 + m2) a = m1 a + m2 a :=
  rfl

omit [DecidableEq A] in
@[simp]
theorem sub_apply (m1 m2 : Z[A]) (a : A) : (m1 - m2) a = m1 a - m2 a :=
  rfl

omit [DecidableEq A] in
@[simp]
theorem neg_apply (m : Z[A]) (a : A) : (-m) a = -m a :=
  rfl

theorem add_support (m1 m2 : Z[A]) :
    (m1 + m2).support = (m1.support ∪ m2.support).filter fun a => m1 a + m2 a ≠ 0 :=
  by
  ext a; simp; rw [add_apply]; simp
  contrapose!
  intro h; cases' h with h1 h2; omega

theorem sub_support (m1 m2 : Z[A]) :
    (m1 - m2).support = (m1.support ∪ m2.support).filter fun a => m1 a - m2 a ≠ 0 :=
  by
  ext a; simp; rw [sub_apply]; simp
  contrapose!
  intro h; cases' h with h1 h2; omega

-- now we do some work so that `{a, b, c}` can be used to construct a Z-set
protected def empty : Z[A] :=
  DFinsupp.mk ∅ fun _ => 0

instance : EmptyCollection Z[A] where emptyCollection := Zset.empty

protected def single (a : A) : Z[A] :=
  DFinsupp.single a 1

instance : Singleton A Z[A] where singleton := Zset.single

protected def insert (a : A) (m : Z[A]) : Z[A] :=
  m + {a}

instance : Insert A Z[A] where insert := Zset.insert

@[simp]
theorem emptyCollection_apply (a : A) : (∅ : Z[A]) a = 0 :=
  rfl

@[simp]
theorem single_apply (a : A) (a' : A) : ({a} : Z[A]) a' = if a = a' then 1 else 0 :=
  by
  conv =>
    lhs; lhs
    change (Zset.single a)
  simp [Zset.single]; rw [DFinsupp.single_apply]; simp

@[simp]
theorem insert_apply (a : A) (m : Z[A]) (a' : A) :
    Insert.insert a m a' = m a' + if a = a' then 1 else 0 :=
  by
  conv =>
    lhs; lhs
    change Zset.insert a m
  unfold Zset.insert; simp

omit [DecidableEq A] in
@[ext]
theorem zset_ext (m1 m2 : Z[A]) : (∀ a, m1 a = m2 a) -> m1 = m2 := by
  intro h; apply DFinsupp.ext; apply h


instance : LawfulSingleton A Z[A] := by
  constructor
  intro x; ext a; simp

#eval graph ({"alice", "bob"} : Z[String])
#eval graph ({"alice"} - {"bob"} : Z[String])

-- TODO: data.dfinsupp.order does contain a partial_order, but it had some weird
-- behavior
instance po : PartialOrder Z[A] where
  le m1 m2 := ∀ a, m1 a ≤ m2 a
  le_refl := by intro m a; simp
  le_trans := by
    intro m1 m2 m3 h12 h23; intro a
    apply le_trans; apply h12; apply h23
  le_antisymm := by
    intro m1 m2 hle1 hle2
    ext a
    apply le_antisymm; apply hle1; apply hle2

-- TODO: how do I define `ordered_add_comm_group Z[A]` by just extending the existing
-- instances?
omit [DecidableEq A] in
theorem zset_le_ext (m1 m2 : Z[A]) : (m1 ≤ m2) = ∀ a, m1 a ≤ m2 a := rfl

instance zsetMem : Membership A Z[A] :=
  ⟨fun m a => a ∈ m.support⟩

theorem elem_eq (a : A) (m : Zset A) : (a ∈ m) = (a ∈ m.support) :=
  rfl

protected def fromSet (s : Finset A) : Z[A] :=
  DFinsupp.mk s fun _ => 1

@[simp]
theorem fromSet_0 : Zset.fromSet (∅ : Finset A) = DFinsupp.mk ∅ fun _ => 1 :=
  rfl

@[simp]
theorem fromSet_apply (s : Finset A) (a : A) : Zset.fromSet s a = if a ∈ s then 1 else 0 :=
  rfl

@[simp]
theorem fromSet_support (s : Finset A) : (Zset.fromSet s).support = s := by
  ext a; simp [Zset.fromSet]

protected def toSet (s : Z[A]) : Finset A :=
  s.support

@[simp]
theorem elem_toSet (a : A) (m : Z[A]) : a ∈ m.toSet ↔ a ∈ m := by rfl

@[simp]
theorem elem_fromSet (a : A) (s : Finset A) : a ∈ Zset.fromSet s ↔ a ∈ s := by rw [elem_eq]; simp

theorem to_fromSet (s : Finset A) [∀ a, Decidable (a ∈ s)] : (Zset.fromSet s).toSet = s := by
  ext a; simp

/-
  Unlike the paper, we use [is_bag] for the property on ℤ-sets, [fun_positive]
  for the property on functions, [positive] for streams, and [is_positive] for
  the property on operators.
-/
def IsSet (m : Z[A]) :=
  ∀ a, a ∈ m → m a = 1

def IsBag (m : Z[A]) :=
  0 ≤ m

def FunPositive (f : Z[A] → Z[B]) :=
  ∀ m, IsBag m → IsBag (f m)

def FunPositive2 (f : Z[A] → Z[B] → Z[C]) :=
  ∀ m1 m2, IsBag m1 → IsBag m2 → IsBag (f m1 m2)

-- mp stands for multiplicity, the result of applying a zset to an element
theorem elem_mp (m : Z[A]) (a : A) : a ∈ m ↔ m a ≠ 0 := by rw [elem_eq]; simp

theorem not_elem_mp (a : A) (m : Z[A]) : a ∉ m ↔ m a = 0 := by rw [elem_eq]; simp

theorem isSet_or (s : Z[A]) : IsSet s ↔ ∀ a, s a = 0 ∨ s a = 1 :=
  by
  unfold IsSet
  constructor <;> intro h a
  · rw [← not_elem_mp]
    by_cases a ∈ s <;> tauto
  · have h' := h a
    rw [elem_mp]; tauto

@[simp]
theorem isSet_0 : IsSet (0 : Z[A]) := by rw [isSet_or]; tauto

theorem set_isBag (s : Z[A]) : IsSet s → IsBag s :=
  by
  intro hset a
  cases' (isSet_or _).mp hset a with h_a h_a <;> rw [h_a] <;> rw [DFinsupp.zero_apply]; simp

@[simp]
theorem elem_single (a x : A) : x ∈ ({a} : Z[A]) ↔ a = x := by rw [elem_mp]; simp

@[simp]
theorem support_single (a : A) : ({a} : Z[A]).support = {a} := by
  ext x; simp; rw [single_apply]; simp; tauto

def distinct (m : Z[A]) : Z[A] :=
  DFinsupp.mk (m.support.filter fun a => m a > 0) fun _ => 1

@[simp]
theorem distinct_apply (m : Z[A]) (a : A) : distinct m a = if m a > 0 then 1 else 0 :=
  by
  unfold distinct; rw [DFinsupp.mk_apply]; simp
  congr; ext; simp
  intros; omega

theorem distinct_support (m : Z[A]) : (distinct m).support = m.support.filter fun a => m a > 0 := by
  ext a; simp [distinct]

section SumLinear

namespace Finset

theorem union_disjoint_l (s1 s2 : Finset A) :
    s1 ∪ s2 = s1.disjUnion (s2 \ s1) Finset.disjoint_sdiff := by ext a; simp

omit [DecidableEq A] in
theorem filter_filter_comm (p q : A → Prop) [DecidablePred p] [DecidablePred q] (s : Finset A) :
    Finset.filter p (Finset.filter q s) = Finset.filter q (Finset.filter p s) :=
  by
  repeat' rw [Finset.filter_filter]
  congr 1; aesop

end Finset

theorem sum_union_zero_l {α : Type} [AddCommMonoid α] (f : A → α) (s s' : Finset A) :
    (∀ x, x ∈ s' → x ∉ s → f x = 0) → Finset.sum (s ∪ s') f = Finset.sum s f :=
  by
  intro hz
  rw [Finset.union_disjoint_l]
  rw [Finset.sum_disjUnion]
  rw [@Finset.sum_eq_zero _ _ (s' \ s)]; simp
  introv hel; simp at hel; apply hz; aesop; tauto

variable {G : Type} [AddCommGroup G] (f : A → ℤ → G)

theorem general_sum_linear (m1 m2 : Z[A]) :
    (∀ a, f a 0 = 0) →
      (∀ a m1 m2, f a (m1 + m2) = f a m1 + f a m2) →
        ((m1 + m2).support.sum fun a => f a ((m1 + m2) a)) =
          (m1.support.sum fun a => f a (m1 a)) + m2.support.sum fun a => f a (m2 a) :=
  by
  intro hf0 hflin
  rw [add_support]
  simp only [Ne]
  rw [Finset.sum_filter_of_ne]; swap
  · intro x; simp; intro h1; contrapose!
    intro hz; rw [hz]
    apply hf0
  conv_lhs =>
    congr
    · skip
    ext
    simp
    rw [hflin]
    skip
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [sum_union_zero_l]; simp
    introv hnz hz
    rw [hz]
    apply hf0
  · rw [Finset.union_comm]
    rw [sum_union_zero_l]; simp
    introv hnz hz
    rw [hz]
    apply hf0

end SumLinear

-- map is sufficiently complex and specific to the zset representation that we
-- define it here and prove some basic properties, from which it is much easier
-- to reason about it as a relational operator
section Flatmap

variable (f : A → Z[B])

-- the core of flatmap (without the finite support of a real `Z[B]`)
def flatmapAt (m : Z[A]) : B → ℤ :=
  fun b => m.support.sum fun a => f a b * m a

def flatmap (m : Z[A]) : Z[B] :=
  DFinsupp.mk (m.support.biUnion fun a => (f a).support) fun b => flatmapAt f m b

-- This is the function used in the definition of flatmap; the theorem shows that
-- the support chosen is correct; that is, it is an over-approximation (the
-- actual support excludes elements where the sum cancels out and
-- reaches 0)
theorem flatmap_apply (m : Z[A]) : ∀ b, m.flatmap f b = flatmapAt f m b :=
  by
  intro b
  unfold Zset.flatmap flatmapAt
  rw [DFinsupp.mk_apply]
  simp
  intro h
  rw [Finset.sum_eq_zero]
  intro x h' ; simp at h'
  rw [h]; simp; assumption

theorem flatmap_0 : Zset.flatmap f 0 = 0 := rfl

omit [DecidableEq A] in
private theorem ite_cases {c : Prop} [Decidable c] (x z : A) (p : A → Prop) :
  p z → p x → p (ite c x z) := by
    intros; split_ifs <;> tauto

theorem flatmap_linear (m1 m2 : Z[A]) :
    Zset.flatmap f (m1 + m2) = Zset.flatmap f m1 + Zset.flatmap f m2 :=
  by
  ext b; simp
  repeat rw [flatmap_apply]; unfold flatmapAt
  apply general_sum_linear fun a m => f a b * m
  · intros; simp
  · intros; simp [mul_add]

instance DecidableMemFx (b: B): DecidablePred (fun x : A => b ∈ f x) := by
  unfold DecidablePred; intro a; simp
  apply Finset.decidableMem b (DFinsupp.support (f a))

theorem flatmap_fromSet_card (s : Finset A) (b : B) :
    (∀ a, (f a).IsSet) →
      Zset.flatmapAt f (Zset.fromSet s) b = Finset.card (s.filter fun x : A => b ∈ f x) :=
  by
  intro hset
  unfold flatmapAt; simp
  have hsum_1 : (s.sum fun a => f a b) = s.sum fun a => if b ∈ f a then 1 else 0 :=
    by
    apply Finset.sum_congr; rfl
    intros; split_ifs
    · apply hset; assumption
    · rename_i h; rw [not_elem_mp] at h; assumption
  rw [hsum_1]; simp

theorem map_fromSet_card (f : A → B) (s : Finset A) (b : B) :
    Zset.flatmapAt (fun a => {f a}) (Zset.fromSet s) b =
      Finset.card (s.filter fun x : A => f x = b) :=
  by
  rw [flatmap_fromSet_card]
  · simp
  intro a
  unfold IsSet; simp

end Flatmap

section Map

variable (f : A → B)

protected def map (m : Z[A]) : Z[B] :=
  flatmap (fun a => {f a}) m

theorem flatmap_map_at (m : Z[A]) (b : B) :
    flatmapAt (fun a => {f a}) m b = m.support.sum fun a => if f a = b then m a else 0 := by
  unfold flatmapAt; simp

theorem map_apply (m : Z[A]) (b : B) :
    Zset.map f m b = m.support.sum fun a => if f a = b then m a else 0 :=
  by
  unfold Zset.map; rw [flatmap_apply]
  rw [flatmap_map_at]

theorem map_linear (f : A → B) (m1 m2 : Z[A]) :
    Zset.map f (m1 + m2) = Zset.map f m1 + Zset.map f m2 := by apply flatmap_linear

theorem map_zpp (f : A → B) :
    Zset.map f 0 = 0 := by
  unfold Zset.map; rw [flatmap_0]

theorem map_is_card (s : Finset A) : ∀ b, Zset.map f (Zset.fromSet s) b = (s.val.map f).count b :=
  by
  intros; unfold Zset.map
  rw [flatmap_apply]
  rw [flatmap_fromSet_card]
  unfold Multiset.count
  rw [Multiset.countP_map]
  simp
  rw [Finset.card_def]
  simp
  congr 1
  apply Multiset.filter_congr
  · tauto
  · intro a; unfold IsSet; simp

namespace Finset

omit [DecidableEq A] in
theorem sum_nonneg (s : Finset A) (f : A → ℤ) : (∀ x, x ∈ s → 0 ≤ f x) → 0 ≤ s.sum f :=
  by
  intro hnn
  apply Finset.sum_induction
  · intros; omega
  · omega
  · assumption

theorem sum_pos (s : Finset A) (f : A → ℤ) :
    (∃ a, a ∈ s ∧ 0 < f a) → (∀ x, x ∈ s → 0 ≤ f x) → 0 < s.sum f :=
  by
  intro hpos hnn
  cases' hpos with a hpos; cases' hpos with hel hpos
  rw [← Finset.add_sum_erase s _ hel]
  suffices h : 0 ≤ ∑ x ∈ s.erase a, f x by
    omega
  apply sum_nonneg
  aesop

end Finset

theorem map_at_nonneg (f : A → B) (m : Z[A]) (b : B) :
    IsBag m → 0 ≤ flatmapAt (fun a => {f a}) m b :=
  by
  intro hpos
  unfold flatmapAt
  apply Finset.sum_nonneg
  intro x; simp; intros
  apply ite_cases; omega
  apply hpos

theorem map_at_pos (f : A → B) (m : Z[A]) (b : B) :
    IsBag m → (0 < flatmapAt (fun a => {f a}) m b ↔ ∃ a, a ∈ m ∧ f a = b) :=
  by
  intro hpos
  constructor
  · unfold flatmapAt
    intro hmap
    by_contra h
    rw [Finset.sum_eq_zero] at hmap
    · omega
    · intro x; simp; intro h1 h2
      push_neg at h
      rw [← not_elem_mp] at h1
      tauto
  · intro hex
    unfold flatmapAt
    apply Finset.sum_pos
    · cases' hex with a h; cases' h with hel hf
      use a; simp
      rw [if_pos hf]
      have ha := hpos a; simp [Zset] at ha
      rw [elem_mp] at hel; simp at hel
      constructor
      · tauto
      · omega
    · simp; intros
      apply ite_cases; omega
      apply hpos

theorem map_support_image (f : A → B) (m : Z[A]) :
    (m.map f).support ⊆ m.support.image f := by
  intro b; simp; rw [map_apply]
  contrapose; simp; intro h
  rw [Finset.sum_eq_zero]
  intro a ah; simp at ah
  specialize h a ah; simp; tauto

end Map

def size (m : Z[A]) : ℕ :=
  m.support.card

end Zset

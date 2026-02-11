-- Copyright 2022-2023 VMware, Inc.
import DBSP.ZSets.Zset
import DBSP.StreamTheory.Linear


-- SPDX-License-Identifier: BSD-2-Clause
open Zset

variable {A B C : Type}

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem distinct_isSet (m : Z[A]) : IsSet (distinct m) :=
  by
  intro a; rw [elem_mp]; simp

theorem distinct_isBag (m : Z[A]) : IsBag (distinct m) := by
  apply set_isBag; apply distinct_isSet

theorem distinct_set_id (m : Z[A]) : IsSet m → m.distinct = m :=
  by
  intro h
  ext a; simp
  cases' (isSet_or _).mp h a with hma hma <;> rw [hma]
  · rw [if_neg]; omega
  · rw [if_pos]; omega

@[simp]
theorem distinct_set_simp (m : Z[A]) : IsSet (distinct m) ↔ True := by
  simp; apply distinct_isSet

@[simp]
theorem distinct_bag_simp (m : Z[A]) : IsBag (distinct m) ↔ True := by
  simp; apply distinct_isBag

theorem distinct_elem {m : Z[A]} {a : A} : IsBag m → (a ∈ m.distinct ↔ a ∈ m) := by
  intro hpos
  rw [elem_mp, elem_mp]
  rw [distinct_apply]
  have h := hpos a; simp at h
  split_ifs <;> simp <;> omega

theorem isBag_distinct_support (m : Z[A]) (hb: IsBag m):
    (distinct m).support = m.support := by
  ext a; simp
  rw [distinct_apply]
  have h := hb a; simp at h
  split_ifs <;> simp <;> omega

theorem distinct_pos : FunPositive (@distinct A _) := by intro f hp; simp

@[simp]
theorem distinct_0 : distinct (0 : Z[A]) = 0 :=
  rfl

def Query (A B : Type) :=
  Operator Z[A] Z[B]

def union (m1 m2 : Z[A]) :=
  distinct (m1 + m2)

instance zsetUnion : Union Z[A] :=
  ⟨union⟩

theorem union_eq (m1 m2 : Z[A]) : m1 ∪ m2 = union m1 m2 :=
  rfl

theorem union_apply (m1 m2 : Z[A]) (a : A) : union m1 m2 a = if 0 < m1 a + m2 a then 1 else 0 :=
  by
  unfold union distinct; simp
  apply if_congr <;> try rfl
  simp; rw [Zset.add_apply]; omega

theorem union_ok (s1 s2 : Finset A) : Zset.toSet (Zset.fromSet s1 ∪ Zset.fromSet s2) = s1 ∪ s2 :=
  by
  ext a
  rw [Finset.mem_union]
  rw [union_eq]; unfold union
  unfold distinct Zset.fromSet Zset.toSet; simp
  rw [add_apply]
  repeat' rw [<- DFinsupp.toFun_eq_coe]
  simp [DFinsupp.mk]
  split_ifs <;> aesop

lemma isBag_union_support (m1 m2 : Z[A]) (h1 : IsBag m1) (h2 : IsBag m2) :
    (m1 ∪ m2).support = m1.support ∪ m2.support := by
  rw [union_eq]; unfold union
  rw [distinct_support, add_support]
  ext a; simp
  have h1a := h1 a; have h2a := h2 a
  simp [Zset, zset_le_ext] at h1a h2a
  constructor
  · rintro ⟨_, h⟩; omega
  · intro h; omega

theorem union_pos : FunPositive2 (@union A _) :=
  by
  intro m1 m2 h1 h2
  intro a; simp
  rw [union_apply]
  split_ifs <;> omega

theorem map_ok (f : A → B) (s : Finset A) : (Zset.map f (Zset.fromSet s)).support = s.image f :=
  by
  ext b; simp; rw [map_is_card]
  simp

theorem map_pos (f : A → B) : FunPositive (Zset.map f) :=
  by
  intro m h
  intro a; simp
  unfold Zset.map; rw [flatmap_apply]
  apply map_at_nonneg; assumption

section filter

variable (p : A → Prop) [DecidablePred p]

def filter (m : Z[A]) : Z[A] :=
  DFinsupp.mk (m.support.filter p) fun a => m a

theorem filter_support (m : Z[A]) : DFinsupp.support (filter p m) = m.support.filter p :=
  by
  unfold filter; ext a; simp
  tauto

@[simp]
theorem filter_apply (m : Z[A]) (a : A) : filter p m a = if p a then m a else 0 :=
  by
  unfold filter; simp
  rw [<- DFinsupp.toFun_eq_coe]; simp
  split_ifs <;> tauto

theorem filter_ok (s : Finset A) : Zset.toSet (filter p (Zset.fromSet s)) = s.filter p :=
  by
  ext a; simp
  rw [elem_mp, filter_apply]
  simp; tauto

theorem filter_linear : ∀ m1 m2 : Z[A], filter p (m1 + m2) = filter p m1 + filter p m2 :=
  by
  intros
  ext a; simp
  split_ifs
  · simp
  · tauto

theorem filter_pos : FunPositive (filter p) :=
  by
  intro m h; intro a; simp
  split_ifs
  · apply h
  · linarith

theorem filter_0 : filter p 0 = 0 :=
  rfl

end filter

section product

def product (m1 : Z[A]) (m2 : Z[B]) : Z[A × B] :=
  -- the unusual binder is because dfinupp.mk actually supplies a proof that
    -- the input is in the support, which is being ignored here
    DFinsupp.mk
    (Finset.product m1.support m2.support) fun ⟨(a, b), _⟩ => m1 a * m2 b

@[simp]
theorem product_apply (m1 : Z[A]) (m2 : Z[B]) (ab : A × B) : product m1 m2 ab = m1 ab.1 * m2 ab.2 :=
  by
  unfold product; cases' ab with a b; simp
  rw [<- DFinsupp.toFun_eq_coe]; simp
  tauto

theorem product_support (m1 : Z[A]) (m2 : Z[B]) :
    (product m1 m2).support = Finset.product m1.support m2.support :=
  by
  unfold product; ext ab; simp
  rw [<- DFinsupp.toFun_eq_coe]; simp
  tauto

theorem product_ok (s1 : Finset A) (s2 : Finset B) :
    Zset.toSet (product (Zset.fromSet s1) (Zset.fromSet s2)) = Finset.product s1 s2 := by
  ext ab; cases' ab with a b; simp
  rw [elem_eq]; simp [product]
  tauto

theorem product_bilinear : Bilinear (@product A B _ _) :=
  by
  constructor
  · intro x1 x2 y
    ext ab; cases' ab with a b; simp
    ring
  · intro x y1 y2
    ext ab; cases' ab with a b; simp
    ring

theorem product_pos : FunPositive2 (@product A B _ _) :=
  by
  intro m1 m2 h1 h2
  intro ab; cases' ab with a b; simp
  have h1a := h1 a
  have h2a := h2 b
  simp at h1a h2a
  nlinarith

@[simp]
theorem product_0 : @product A B _ _ 0 0 = 0 :=
  rfl

section equiJoin

variable (π1 : A → C) (π2 : B → C)

def equiJoin (m1 : Z[A]) (m2 : Z[B]) : Z[A × B] :=
  filter (fun t => π1 t.1 = π2 t.2) (product m1 m2)

@[simp]
theorem equiJoin_apply (m1 : Z[A]) (m2 : Z[B]) (t : A × B) :
    equiJoin π1 π2 m1 m2 t = if π1 t.1 = π2 t.2 then m1 t.1 * m2 t.2 else 0 := by
  unfold equiJoin;
  simp

theorem equiJoin_support (m1 : Z[A]) (m2 : Z[B]) :
    (equiJoin π1 π2 m1 m2).support =
      (Finset.product m1.support m2.support).filter fun t => π1 t.1 = π2 t.2 :=
  by
  unfold equiJoin; rw [filter_support, product_support]

theorem equiJoin_bilinear : Bilinear (equiJoin π1 π2) :=
  by
  constructor <;> intros
  · unfold equiJoin; rw [product_bilinear.1, filter_linear]
  · unfold equiJoin; rw [product_bilinear.2, filter_linear]

theorem equiJoin_pos : FunPositive2 (equiJoin π1 π2) :=
  by
  intro m1 m2 h1 h2
  apply filter_pos; apply product_pos <;> assumption

@[simp]
theorem equiJoin_0_l (b : Z[B]) : equiJoin π1 π2 0 b = 0 :=
  rfl

@[simp]
theorem equiJoin_0_r (a : Z[A]) : equiJoin π1 π2 a 0 = 0 := by ext a; simp

end equiJoin

end product

-- TODO: paper says intersection can be defined as a special case of an
-- equijoin, but this construction required projecting A × A → A (where both are
-- equal due to the filter), and it's not obvious that project preserves
-- bilinearity. In any case the direct definition is straightforward.
def intersect (m1 m2 : Z[A]) : Z[A] :=
  DFinsupp.mk (m1.support ∩ m2.support) fun a => m1 a * m2 a

instance : Inter Z[A] :=
  ⟨intersect⟩

@[simp]
theorem intersect_apply (m1 m2 : Z[A]) (a : A) : (m1 ∩ m2) a = m1 a * m2 a :=
  by
  conv =>
    lhs; lhs; change intersect m1 m2
  unfold intersect; rw [<- DFinsupp.toFun_eq_coe]; simp
  tauto

@[simp]
theorem intersect_0 : (0 : Z[A]) ∩ 0 = 0 :=
  rfl

@[simp]
theorem intersect_support (m1 m2 : Z[A]) : (m1 ∩ m2).support = m1.support ∩ m2.support :=
  by
  conv =>
    lhs; rhs; change intersect m1 m2
  ext a
  unfold intersect; simp
  tauto

theorem intersect_ok (s1 s2 : Finset A) :
    Zset.toSet (Zset.fromSet s1 ∩ Zset.fromSet s2) = s1 ∩ s2 :=
  by
  ext a; simp
  rw [elem_mp]; simp; tauto

theorem intersect_pos : FunPositive2 ((· ∩ ·) : Z[A] → Z[A] → Z[A]) :=
  by
  intro m1 m2 hpos1 hpos2
  intro a; simp
  have h1 := hpos1 a; have h2 := hpos2 a; simp at h1 h2
  nlinarith

theorem intersect_bilinear : Bilinear ((· ∩ ·) : Z[A] → Z[A] → Z[A]) := by
  constructor <;> introv <;> ext a <;> simp <;> nlinarith

def difference (m1 m2 : Z[A]) : Z[A] :=
  distinct (m1 - m2)

theorem difference_ok (s1 s2 : Finset A) :
    Zset.toSet (difference (Zset.fromSet s1) (Zset.fromSet s2)) = s1 \ s2 :=
  by
  ext a; simp
  rw [elem_mp]; unfold difference; simp
  split_ifs <;> try simp; tauto

section groupBy

variable {K : Type} [DecidableEq K] (p : A → K)

def groupBy : Z[A] → Π₀ _ : K, Z[A] := fun m =>
  DFinsupp.mk (m.support.image p) fun k =>
    DFinsupp.mk (m.support.filter fun a => p a = k) fun a => if p a = k then m a else 0

@[simp]
theorem groupBy_apply (m : Z[A]) (k : K) (a : A) : groupBy p m k a = if p a = k then m a else 0 :=
  by
  unfold groupBy; simp
  rw [<- DFinsupp.toFun_eq_coe]; simp
  split_ifs with hk hp <;> simp at hk ⊢
  · split_ifs <;> try tauto
  · tauto
  · by_contra; apply hk a <;> tauto

theorem groupBy_support (m : Z[A]) (k : K) :
    (groupBy p m k).support = m.support.filter fun a => p a = k := by
  ext a; simp; rw [groupBy_apply]; simp; tauto

theorem elem_groupBy (m : Z[A]) (k : K) (a : A) : a ∈ groupBy p m k ↔ p a = k ∧ a ∈ m := by
  rw [elem_mp, elem_mp]; simp

theorem groupBy_linear (m1 m2 : Z[A]) : groupBy p (m1 + m2) = groupBy p m1 + groupBy p m2 :=
  by
  ext k a; simp
  split_ifs <;> rfl

end groupBy

-- A few properties about [distinct]
@[simp]
theorem ite_ite {A : Type} {c1 : Prop} [Decidable c1] {c2 : Prop} [Decidable c2] (x z : A) :
    ite c1 (ite c2 x z) z = ite (c1 ∧ c2) x z := by split_ifs <;> tauto

-- this doesn't require is_bag i
theorem filter_distinct_comm (p : A → Prop) [DecidablePred p] (i : Z[A]) :
    filter p (distinct i) = distinct (filter p i) :=
  by
  ext a; simp
  apply if_congr <;> try rfl
  split_ifs <;> tauto

theorem product_distinct_comm (i1 : Z[A]) (i2 : Z[B]) :
    IsBag i1 → IsBag i2 → product (distinct i1) (distinct i2) = distinct (product i1 i2) :=
  by
  intro hpos1 hpos2
  ext ab; cases' ab with a b; simp
  have h1 := hpos1 a; have h2 := hpos2 b
  simp at h1 h2
  apply if_congr <;> try rfl
  constructor
  · rintro ⟨h1, h2⟩; apply Int.mul_pos <;> tauto
  · intro h
    by_cases ha: i1 a = 0 <;> by_cases hb: i2 b = 0 <;> aesop <;> omega

theorem join_distinct_comm (π1 : A → C) (π2 : B → C) (i1 : Z[A]) (i2 : Z[B]) :
    IsBag i1 →
      IsBag i2 → equiJoin π1 π2 (distinct i1) (distinct i2) = distinct (equiJoin π1 π2 i1 i2) :=
  by
  intro hpos1 hpos2
  unfold equiJoin
  rw [← filter_distinct_comm]
  · rw [← product_distinct_comm] <;> assumption

theorem intersect_distinct_comm (i1 i2 : Z[A]) :
    IsBag i1 → IsBag i2 → distinct i1 ∩ distinct i2 = distinct (i1 ∩ i2) :=
  by
  intro hpos1 hpos2
  ext a; simp
  apply if_congr <;> try rfl
  have h1 := hpos1 a; have h2 := hpos2 a; simp at h1 h2
  by_cases ha: i1 a = 0 <;> by_cases hb: i2 a = 0 <;> aesop <;> omega

private theorem map_at_distinct_none (f : A → B) (i : Z[A]) (b : B) :
    IsBag i → (∀ a, a ∈ i → f a ≠ b) → flatmapAt (fun a => {f a}) i.distinct b = 0 :=
  by
  intro hpos h
  unfold flatmapAt
  rw [Finset.sum_eq_zero]
  intro x ix_pos; simp at ix_pos
  simp; intro hfx
  suffices hne : f x ≠ b; · tauto
  apply h; rw [elem_mp]; linarith

theorem
  map_inj_distinct_comm
  ( f : A → B ) (f_inj : Function.Injective f) ( i : Z[ A ] )
    : IsBag i → distinct (Zset.map f i) = Zset.map f (distinct i) := by
  intro hpos
  ext b
  simp
  unfold Zset.map
  rw [flatmap_apply, flatmap_apply]
  split_ifs with h <;> rw [map_at_pos _ _ _ hpos] at h
  · cases' h with a h
    cases' h with hel hf
    have ha := hpos a
    simp at ha
    rw [flatmap_map_at]
    rw [← @Finset.sum_erase_add _ _ _ _ _ _ a]
    · rw [Finset.sum_eq_zero]
      · rw [distinct_apply]
        rw [elem_mp] at hel
        rw [if_pos]
        · omega
        · assumption
      introv hel_erase
      split_ifs
      swap; rfl
      simp at hel_erase ⊢
      suffices hxa : x = a
      · exfalso; tauto
      apply f_inj
      cc
    simp
    rw [elem_mp] at hel; simp [distinct]; omega
  · push_neg at h
    rw [map_at_distinct_none]
    assumption
    assumption

@[simp]
theorem distinct_idem (i : Z[A]) : distinct (distinct i) = distinct i :=
  by
  ext a; simp
  split_ifs <;>
    first
    | rfl
    | linarith

theorem filter_distinct_dedup (p : A → Prop) [DecidablePred p] (i : Z[A]) :
    distinct (filter p (distinct i)) = distinct (filter p i) := by
  rw [filter_distinct_comm, distinct_idem]

theorem map_distinct_dedup (f : A → B) (i : Z[A]) :
    IsBag i → distinct (Zset.map f (distinct i)) = distinct (Zset.map f i) :=
  by
  intro hpos
  ext b; simp
  apply if_congr <;> try rfl
  unfold Zset.map
  rw [flatmap_apply, flatmap_apply]
  rw [map_at_pos, map_at_pos]
  ·
    conv_lhs =>
      congr
      ext
      rw [distinct_elem hpos]
      skip
  · assumption
  · simp

theorem add_distinct_dedup (i1 i2 : Z[A]) :
    IsBag i1 → IsBag i2 → distinct (i1.distinct + i2.distinct) = distinct (i1 + i2) :=
  by
  intro hpos1 hpos2
  ext a; simp
  have h1 := hpos1 a; have h2 := hpos2 a; simp at h1 h2
  split_ifs <;>
    first
    | rfl
    | linarith

theorem product_distinct_dedup (i1 : Z[A]) (i2 : Z[B]) :
    IsBag i1 →
      IsBag i2 → distinct (product (distinct i1) (distinct i2)) = distinct (product i1 i2) :=
  by
  intro hpos1 hpos2
  rw [product_distinct_comm, distinct_idem] <;> assumption

theorem join_distinct_dedup (π1 : A → C) (π2 : B → C) (i1 : Z[A]) (i2 : Z[B]) :
    IsBag i1 →
      IsBag i2 →
        distinct (equiJoin π1 π2 (distinct i1) (distinct i2)) = distinct (equiJoin π1 π2 i1 i2) :=
  by
  intro hpos1 hpos2
  rw [join_distinct_comm, distinct_idem] <;> assumption

theorem intersect_distinct_dedup (i1 i2 : Z[A]) :
    IsBag i1 → IsBag i2 → distinct (distinct i1 ∩ distinct i2) = distinct (i1 ∩ i2) :=
  by
  intro hpos1 hpos2
  rw [intersect_distinct_comm, distinct_idem] <;> assumption

--- Lemmas on id_distinct input and join
section id_distinct
def id_distinct (π: A → B) (s: Set A) :=
  ∀ a1 ∈ s, ∀ a2 ∈ s, π a1 = π a2 → a1 = a2

variable {p: A → Prop} [DecidablePred p]

omit [DecidableEq B] in
lemma filter_keep_id_distinct
    {π: A → B} {s: Z[A]} (h: id_distinct π s.support):
    id_distinct π (filter p s).support := by
  intro a1 ha1 a2 ha2 heq
  rw [filter_support] at ha1 ha2
  apply h <;> try tauto
  all_goals apply Finset.filter_subset p; tauto

omit [DecidableEq C] in
lemma map_keep_id_distinct {π: B → C} {f: A → B}
    {s: Z[A]} (h: id_distinct (π ∘ f) s.support):
    id_distinct π (Zset.map f s).support := by
  intro b1 hb1 b2 hb2 heq
  apply map_support_image at hb1
  apply map_support_image at hb2
  simp at hb1 hb2
  rcases hb1 with ⟨a1, hs1, ha1⟩
  rcases hb2 with ⟨a2, hs2, ha2⟩
  rw [<- ha1, <- ha2]; congr
  apply h <;> try (simp; tauto)
  simp; rw [ha1, ha2]; tauto

lemma equiJoin_id_distinct_size {π1: A → C} {π2: B → C}
    {s1: Z[A]} {s2: Z[B]} (h1: id_distinct π1 s1.support) (h2: id_distinct π2 s2.support):
    (equiJoin π1 π2 s1 s2).size ≤ min s1.size s2.size:= by
  apply le_min
  · apply Finset.card_le_card_of_injective
    case h₁.f =>
      rintro ⟨x, hx⟩
      constructor
      case mk.val => exact x.1
      rw [equiJoin_support] at hx
      simp at hx; simp; tauto
    rintro ⟨⟨x1, x2⟩, hx⟩ ⟨⟨y1, y2⟩, hy⟩; simp; intro eq
    rw [equiJoin_support] at hx hy
    simp at hx hy
    constructor; tauto
    apply h2 <;> try (simp; tauto)
    apply congrArg π1 at eq
    rw [<- hx.2, eq, hy.2]
  · apply Finset.card_le_card_of_injective
    case h₂.f =>
      rintro ⟨x, hx⟩
      constructor
      case mk.val => exact x.2
      rw [equiJoin_support] at hx
      simp at hx; simp; tauto
    rintro ⟨⟨x1, x2⟩, hx⟩ ⟨⟨y1, y2⟩, hy⟩; simp; intro eq
    rw [equiJoin_support] at hx hy
    simp at hx hy
    constructor; swap; tauto
    apply h1 <;> try (simp; tauto)
    apply congrArg π2 at eq
    rw [hx.2, eq, hy.2]

def stream_id_distinct (π: A → B) (x: stream Z[A]) :=
  id_distinct π (⋃ i, (x i).support)

omit [DecidableEq B] in
lemma stream_id_distinct_to_id_distinct {π: A → B} {x: stream Z[A]}
    (h: stream_id_distinct π x) (i: ℕ):
    id_distinct π (x i).support := by
  intro a1 ha1 a2 ha2 heq
  simp at ha1 ha2
  apply h <;> try (simp; tauto)
  tauto

omit [DecidableEq B] in
lemma lifting_filter_id_distinct {π: A → B} {s: stream Z[A]}
  (h: stream_id_distinct π s):
    stream_id_distinct π (↑↑(filter p) s) := by
  intro a1 ha1 a2 ha2 heq
  simp at ha1 ha2
  rcases ha1 with ⟨i1, ha1⟩
  rcases ha2 with ⟨i2, ha2⟩
  rw [filter_apply] at ha1 ha2
  simp at ha1 ha2
  apply h <;> simp [*]
  · use i1; tauto
  · use i2; tauto

omit [DecidableEq C] in
lemma lifting_map_id_distinct {π: B → C} {f: A → B}
    {s: stream Z[A]} (h: stream_id_distinct (π ∘ f) s):
    stream_id_distinct π (↑↑(Zset.map f) s) := by
  intro b1 hb1 b2 hb2 heq
  simp at hb1 hb2
  rcases hb1 with ⟨i1, hb1⟩
  rcases hb2 with ⟨i2, hb2⟩
  rw [<- not_elem_mp] at hb1 hb2; simp at hb1 hb2
  apply map_support_image at hb1
  apply map_support_image at hb2
  simp at hb1 hb2
  rcases hb1 with ⟨a1, hs1, ha1⟩
  rcases hb2 with ⟨a2, hs2, ha2⟩
  rw [<- ha1, <- ha2]; congr
  apply h <;> try (simp; tauto)
  simp; rw [ha1, ha2]; tauto

lemma integral_Zset_mem {s: stream Z[A]}
  {a: A} {n: ℕ} (h: a ∈ I s n):
    ∃ i ≤ n, a ∈ s i := by
  revert a; rw [integral_sumVals]; simp
  induction n
  · intro a ha; simp at ha; tauto
  rename_i n ih; intro a ha
  simp at ha
  rw [elem_eq, add_support] at ha
  apply Finset.filter_subset at ha
  rw [Finset.mem_union] at ha
  rcases ha with ha | ha
  · use n+1;
    constructor
    omega; apply ha
  specialize ih ha
  rcases ih with ⟨i, ih⟩
  use i; tauto

omit [DecidableEq B] in
lemma integral_id_distinct {π: A → B} {s: stream Z[A]}
  (h: stream_id_distinct π s):
    stream_id_distinct π (I s) := by
  intro a1 ha1 a2 ha2 heq
  simp at ha1 ha2
  rcases ha1 with ⟨i1, ha1⟩
  rcases ha2 with ⟨i2, ha2⟩
  rw [<- not_elem_mp] at ha1 ha2; simp at ha1 ha2
  apply h
  · apply integral_Zset_mem at ha1
    rcases ha1 with ⟨m1, ha1⟩; simp [elem_eq] at ha1
    simp; use m1; tauto
  · apply integral_Zset_mem at ha2
    rcases ha2 with ⟨m2, ha2⟩; simp [elem_eq] at ha2
    simp; use m2; tauto
  · tauto

omit [DecidableEq B] in
lemma delay_id_distinct {π: A → B} {s: stream Z[A]}
  (h: stream_id_distinct π s):
    stream_id_distinct π (z⁻¹ s) := by
  intro a1 ha1 a2 ha2 heq
  simp at ha1 ha2
  rcases ha1 with ⟨i1, ha1⟩
  rcases ha2 with ⟨i2, ha2⟩
  simp [delay] at ha1 ha2
  split_ifs at ha1; tauto
  split_ifs at ha2; tauto
  apply h
  · simp; use (i1 -1)
  · simp; use (i2 -1)
  · tauto

end id_distinct

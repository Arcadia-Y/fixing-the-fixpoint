import DBSP.ZsetCkt.ZsetCkt
import DBSP.ResourceAnalysis.HoareR
open CktBasic

section ZsetCkt
variable {A B C: Type} [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable {ns: Bool}

abbrev Zsize (x: SOType ns Z[A]) := liftO ns Zset.size x

lemma Zsize_I (x: SOType ns Z[A]):
    Zsize (I x) ≤ I (Zsize x) := by
  intro i; simp
  induction' i with i ih
  · rcases ns <;> simp
  · rcases ns <;> simp
    · apply le_trans
      apply Zset_size_add
      simp; apply ih
    · intro j; simp
      apply le_trans
      apply Zset_size_add
      simp; apply ih

lemma Zsize_delay (x: SOType ns Z[A]):
    Zsize (z⁻¹ x) = z⁻¹ (Zsize x) := by
  rcases ns <;> funext i <;> rcases i <;> simp [Zset.size]
  funext _; simp [Zset.size]

lemma Zsize_delta (x: Z[A]):
    Zsize (ns:=0) (δ0 x) = (δ0 (x.size)) := by
  funext i; rcases i <;> simp [Zset.size]

def ZSB (x: SOType ns Z[A]) (b: SOType ns ℕ) :=
  Zsize x ≤ b

-- lemmas on ZSB and Zset operations (polymorphic w.r.t. ns)
lemma ZSB_add {x1 x2: SOType ns Z[A]} {b1 b2}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2):
    ZSB (x1 + x2) (b1 + b2) := by
  rcases ns with _ | _
  · intro m; simp
    apply le_trans; apply Zset_size_add
    apply add_le_add <;> tauto
  · intro i m; simp
    apply le_trans; apply Zset_size_add
    apply add_le_add <;> tauto

lemma ZSB_sub {x1 x2: SOType ns Z[A]} {b1 b2}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2):
    ZSB (x1 - x2) (b1 + b2) := by
  rcases ns with _ | _
  · intro m; simp
    apply le_trans; apply Zset_size_sub
    apply add_le_add <;> tauto
  · intro i m; simp
    apply le_trans; apply Zset_size_sub
    apply add_le_add <;> tauto

lemma ZSB_distinct {x: SOType ns Z[A]} {b}
  (h: ZSB x b):
    ZSB (liftO ns Zset.distinct x) b := by
  rcases ns with _ | _
  · intro m; simp
    apply le_trans; apply Zset_size_distinct; apply h
  · intro i m; simp
    apply le_trans; apply Zset_size_distinct; apply h

lemma ZSB_map {f: A → B} {x: SOType ns Z[A]} {b}
  (h: ZSB x b):
    ZSB (liftO ns (Zset.map f) x) b := by
  rcases ns with _ | _
  · intro m; simp
    apply le_trans; apply Zset_size_map; apply h
  · intro i m; simp
    apply le_trans; apply Zset_size_map; apply h

lemma ZSB_filter {p: A → Prop} [DecidablePred p] {x: SOType ns Z[A]} {b}
  (h: ZSB x b):
    ZSB (liftO ns (filter p) x) b := by
  rcases ns with _ | _
  · intro m; simp
    apply le_trans; apply Zset_size_filter; apply h
  · intro i m; simp
    apply le_trans; apply Zset_size_filter; apply h

lemma ZSB_H {x1 x2: SOType ns Z[A]} {b1 b2}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2):
    ZSB (liftO ns Zset_H (sprodO ns (x1, x2))) (b1 + b2) := by
  rcases ns with _ | _
  · intro m; simp
    apply le_trans; apply Zset_size_H
    apply add_le_add <;> tauto
  · intro i m; simp
    apply le_trans; apply Zset_size_H
    apply add_le_add <;> tauto

lemma ZSB_product {x1: SOType ns Z[A]} {x2: SOType ns Z[B]} {b1 b2}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2):
    ZSB (liftO ns Zset_product (sprodO ns (x1, x2))) (liftO ns (fun p => p.1 * p.2) (sprodO ns (b1, b2))) := by
  rcases ns with _ | _
  · intro m; simp
    apply le_trans; apply Zset_size_product
    apply mul_le_mul' <;> tauto
  · intro i m; simp
    apply le_trans; apply Zset_size_product
    apply mul_le_mul' <;> tauto

lemma ZSB_join {π1 : A → C} {π2 : B → C}
    {x1: SOType ns Z[A]} {x2: SOType ns Z[B]} {b1 b2}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2):
    ZSB (liftO ns (Zset_join π1 π2) (sprodO ns (x1, x2))) (liftO ns (fun p => p.1 * p.2) (sprodO ns (b1, b2))) := by
  rcases ns with _ | _
  · intro m; simp
    apply le_trans; apply Zset_size_join
    apply mul_le_mul' <;> tauto
  · intro i m; simp
    apply le_trans; apply Zset_size_join
    apply mul_le_mul' <;> tauto

lemma ZSB_I {x: SOType ns Z[A]} {b}
  (h: ZSB x b):
    ZSB (I x) (I b) := by
  apply le_trans; apply Zsize_I
  apply mono_integral; tauto

--- HoareR Zset Lemmas (polymorphic w.r.t. ns)
theorem HoareR_Zset_add {x1 x2: SOType ns Z[A]}:
    HoareR (fun y => y = sprodO ns (x1, x2)) (Ckt.add (ns := ns) (a := [Z[A]]v))
      (fun y => y = x1 + x2)
      (Zsize x1 + Zsize x2) := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns <;> simp [IntConv, denote]
    funext _ _; simp
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp [cost_f, add_cost, BaseType.add_cost]
    intro _; simp
    intro _ _; simp

theorem HoareR_Zset_sub {x1 x2: SOType ns Z[A]}:
    HoareR (fun y => y = sprodO ns (x1, x2)) (Ckt.sub (ns := ns) (a := [Z[A]]v))
      (fun y => y = x1 - x2)
      (Zsize x1 + Zsize x2) := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns <;> simp [IntConv, denote]
    funext _; simp
    funext _ _; simp
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp [cost_f, sub_cost, BaseType.sub_cost]
    intro _; simp
    intro _ _; simp

theorem HoareR_Zset_distinct {x: SOType ns Z[A]}:
    HoareR (fun y => y = x) (Ckt.node1 (ns := ns) DistinctUnaryNode)
      (fun y => y = liftO ns Zset.distinct x)
      (Zsize x) := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns <;> simp only [IntConv, denote, DistinctUnaryNode, liftO] <;> trivial
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, UnaryNode.cost, DistinctUnaryNode, liftO, Zset.size] <;> rfl

theorem HoareR_Zset_map (f: A → B) {x: SOType ns Z[A]}:
    HoareR (fun y => y = x) (Ckt.node1 (ns := ns) (MapUnaryNode f))
      (fun y => y = liftO ns (Zset.map f) x)
      (Zsize x) := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns <;> simp only [IntConv, denote, MapUnaryNode, liftO] <;> trivial
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, UnaryNode.cost, MapUnaryNode, liftO, Zset.size] <;> rfl

theorem HoareR_Zset_filter (p: A → Prop) [DecidablePred p] {x: SOType ns Z[A]}:
    HoareR (fun y => y = x) (Ckt.node1 (ns := ns) (FilterUnaryNode p))
      (fun y => y = liftO ns (filter p) x)
      (Zsize x) := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns <;> simp only [IntConv, denote, FilterUnaryNode, liftO] <;> trivial
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, UnaryNode.cost, FilterUnaryNode, liftO, Zset.size] <;> rfl

theorem HoareR_Zset_H {x1 x2: SOType ns Z[A]}:
    HoareR (fun y => y = sprodO ns (x1, x2)) (Ckt.node2 (ns := ns) HBinaryNode)
      (fun y => y = liftO ns Zset_H (sprodO ns (x1, x2)))
      (Zsize x1 + Zsize x2) := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns <;> simp only [IntConv, denote, HBinaryNode, Zset_H, liftO, sprodO, sprod, sprod2] <;> trivial
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, BinaryNode.cost, HBinaryNode, liftO, Zset.size, sprodO, sprod, sprod2] <;> rfl

theorem HoareR_Zset_product {x1: SOType ns Z[A]} {x2: SOType ns Z[B]}:
    HoareR (fun y => y = sprodO ns (x1, x2)) (Ckt.node2 (ns := ns) ProductBinaryNode)
      (fun y => y = liftO ns Zset_product (sprodO ns (x1, x2)))
      (liftO ns (fun p => Zset.size p.1 * Zset.size p.2) (sprodO ns (x1, x2))) := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns <;> simp only [IntConv, denote, ProductBinaryNode, Zset_product, liftO, sprodO, sprod, sprod2] <;> trivial
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, BinaryNode.cost, ProductBinaryNode, liftO, Zset.size, sprodO, sprod, sprod2] <;> rfl

theorem HoareR_Zset_join (π1 : A → C) (π2 : B → C)
    {x1: SOType ns Z[A]} {x2: SOType ns Z[B]}:
    HoareR (fun y => y = sprodO ns (x1, x2)) (Ckt.node2 (ns := ns) (EquiJoinBinaryNode π1 π2))
      (fun y => y = liftO ns (Zset_join π1 π2) (sprodO ns (x1, x2)))
      (liftO ns (fun p => Zset.size p.1 * Zset.size p.2) (sprodO ns (x1, x2))) := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns <;> simp only [IntConv, denote, EquiJoinBinaryNode, Zset_join, liftO, sprodO, sprod, sprod2] <;> trivial
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, BinaryNode.cost, EquiJoinBinaryNode, liftO, Zset.size, sprodO, sprod, sprod2] <;> rfl

theorem HoareR_Zset_I_ns0 {x: SOType 0 Z[A]}:
    HoareR
      (fun y => y = x)
      (@cI [Z[A]]v 0)
      (fun y => y = I x)
      (fun i => (x i).size + (z⁻¹ (I x) i).size + (I x i).size) := by
  apply HoareR_weaken_bound
  apply HoareR_I
  intro i
  simp [add_cost, BaseType.add_cost, VType_space]

theorem HoareR_Zset_I {x: SOType ns Z[A]}:
    HoareR
      (fun y => y = x)
      (@cI [Z[A]]v ns)
      (fun y => y = I x)
      (3 • I (Zsize x)) := by
  apply HoareR_weaken_bound
  apply HoareR_I
  have h1: Zsize x ≤ I (Zsize x) := by
    apply le_integral
  have h2 := Zsize_I x
  have h3 : Zsize (z⁻¹ (I x)) ≤ I (Zsize x) := by
    rw [Zsize_delay]
    rcases ns
    · apply le_trans; apply mono_delay
      apply Zsize_I; apply delay_le;
      apply mono_integral_stream
    · apply le_trans; apply mono_delay
      apply Zsize_I; apply delay_le;
      apply mono_integral_stream
  have h4 := add_le_add h1 h3
  have h5 := add_le_add h4 h2
  rcases ns
  · intro i
    simp [add_cost, BaseType.add_cost, VType_space, BaseType.size]
    apply le_trans; apply h5
    simp; omega
  · intro i j
    simp [add_cost, BaseType.add_cost, VType_space, BaseType.size]
    apply le_trans; apply h5
    simp; omega

theorem HoareR_Zset_D {x: SOType ns Z[A]}:
    HoareR
      (fun y => y = x)
      (@cD [Z[A]]v ns)
      (fun y => y = D x)
      (2 • Zsize x + z⁻¹ (Zsize x)) := by
  apply HoareR_weaken_bound
  apply HoareR_D
  rcases ns
  · intro i
    simp [sub_cost, VType_space]
    rcases i <;> simp <;> omega
  · intro i j
    simp [sub_cost, VType_space]
    rcases i <;> simp <;> omega

theorem HoareR_ZSB_D {x: SOType ns Z[A]} {b: SOType ns ℕ}
  (h: ZSB x b):
    HoareR
      (fun y => y = x)
      (@cD [Z[A]]v ns)
      (fun y => y = D x)
      (2 • b + z⁻¹ b) := by
  apply HoareR_weaken_bound
  apply HoareR_D
  rcases ns
  · intro i
    simp [sub_cost, VType_space]
    rcases i with _ | i<;> simp
    · specialize h 0; simp at h
      omega
    · have h1 := h i
      have h2 := h (i + 1)
      simp at h1 h2
      omega
  · intro i j
    simp [sub_cost, VType_space]
    rcases i with _ | i<;> simp
    · specialize h 0 j; simp at h
      omega
    · have h1 := h i j
      have h2 := h (i + 1) j
      simp at h1 h2
      omega

theorem HoareR_ZSB_D_mono {x: SOType ns Z[A]} {b: SOType ns ℕ}
  (h: ZSB x b) (hm: Monotone b):
    HoareR
      (fun y => y = x)
      (@cD [Z[A]]v ns)
      (fun y => y = D x)
      (3 • b) := by
  apply HoareR_weaken_bound
  apply HoareR_ZSB_D h
  rcases ns
  · intro i
    rcases i with _ | i <;> simp
    · omega
    · specialize hm (Nat.le_succ i); simp at hm
      omega
  · intro i j
    rcases i with _ | i <;> simp
    · omega
    · specialize hm (Nat.le_succ i) j; simp at hm
      omega

-- "Support+IsBag" style lemmas for ns=0

theorem HoareR_join_support_ns0 (π1 : A → C) (π2 : B → C)
  {x1: stream Z[A]} {x2: stream Z[B]}
  {S1: stream (Finset A)} {S2: stream (Finset B)}
  (h1s: ∀j, (x1 j).support = S1 j) (h1b: ∀j, (x1 j).IsBag)
  (h2s: ∀j, (x2 j).support = S2 j) (h2b: ∀j, (x2 j).IsBag):
    HoareR (fun y => y = sprod (x1, x2)) (Ckt.node2 (ns:=0) (EquiJoinBinaryNode π1 π2))
      (fun y => (∀ j, (y j).support = {t ∈ S1 j ×ˢ S2 j | π1 t.1 = π2 t.2}) ∧ (∀ j, (y j).IsBag))
      (fun j => (S1 j).card * (S2 j).card) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_Zset_join
  · intro j; simp
    unfold Zset.size
    rw [h1s, h2s]
  · simp; constructor <;> intro j
    · simp [equiJoin_support, h1s, h2s]
    · apply equiJoin_pos <;> tauto

theorem HoareR_map_support_ns0 (f: A → B)
  {x: stream Z[A]} {S: stream (Finset A)}
  (h1s: ∀j, (x j).support = S j) (h1b: ∀j, (x j).IsBag):
    HoareR (fun y => y = x) (Ckt.node1 (ns:=0) (MapUnaryNode f))
      (fun y => (∀ j, (y j).support = Finset.image f (S j)) ∧ (∀ j, (y j).IsBag))
      (fun j => (S j).card) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_Zset_map
  · intro j; simp
    unfold Zset.size
    rw [h1s]
  · simp; constructor <;> intro j
    · rw [Zset.isBag_map_support, h1s]; tauto
    · apply map_pos; tauto

theorem HoareR_add_support_ns0 {x1 x2: stream Z[A]} {S1 S2: stream (Finset A)}
  (h1s: ∀j, (x1 j).support = S1 j) (h1b: ∀j, (x1 j).IsBag)
  (h2s: ∀j, (x2 j).support = S2 j) (h2b: ∀j, (x2 j).IsBag):
    HoareR (fun y => y = sprod (x1, x2)) (Ckt.add (ns:=0) (a := [Z[A]]v))
      (fun y => (∀ j, (y j).support = S1 j ∪ S2 j) ∧ (∀ j, (y j).IsBag))
      (fun j => (S1 j).card + (S2 j).card) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_Zset_add
  · intro j; simp
    unfold Zset.size
    rw [h1s, h2s]
  · simp; constructor <;> intro j
    · rw [Zset.isBag_add_support, h1s, h2s] <;> tauto
    · apply Zset.add_pos <;> tauto

theorem HoareR_distinct_support_ns0 {x: stream Z[A]} {S: stream (Finset A)}
  (h1s: ∀j, (x j).support = S j) (h1b: ∀j, (x j).IsBag):
    HoareR (fun y => y = x) (Ckt.node1 (ns:=0) DistinctUnaryNode)
      (fun y => (∀ j, (y j).support = S j) ∧ (∀ j, (y j).IsSet))
      (fun j => (S j).card) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_Zset_distinct
  · intro j; simp
    unfold Zset.size
    rw [h1s]
  · simp; intro j
    rw [isBag_distinct_support, h1s]; tauto

-- "Support+IsBag" style lemmas for ns=1
lemma integral_support {x: stream Z[A]} {S: stream (Finset A)}
  (hs: ∀ i, (x i).support = S i) (hb: ∀ i, (x i).IsBag):
    (∀ i, (I x i).support = (Finset.range (i+1)).biUnion (fun k => S k)) ∧
    (∀ i, (I x i).IsBag) := by
  rw [<- forall_and_iff]; intro i
  induction' i with i ih <;> simp
  · tauto
  rcases ih with ⟨ih1, ih2⟩
  constructor
  · rw [Zset.isBag_add_support, ih1, hs]
    · simp [Finset.range_succ, Finset.biUnion_insert, Finset.union_assoc]
    · exact hb _
    · exact ih2
  · apply Zset.add_pos <;> tauto

lemma nested_stream_I_fun_eq {A: Type} [AddCommMonoid A]
  (x: stream (stream A)) (i j: ℕ):
    I (fun k => x k j) i = I x i j := by
  induction' i with i ih <;> simp
  rw [ih]

theorem HoareR_I_support_ns1 {x: SOType 1 Z[A]} {S: SOType 1 (Finset A)}
  (h1s: ∀ i j, (x i j).support = S i j) (h1b: ∀ i j, (x i j).IsBag)
  (S2: SOType 1 (Finset A)) (hres: ∀ i j, (Finset.range (i+1)).biUnion (fun k => S k j) = S2 i j):
    HoareR (fun y => y = x) (@cI [Z[A]]v 1)
      (fun y => (∀ i j, (y i j).support = S2 i j) ∧ (∀ i j, (y i j).IsBag))
      (fun i j => (S i j).card + (S2 (i-1) j).card + (S2 i j).card) := by
  have hr := fun j => integral_support (fun i => h1s i j) (fun i => h1b i j)
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_I
  · intro i j; simp [add_cost, Zset.size, VType_space]
    simp_rw [<- hres]
    rcases i with _ | i <;> simp [-integral_succ]
    · rw [h1s]; omega
    · simp_rw [<- nested_stream_I_fun_eq]
      simp_rw [(hr j).1, h1s]; omega
  · simp; constructor <;> intro i j <;> rw [<- nested_stream_I_fun_eq]
    · rw [(hr j).1, hres]
    · apply (hr j).2

theorem HoareR_I_sprod2_support {x1: SOType 1 Z[A]} {x2: SOType 1 Z[B]}
  {S1 IS1: SOType 1 (Finset A)} {S2 IS2: SOType 1 (Finset B)}
  (h1s: ∀ i j, (x1 i j).support = S1 i j) (h1b: ∀ i j, (x1 i j).IsBag)
  (h2s: ∀ i j, (x2 i j).support = S2 i j) (h2b: ∀ i j, (x2 i j).IsBag)
  (his1: ∀ i j, (Finset.range (i+1)).biUnion (fun k => S1 k j) = IS1 i j)
  (his2: ∀ i j, (Finset.range (i+1)).biUnion (fun k => S2 k j) = IS2 i j):
    HoareR (fun y => y = sprod2 (x1, x2)) (@cI ([Z[A]]v ×ᵥ [Z[B]]v) 1)
      (fun y => ∃ (y1: SOType 1 Z[A]) (y2: SOType 1 Z[B]),
        y = sprod2 (y1, y2) ∧
        (∀ i j, (y1 i j).support = IS1 i j) ∧ (∀ i j, (y1 i j).IsBag) ∧
        (∀ i j, (y2 i j).support = IS2 i j) ∧ (∀ i j, (y2 i j).IsBag))
      (fun i j =>
        (S1 i j).card + (IS1 (i - 1) j).card + (IS1 i j).card +
        (S2 i j).card + (IS2 (i - 1) j).card + (IS2 i j).card) := by
  have hr1 := fun j => integral_support (fun i => h1s i j) (fun i => h1b i j)
  have hr2 := fun j => integral_support (fun i => h2s i j) (fun i => h2b i j)
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_I
  · intro i j; simp [add_cost, Zset.size, VType_space, integral_sprod2]
    simp_rw [← his1, ← his2]
    rcases i with _ | i <;> simp [-integral_succ]
    · rw [h1s, h2s]; omega
    · simp_rw [← nested_stream_I_fun_eq]
      simp_rw [(hr1 j).1, (hr2 j).1, h1s, h2s]; omega
  · intro y hy; subst hy
    rw [integral_sprod2]
    refine ⟨I x1, I x2, rfl, ?_, ?_, ?_, ?_⟩ <;> intro i j <;> rw [← nested_stream_I_fun_eq]
    · rw [(hr1 j).1, his1]
    · exact (hr1 j).2 i
    · rw [(hr2 j).1, his2]
    · exact (hr2 j).2 i

theorem HoareR_lifted_I_support {x: SOType 1 Z[A]} {S: SOType 1 (Finset A)}
  (h1s: ∀ i j, (x i j).support = S i j) (h1b: ∀ i j, (x i j).IsBag)
  (S2: SOType 1 (Finset A)) (hres: ∀ i j, (Finset.range (j+1)).biUnion (S i) = S2 i j):
    HoareR (fun y => y = x) (@lifted_I [Z[A]]v)
      (fun y => (∀ i j, (y i j).support = S2 i j) ∧ (∀ i j, (y i j).IsBag))
      (fun i j => (S i j).card + (S2 i (j-1)).card + (S2 i j).card) := by
  have hr := fun i => integral_support (fun j => h1s i j) (fun j => h1b i j)
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_lifted_I
  · intro i j; simp [add_cost, Zset.size, VType_space]
    simp_rw [<- hres]
    rcases j <;> simp [-integral_succ]
    · rw [h1s]; omega
    · simp_rw [(hr i).1, h1s]
      rw [show (fun k ↦ S i k) = S i by funext k; simp]
  · simp; constructor <;> intro i j
    · rw [(hr i).1, hres]
    · apply (hr i).2

theorem HoareR_delay_support_ns1 {x: SOType 1 Z[A]} {S: SOType 1 (Finset A)}
  (h1s: ∀ i j, (x i j).support = S i j) (h1b: ∀ i j, (x i j).IsBag):
    HoareR (fun y => y = x) (@Ckt.delay 1 [Z[A]]v)
      (fun y => (∀ i j, (y i j).support = z⁻¹ S i j) ∧ (∀ i j, (y i j).IsBag))
      (fun i j => (S i j).card) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_delay
  · intro i j; simp [VType_space, Zset.size]
    rw [h1s]
  · simp; constructor
    · intro i j; rcases i with _ | i <;> simp
      rw [h1s]
    · intro i j; rcases i <;> simp [h1b]

theorem HoareR_lifted_delay_support_ns1 {x: SOType 1 Z[A]} {S: SOType 1 (Finset A)}
  (h1s: ∀ i j, (x i j).support = S i j) (h1b: ∀ i j, (x i j).IsBag):
    HoareR (fun y => y = x) (@Ckt.lifted_delay [Z[A]]v)
      (fun y => (∀ i j, (y i j).support = ↑↑z⁻¹ S i j) ∧ (∀ i j, (y i j).IsBag))
      (fun i j => (S i j).card) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_lifted_delay
  · intro i j; simp [VType_space, Zset.size]
    rw [h1s]
  · simp; constructor
    · intro i j; rcases j with _ | i <;> simp
      rw [h1s]
    · intro i j; rcases j <;> simp [h1b]

theorem HoareR_join_support_ns1 (π1 : A → C) (π2 : B → C)
  {x1: stream (stream Z[A])} {x2: stream (stream Z[B])}
  {S1: stream (stream (Finset A))} {S2: stream (stream (Finset B))}
  (h1s: ∀ i j, (x1 i j).support = S1 i j) (h1b: ∀ i j, (x1 i j).IsBag)
  (h2s: ∀ i j, (x2 i j).support = S2 i j) (h2b: ∀ i j, (x2 i j).IsBag):
    HoareR (fun y => y = sprod2 (x1, x2)) (Ckt.node2 (ns:=1) (EquiJoinBinaryNode π1 π2))
      (fun y => (∀ i j, (y i j).support = {t ∈ S1 i j ×ˢ S2 i j | π1 t.1 = π2 t.2}) ∧ (∀ i j, (y i j).IsBag))
      (fun i j => (S1 i j).card * (S2 i j).card) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_Zset_join
  · intro i j; simp
    unfold Zset.size
    rw [h1s, h2s]
  · simp; constructor <;> intro i j
    · simp [equiJoin_support, h1s, h2s]
    · apply equiJoin_pos <;> tauto

theorem HoareR_add_support_ns1 {x1 x2: stream (stream Z[A])} {S1 S2: stream (stream (Finset A))}
  (h1s: ∀ i j, (x1 i j).support = S1 i j) (h1b: ∀ i j, (x1 i j).IsBag)
  (h2s: ∀ i j, (x2 i j).support = S2 i j) (h2b: ∀ i j, (x2 i j).IsBag):
    HoareR (fun y => y = sprod2 (x1, x2)) (Ckt.add (ns:=1) (a := [Z[A]]v))
      (fun y => (∀ i j, (y i j).support = S1 i j ∪ S2 i j) ∧ (∀ i j, (y i j).IsBag))
      (fun i j => (S1 i j).card + (S2 i j).card) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_Zset_add
  · intro i j; simp
    unfold Zset.size
    rw [h1s, h2s]
  · simp; constructor <;> intro i j
    · rw [Zset.isBag_add_support, h1s, h2s] <;> tauto
    · apply Zset.add_pos <;> tauto

theorem HoareR_map_support_ns1 (f: A → B)
  {x: stream (stream Z[A])} {S: stream (stream (Finset A))}
  (h1s: ∀ i j, (x i j).support = S i j) (h1b: ∀ i j, (x i j).IsBag):
    HoareR (fun y => y = x) (Ckt.node1 (ns:=1) (MapUnaryNode f))
      (fun y => (∀ i j, (y i j).support = Finset.image f (S i j)) ∧ (∀ i j, (y i j).IsBag))
      (fun i j => (S i j).card) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_Zset_map
  · intro i j; simp
    unfold Zset.size
    rw [h1s]
  · simp; constructor <;> intro i j
    · rw [Zset.isBag_map_support, h1s]; tauto
    · apply map_pos; tauto

theorem HoareR_H_support_ns1 {x1 x2: stream (stream Z[A])} {S1 S2: stream (stream (Finset A))}
  (h1s: ∀ i j, (x1 i j).support = S1 i j) (h1b: ∀ i j, (x1 i j).IsBag)
  (h2s: ∀ i j, (x2 i j).support = S2 i j) (h2b: ∀ i j, (x2 i j).IsBag):
    HoareR (fun y => y = sprod2 (x1, x2)) (Ckt.node2 (ns:=1) HBinaryNode)
      (fun y => ∀ i j, y i j = Zset.fromSet (S2 i j \ S1 i j))
      (fun i j => (S1 i j).card + (S2 i j).card) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_Zset_H
  · intro i j; simp
    unfold Zset.size
    rw [h1s, h2s]
  · simp; intro i j
    rw [distinctH_support_isBag, h1s, h2s]
    all_goals tauto

--- HoareR with ZSB - using ZSB as hypothesis (polymorphic w.r.t. ns)
theorem HoareR_ZSB_add {x1 x2: SOType ns Z[A]} {b1 b2}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2):
    HoareR (fun y => y = sprodO ns (x1, x2)) (Ckt.add (ns := ns) (a := [Z[A]]v))
      (fun y => ZSB y (b1 + b2))
      (b1 + b2) := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns with _ | _
    · simp only [IntConv, denote, ZSB, liftO, sprodO, sprod]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_add
      apply add_le_add <;> tauto
    · simp only [IntConv, denote, ZSB, liftO, sprodO, sprod2]
      refine ⟨trivial, ?_⟩
      intro i m; simp
      apply le_trans; apply Zset_size_add
      apply add_le_add <;> tauto
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, add_cost, BaseType.add_cost, liftO, Zset.size, sprodO, sprod, sprod2]
    · apply add_le_add <;> tauto
    · intro i; apply add_le_add <;> tauto

theorem HoareR_ZSB_sub {x1 x2: SOType ns Z[A]} {b1 b2}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2):
    HoareR (fun y => y = sprodO ns (x1, x2)) (Ckt.sub (ns := ns) (a := [Z[A]]v))
      (fun y => ZSB y (b1 + b2))
      (b1 + b2) := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns with _ | _
    · simp only [IntConv, denote, ZSB, liftO, sprodO, sprod]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_sub
      apply add_le_add <;> tauto
    · simp only [IntConv, denote, ZSB, liftO, sprodO, sprod2]
      refine ⟨trivial, ?_⟩
      intro i m; simp
      apply le_trans; apply Zset_size_sub
      apply add_le_add <;> tauto
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, sub_cost, BaseType.sub_cost, liftO, Zset.size, sprodO, sprod, sprod2]
    · apply add_le_add <;> tauto
    · intro i; apply add_le_add <;> tauto

theorem HoareR_ZSB_distinct {x: SOType ns Z[A]} {b}
  (h: ZSB x b):
    HoareR (fun y => y = x) (Ckt.node1 (ns := ns) DistinctUnaryNode)
      (fun y => ZSB y b)
      b := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns with _ | _
    · simp only [IntConv, denote, ZSB, liftO, DistinctUnaryNode]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_distinct; apply h
    · simp only [IntConv, denote, ZSB, liftO, DistinctUnaryNode]
      refine ⟨trivial, ?_⟩
      intro i m; simp
      apply le_trans; apply Zset_size_distinct; apply h
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, UnaryNode.cost, DistinctUnaryNode, liftO, Zset.size] <;> tauto

theorem HoareR_ZSB_map {f: A → B} {x: SOType ns Z[A]} {b}
  (h: ZSB x b):
    HoareR (fun y => y = x) (Ckt.node1 (ns := ns) (MapUnaryNode f))
      (fun y => ZSB y b)
      b := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns with _ | _
    · simp only [IntConv, denote, ZSB, liftO, MapUnaryNode]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_map; apply h
    · simp only [IntConv, denote, ZSB, liftO, MapUnaryNode]
      refine ⟨trivial, ?_⟩
      intro i m; simp
      apply le_trans; apply Zset_size_map; apply h
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, UnaryNode.cost, MapUnaryNode, liftO, Zset.size] <;> tauto

theorem HoareR_ZSB_filter {p: A → Prop} [DecidablePred p] {x: SOType ns Z[A]} {b}
  (h: ZSB x b):
    HoareR (fun y => y = x) (Ckt.node1 (ns := ns) (FilterUnaryNode p))
      (fun y => ZSB y b)
      b := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns with _ | _
    · simp only [IntConv, denote, ZSB, liftO, FilterUnaryNode]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_filter; apply h
    · simp only [IntConv, denote, ZSB, liftO, FilterUnaryNode]
      refine ⟨trivial, ?_⟩
      intro i m; simp
      apply le_trans; apply Zset_size_filter; apply h
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, UnaryNode.cost, FilterUnaryNode, liftO, Zset.size] <;> tauto

theorem HoareR_ZSB_H {x1 x2: SOType ns Z[A]} {b1 b2}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2):
    HoareR (fun y => y = sprodO ns (x1, x2)) (Ckt.node2 (ns := ns) HBinaryNode)
      (fun y => ZSB y (b1 + b2))
      (b1 + b2) := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns with _ | _
    · simp only [IntConv, denote, ZSB, liftO, HBinaryNode, sprodO, sprod]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_H
      apply add_le_add <;> tauto
    · simp only [IntConv, denote, ZSB, liftO, HBinaryNode, sprodO, sprod2]
      refine ⟨trivial, ?_⟩
      intro i m; simp
      apply le_trans; apply Zset_size_H
      apply add_le_add <;> tauto
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, BinaryNode.cost, HBinaryNode, liftO, Zset.size, sprodO, sprod, sprod2]
    · apply add_le_add <;> tauto
    · intro i; apply add_le_add <;> tauto

theorem HoareR_ZSB_join {π1 : A → C} {π2 : B → C}
    {x1: SOType ns Z[A]} {x2: SOType ns Z[B]} {b1 b2}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2):
    HoareR (fun y => y = sprodO ns (x1, x2)) (Ckt.node2 (ns := ns) (EquiJoinBinaryNode π1 π2))
      (fun y => ZSB y (liftO ns (fun p => p.1 * p.2) (sprodO ns (b1, b2))))
      (liftO ns (fun p => p.1 * p.2) (sprodO ns (b1, b2))) := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns with _ | _
    · simp only [IntConv, denote, ZSB, liftO, EquiJoinBinaryNode, sprodO, sprod]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_join
      apply mul_le_mul' <;> tauto
    · simp only [IntConv, denote, ZSB, liftO, EquiJoinBinaryNode, sprodO, sprod2]
      refine ⟨trivial, ?_⟩
      intro i m; simp
      apply le_trans; apply Zset_size_join
      apply mul_le_mul' <;> tauto
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, BinaryNode.cost, EquiJoinBinaryNode, liftO, Zset.size, sprodO, sprod, sprod2]
    · intro m; simp; apply mul_le_mul' <;> tauto
    · intro i m; simp; apply mul_le_mul' <;> tauto

theorem HoareR_ZSB_delay {x: SOType ns Z[A]} {b}
  (h: ZSB x b):
    HoareR (fun y => y = x) (Ckt.delay (ns := ns) (a := [Z[A]]v))
      (fun y => ZSB y (z⁻¹ b)) b := by
  constructor
  case post =>
    intro y hy; subst hy
    rcases ns with _ | _
    · simp only [IntConv, denote, ZSB, liftO]
      refine ⟨trivial, ?_⟩
      rw [Zsize_delay]
      intro m; simp [delay]
      split_ifs; simp
      apply h
    · simp only [IntConv, denote, ZSB, liftO]
      refine ⟨trivial, ?_⟩
      intro i m; simp [delay]
      split_ifs; simp [Zset.size]
      apply h
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, liftO, Zset.size]
    · intro i; simp [VType_space, BaseType.size]; apply h
    · intro i j; simp [VType_space, BaseType.size]; apply h

theorem HoareR_ZSB_I {x: SOType ns Z[A]} {b}
  (h: ZSB x b):
    HoareR (fun y => y = x) (cI (a := [Z[A]]v) (ns := ns))
      (fun y => ZSB y (I b))
      (3 • I b) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_Zset_I
  · apply smul_mono_right
    apply mono_integral; tauto
  · intro y _; subst y
    apply ZSB_I h

--- stream_id_distinct lemmas (ns = false only)
section sid_lemmas
variable {A B C: Type} [DecidableEq A]

lemma HoareR_sid_I {x: stream Z[A]} {b} {π: A → B}
  (h: ZSB x b) (hd: stream_id_distinct π x):
    HoareR (fun y => y = x) (cI (a := [Z[A]]v) (ns := false))
      (fun y => ZSB y (I b) ∧ stream_id_distinct π y)
      (3 • I b) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_Zset_I
  · apply smul_mono_right
    apply mono_integral; tauto
  · intro y _;subst y
    constructor; apply ZSB_I h
    apply integral_id_distinct hd

lemma HoareR_sid_delay {x: stream Z[A]} {b} {π: A → B}
  (h: ZSB x b) (hb: Monotone b) (hd: stream_id_distinct π x):
    HoareR (fun y => y = x) (Ckt.delay (ns := false) (a := [Z[A]]v))
      (fun y => ZSB y b ∧ stream_id_distinct π y)
      b := by
  constructor
  case post =>
    intro y hy; subst hy
    simp only [IntConv, denote, ZSB, liftO]
    refine ⟨trivial, ?_, ?_⟩
    · rw [Zsize_delay]
      intro m; simp [delay]
      split_ifs; simp
      apply le_trans; apply h; apply hb; omega
    · apply delay_id_distinct; tauto
  case cost =>
    intro y hy; subst hy
    simp only [cost_f, VType_space, BaseType.size, liftO, Zset.size]; tauto

lemma HoareR_sid_filter {p: A → Prop} [DecidablePred p]
  {x: stream Z[A]} {b} {π: A → B}
  (h: ZSB x b) (hd: stream_id_distinct π x):
    HoareR (fun y => y = x) (Ckt.node1 (ns := false) (FilterUnaryNode p))
      (fun y => ZSB y b ∧ stream_id_distinct π y)
      b := by
  constructor
  case post =>
    intro y hy; subst hy
    simp only [IntConv, denote, ZSB, liftO, FilterUnaryNode]
    refine ⟨trivial, ?_, ?_⟩
    · intro m; simp
      apply le_trans; apply Zset_size_filter; apply h
    · apply lifting_filter_id_distinct; tauto
  case cost =>
    intro y hy; subst hy
    simp only [cost_f, UnaryNode.cost, FilterUnaryNode, liftO, Zset.size]; tauto

lemma HoareR_sid_map
  {x: stream Z[A]} {b} {f: A → B} {g: B → C} [DecidableEq B]
  (h: ZSB x b) (hd: stream_id_distinct (g ∘ f) x):
    HoareR (fun y => y = x) (Ckt.node1 (ns := false) (MapUnaryNode f))
      (fun y => ZSB y b ∧ stream_id_distinct g y)
      b := by
  constructor
  case post =>
    intro y hy; subst hy
    simp only [IntConv, denote, ZSB, liftO, MapUnaryNode]
    refine ⟨trivial, ?_, ?_⟩
    · intro m; simp
      apply le_trans; apply Zset_size_map; apply h
    · apply lifting_map_id_distinct; tauto
  case cost =>
    intro y hy; subst hy
    simp only [cost_f, UnaryNode.cost, MapUnaryNode, liftO, Zset.size]; tauto

lemma HoareR_sid_join {π1 : A → C} {π2 : B → C} [DecidableEq B] [DecidableEq C]
  {x1: stream Z[A]} {x2: stream Z[B]} {b1 b2}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2)
  (h1d: stream_id_distinct π1 x1) (h2d: stream_id_distinct π2 x2):
    HoareR (fun y => y = sprod (x1, x2)) (Ckt.node2 (ns := false) (EquiJoinBinaryNode π1 π2))
      (fun y => ZSB y (fun i => min (b1 i) (b2 i)))
      (fun i => b1 i * b2 i) := by
  constructor
  case post =>
    intro y hy; subst hy
    simp only [IntConv, denote, EquiJoinBinaryNode, sprodO, sprod]
    refine ⟨trivial, ?_⟩
    intro m; simp only [liftO, Zset.size, Zset_join]
    apply le_trans
    apply equiJoin_id_distinct_size
    · apply stream_id_distinct_to_id_distinct; tauto
    · apply stream_id_distinct_to_id_distinct; tauto
    simp; constructor <;> tauto
  case cost =>
    intro y hy; subst hy
    simp only [cost_f, BinaryNode.cost, EquiJoinBinaryNode, liftO, Zset.size, sprodO, sprod]
    intro i; apply mul_le_mul' <;> tauto

lemma HoareR_sid_join_l {π1 : A → C} {π2 : B → C} [DecidableEq B] [DecidableEq C]
  {x1: stream Z[A]} {x2: stream Z[B]} {b1 b2}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2)
  (h1d: stream_id_distinct π1 x1) (h2d: stream_id_distinct π2 x2):
    HoareR (fun y => y = sprod (x1, x2)) (Ckt.node2 (ns := false) (EquiJoinBinaryNode π1 π2))
      (fun y => ZSB y b1)
      (fun i => b1 i * b2 i) := by
  apply HoareR_conseq_post (HoareR_sid_join h1 h2 h1d h2d)
  intro y hy
  intro m; apply le_trans; apply hy; simp

lemma HoareR_sid_join_r {π1 : A → C} {π2 : B → C} [DecidableEq B] [DecidableEq C]
  {x1: stream Z[A]} {x2: stream Z[B]} {b1 b2}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2)
  (h1d: stream_id_distinct π1 x1) (h2d: stream_id_distinct π2 x2):
    HoareR (fun y => y = sprod (x1, x2)) (Ckt.node2 (ns := false) (EquiJoinBinaryNode π1 π2))
      (fun y => ZSB y b2)
      (fun i => b1 i * b2 i) := by
  apply HoareR_conseq_post (HoareR_sid_join h1 h2 h1d h2d)
  intro y hy
  intro m; apply le_trans; apply hy; simp

end sid_lemmas

end ZsetCkt

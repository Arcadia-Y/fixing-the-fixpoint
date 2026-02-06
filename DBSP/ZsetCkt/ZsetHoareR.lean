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
    rcases ns <;> simp [Terminate, denote]
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
    rcases ns <;> simp [Terminate, denote]
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
    rcases ns <;> simp only [Terminate, denote, DistinctUnaryNode, liftO] <;> trivial
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
    rcases ns <;> simp only [Terminate, denote, MapUnaryNode, liftO] <;> trivial
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
    rcases ns <;> simp only [Terminate, denote, FilterUnaryNode, liftO] <;> trivial
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
    rcases ns <;> simp only [Terminate, denote, HBinaryNode, Zset_H, liftO, sprodO, sprod, sprod2] <;> trivial
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
    rcases ns <;> simp only [Terminate, denote, ProductBinaryNode, Zset_product, liftO, sprodO, sprod, sprod2] <;> trivial
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
    rcases ns <;> simp only [Terminate, denote, EquiJoinBinaryNode, Zset_join, liftO, sprodO, sprod, sprod2] <;> trivial
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp only [cost_f, BinaryNode.cost, EquiJoinBinaryNode, liftO, Zset.size, sprodO, sprod, sprod2] <;> rfl

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
    · simp only [Terminate, denote, ZSB, liftO, sprodO, sprod]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_add
      apply add_le_add <;> tauto
    · simp only [Terminate, denote, ZSB, liftO, sprodO, sprod2]
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
    · simp only [Terminate, denote, ZSB, liftO, sprodO, sprod]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_sub
      apply add_le_add <;> tauto
    · simp only [Terminate, denote, ZSB, liftO, sprodO, sprod2]
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
    · simp only [Terminate, denote, ZSB, liftO, DistinctUnaryNode]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_distinct; apply h
    · simp only [Terminate, denote, ZSB, liftO, DistinctUnaryNode]
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
    · simp only [Terminate, denote, ZSB, liftO, MapUnaryNode]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_map; apply h
    · simp only [Terminate, denote, ZSB, liftO, MapUnaryNode]
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
    · simp only [Terminate, denote, ZSB, liftO, FilterUnaryNode]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_filter; apply h
    · simp only [Terminate, denote, ZSB, liftO, FilterUnaryNode]
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
    · simp only [Terminate, denote, ZSB, liftO, HBinaryNode, sprodO, sprod]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_H
      apply add_le_add <;> tauto
    · simp only [Terminate, denote, ZSB, liftO, HBinaryNode, sprodO, sprod2]
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
    · simp only [Terminate, denote, ZSB, liftO, EquiJoinBinaryNode, sprodO, sprod]
      refine ⟨trivial, ?_⟩
      intro m; simp
      apply le_trans; apply Zset_size_join
      apply mul_le_mul' <;> tauto
    · simp only [Terminate, denote, ZSB, liftO, EquiJoinBinaryNode, sprodO, sprod2]
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
    · simp only [Terminate, denote, ZSB, liftO]
      refine ⟨trivial, ?_⟩
      rw [Zsize_delay]
      intro m; simp [delay]
      split_ifs; simp
      apply h
    · simp only [Terminate, denote, ZSB, liftO]
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
    simp only [Terminate, denote, ZSB, liftO]
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
    simp only [Terminate, denote, ZSB, liftO, FilterUnaryNode]
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
    simp only [Terminate, denote, ZSB, liftO, MapUnaryNode]
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
    simp only [Terminate, denote, EquiJoinBinaryNode, sprodO, sprod]
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

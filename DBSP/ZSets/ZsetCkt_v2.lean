-- consider splitting the ZsetCkt definition part and the resource anlysis part
import DBSP.Circuits.Circuits_v2
import DBSP.ZSets.Zset
import DBSP.ZSets.Relational
import DBSP.ZSets.RelationalIncremental
import DBSP.Logic.DHoare_v4
import DBSP.ResourceAnalysis.Dominate_v3
open CktBasic

section ZsetCkt
variable {A B C: Type} [DecidableEq A]  [DecidableEq B]  [DecidableEq C]
-- We currently only care about the size of a Zset and ignore its contents
instance ZsetBaseType: BaseType (Z[A]) where
  has_group := by infer_instance
  size := Zset.size
  add_cost := fun (x, y) => x.size + y.size
  sub_cost := fun (x, y) => x.size + y.size

instance DistinctUnaryNode:
    UnaryNode (@Zset.distinct A _) where
  cost := fun x => x.size

instance MapUnaryNode (f: A -> B):
    UnaryNode (Zset.map f) where
  cost := fun x => x.size

instance FilterUnaryNode (p: A -> Prop) [DecidablePred p]:
    UnaryNode (filter p) where
  cost := fun x => x.size

@[simp]
def Zset_H (x: Z[A] × Z[A]): Z[A] := distinctH x.1 x.2
instance HBinaryNode:
    BinaryNode (@Zset_H A _) where
  cost := fun x => x.fst.size + x.snd.size

@[simp]
def Zset_product (x: Z[A] × Z[B]): Z[A × B] := product x.1 x.2
instance ProductBinaryNode:
    BinaryNode (@Zset_product A B _ _) where
  cost := fun x => x.fst.size * x.snd.size

@[simp]
def Zset_join (π1 : A → C) (π2 : B → C) (x: Z[A] × Z[B]): Z[A × B] :=
  equiJoin π1 π2 x.1 x.2
instance EquiJoinBinaryNode (π1 : A → C) (π2 : B → C):
    BinaryNode (Zset_join π1 π2) where
  cost := fun x => x.fst.size * x.snd.size

-- TODO: intersection

--- Zset.size Lemmas
lemma Zset_size_add (x1 x2: Z[A]):
    Zset.size (x1 + x2) ≤ Zset.size x1 + Zset.size x2 := by
  simp; rw [Zset.add_support]
  apply le_trans
  · apply Finset.card_filter_le
  · apply le_trans
    · apply Finset.card_union_le
    · rfl

lemma Zset_size_sub (x1 x2: Z[A]):
    Zset.size (x1 - x2) ≤ Zset.size x1 + Zset.size x2 := by
  simp; rw [Zset.sub_support]
  apply le_trans
  · apply Finset.card_filter_le
  · apply le_trans
    · apply Finset.card_union_le
    · rfl

lemma Zset_size_distinct (x: Z[A]):
    Zset.size (Zset.distinct x) ≤ Zset.size x := by
  simp; rw [Zset.distinct_support]
  apply le_trans; apply Finset.card_filter_le; rfl

lemma Zset_size_map (f: A → B) (x: Z[A]):
    Zset.size (Zset.map f x) ≤ Zset.size x := by
  simp; apply le_trans
  apply Finset.card_le_card; apply Zset.map_support_image
  apply le_trans; apply Finset.card_image_le; tauto

lemma Zset_size_filter (p: A → Prop) [DecidablePred p] (x: Z[A]):
    Zset.size (filter p x) ≤ Zset.size x := by
  simp; rw [filter_support]
  apply le_trans; apply Finset.card_filter_le; rfl

lemma Zset_size_H (x1 x2: Z[A]):
    Zset.size (Zset_H (x1, x2)) ≤ Zset.size x1 + Zset.size x2 := by
  simp
  suffices h:
    (DFinsupp.support (distinctH x1 x2)).card ≤
    (DFinsupp.support x1 ∪ DFinsupp.support x2).card by
    apply le_trans h
    apply le_trans; apply Finset.card_union_le; rfl
  apply Finset.card_le_card
  intro a; simp [distinctH]
  contrapose; simp

lemma Zset_size_product (x1: Z[A]) (x2: Z[B]):
    Zset.size (Zset_product (x1, x2)) ≤ Zset.size x1 * Zset.size x2 := by
  simp; rw [product_support]; simp

lemma Zset_size_join (π1 : A → C) (π2 : B → C) (x1: Z[A]) (x2: Z[B]):
    Zset.size (Zset_join π1 π2 (x1, x2)) ≤ Zset.size x1 * Zset.size x2 := by
  simp; unfold equiJoin
  rw [filter_support, product_support]; simp
  apply le_trans; apply Finset.card_filter_le; simp

-- DHoare Zset Lemmas
variable {n: ℕ} {ns: Bool}

lemma DHoare_Zset_add {x1 x2: stream (Optstream ns Z[A])}:
    DHoare n (@Ckt.add ns (VType.base Z[A])) (sprodO ns (x1, x2))
      (fun y _ => y = x1 + x2)
      1 (liftO ns Zset.size x1 + liftO ns Zset.size x2) := by
  constructor
  · intro _ _; simp [denote]
    rcases ns <;> rfl
  · intro _ _; simp [cost_f]
    rcases ns <;> rfl

lemma DHoare_Zset_sub {x1 x2: stream (Optstream ns Z[A])}:
    DHoare n (@Ckt.sub ns (VType.base Z[A])) (sprodO ns (x1, x2))
      (fun y _ => y = x1 - x2)
      1 (liftO ns Zset.size x1 + liftO ns Zset.size x2) := by
  constructor
  · intro _ _; simp [denote]
    rcases ns <;> rfl
  · intro _ _; simp [cost_f]
    rcases ns <;> rfl

lemma DHoare_Zset_distinct {x: stream Z[A]}:
    DHoare n (c₁ (@Zset.distinct A _)) x
      (fun y _ => y = ↑↑Zset.distinct x)
      1 (↑↑Zset.size x) := by
  constructor
  · intro _ _; simp [denote]
  · intro _ _; simp [cost_f, UnaryNode.cost]

lemma DHoare_Zset_map (f: A → B) {x: stream Z[A]}:
    DHoare n (c₁ (Zset.map f)) x
      (fun y _ => y = ↑↑(Zset.map f) x)
      1 (↑↑Zset.size x) := by
  constructor
  · intro _ _; simp [denote]
  · intro _ _; simp [cost_f, UnaryNode.cost]

lemma DHoare_Zset_filter (p: A → Prop) [DecidablePred p] {x: stream Z[A]}:
    DHoare n (c₁ (filter p)) x
      (fun y _ => y = ↑↑(filter p) x)
      1 (↑↑Zset.size x) := by
  constructor
  · intro _ _; simp [denote]
  · intro _ _; simp [cost_f, UnaryNode.cost]

lemma DHoare_Zset_H {x1 x2: stream Z[A]}:
    DHoare n (c₂ (@Zset_H A _)) (sprod (x1, x2))
      (fun y _ => y = ↑↑Zset_H (x1, x2))
      1 (↑↑Zset.size x1 + ↑↑Zset.size x2) := by
  constructor
  · intro _ _; simp [denote]; rfl
  · intro _ _; simp [cost_f]; rfl

lemma DHoare_Zset_product {x1: stream Z[A]} {x2: stream Z[B]}:
    DHoare n (c₂ (@Zset_product A B _ _)) (sprod (x1, x2))
      (fun y _ => y = ↑↑Zset_product (x1, x2))
      1 (fun i => Zset.size (x1 i) * Zset.size (x2 i)) := by
  constructor
  · intro _ _; simp [denote]; rfl
  · intro _ _; simp [cost_f]; rfl

lemma DHoare_Zset_join (π1 : A → C) (π2 : B → C)
    {x1: stream Z[A]} {x2: stream Z[B]}:
    DHoare n (c₂ (Zset_join π1 π2)) (sprod (x1, x2))
      (fun y _ => y = ↑↑(Zset_join π1 π2) (x1, x2))
      1 (fun i => Zset.size (x1 i) * Zset.size (x2 i)) := by
  constructor
  · intro _ _; simp [denote]; rfl
  · intro _ _; simp [cost_f]; rfl

theorem DHoare_Zset_I (x: stream Z[A]):
    DHoare n (@cI false [Z[A]]v) x (fun y _ => y = I x)
      1 (↑↑Zset.size x + ↑↑Zset.size (z⁻¹ (I x)) + ↑↑Zset.size (I x)) := by
  constructor
  · intro _ _; simp
  · intro _ _; simp [cost_f, cI]
    rw [<- cI, cI_denote]
    simp [add_cost, BaseType.add_cost, VType_space, BaseType.size]

theorem DHoare_Zset_D (x: stream Z[A]):
    DHoare n (@cD false [Z[A]]v) x (fun y _ => y = D x)
      1 (↑↑Zset.size x + ↑↑Zset.size x + ↑↑Zset.size (z⁻¹ x)) := by
  constructor
  · intro _ _; simp
  · intro _ _; simp [cost_f, cD, denote]
    simp [sub_cost, BaseType.sub_cost, VType_space, BaseType.size]
    omega

--- DHoare with Zset SizeBound
def ZSB (x: stream Z[A]) (k n: ℕ) (b: stream ℕ) :=
  ↑↑Zset.size x <[k, n] b

-- lemmas on Dom and Zset operations
lemma ZSB_add {x1 x2: stream Z[A]} {k1 b1 k2 b2}
  (h1: ZSB x1 k1 n b1) (h2: ZSB x2 k2 n b2):
    ZSB (x1 + x2) (max k1 k2) n (b1 + b2) := by
  apply Dom_scale_k; apply Dom_trans
  case h.k1 => exact 1
  intro m hm; simp [-Zset.size]; apply Zset_size_add
  apply Dom_add_Dom <;> tauto
  simp

lemma ZSB_sub {x1 x2: stream Z[A]} {k1 b1 k2 b2}
  (h1: ZSB x1 k1 n b1) (h2: ZSB x2 k2 n b2):
    ZSB (x1 - x2) (max k1 k2) n (b1 + b2) := by
  apply Dom_scale_k; apply Dom_trans
  case h.k1 => exact 1
  intro m hm; simp [-Zset.size]; apply Zset_size_sub
  apply Dom_add_Dom <;> tauto
  simp

lemma ZSB_distinct {x: stream Z[A]} {k b}
  (h: ZSB x k n b):
    ZSB (↑↑Zset.distinct x) k n b := by
  intro m hm; simp [-Zset.size]
  specialize h m hm; simp [-Zset.size] at h
  apply le_trans; apply Zset_size_distinct; tauto


lemma ZSB_map {f: A → B} {x: stream Z[A]} {k b}
  (h: ZSB x k n b):
    ZSB (↑↑(Zset.map f) x) k n b := by
  intro m hm; simp [-Zset.size]
  specialize h m hm; simp [-Zset.size] at h
  apply le_trans; apply Zset_size_map; tauto

lemma ZSB_filter {p: A → Prop} [DecidablePred p] {x: stream Z[A]} {k b}
  (h: ZSB x k n b):
    ZSB (↑↑(filter p) x) k n b := by
  intro m hm; simp [-Zset.size]
  specialize h m hm; simp [-Zset.size] at h
  apply le_trans; apply Zset_size_filter; tauto

lemma ZSB_H {x1 x2: stream Z[A]} {k1 b1 k2 b2}
  (h1: ZSB x1 k1 n b1) (h2: ZSB x2 k2 n b2):
    ZSB (↑↑Zset_H (sprod (x1, x2))) (max k1 k2) n (b1 + b2) := by
  apply Dom_scale_k; apply Dom_trans
  case h.k1 => exact 1
  intro m hm; simp [-Zset.size]; apply Zset_size_H
  apply Dom_add_Dom <;> tauto
  simp

lemma ZSB_product {x1: stream Z[A]} {x2: stream Z[B]} {k1 b1 k2 b2}
  (h1: ZSB x1 k1 n b1) (h2: ZSB x2 k2 n b2):
    ZSB (↑↑Zset_product (sprod (x1, x2))) (k1 * k2) n (fun i => b1 i * b2 i) := by
  apply Dom_scale_k; apply Dom_trans
  case h.k1 => exact 1
  intro m hm; simp [-Zset.size]; apply Zset_size_product
  apply Dom_mul_Dom <;> tauto
  simp

lemma ZSB_join {π1 : A → C} {π2 : B → C}
    {x1: stream Z[A]} {x2: stream Z[B]} {k1 b1 k2 b2}
  (h1: ZSB x1 k1 n b1) (h2: ZSB x2 k2 n b2):
    ZSB (↑↑(Zset_join π1 π2) (sprod (x1, x2))) (k1 * k2) n (fun i => b1 i * b2 i) := by
  apply Dom_scale_k; apply Dom_trans
  case h.k1 => exact 1
  intro m hm; simp [-Zset.size]; apply Zset_size_join
  apply Dom_mul_Dom <;> tauto
  simp

lemma DHoare_ZSB_add {x1 x2: stream Z[A]} {k1 b1 k2 b2}
  (h1: ZSB x1 k1 n b1) (h2: ZSB x2 k2 n b2):
    DHoare n (@Ckt.add false [Z[A]]v) (sprod (x1, x2))
      (fun y _ => ZSB y (max k1 k2) n (b1 + b2))
      (max k1 k2) (b1 + b2) := by
  apply DHoare_scale_k; apply DHoare_weaken; apply DHoare_conseq
  apply DHoare_Zset_add
  intro y _ hy; subst hy
  apply ZSB_add <;> tauto
  simp; apply Dom_add_Dom <;> tauto
  simp

lemma DHoare_ZSB_sub {x1 x2: stream Z[A]} {k1 b1 k2 b2}
  (h1: ZSB x1 k1 n b1) (h2: ZSB x2 k2 n b2):
    DHoare n (@Ckt.sub false [Z[A]]v) (sprod (x1, x2))
      (fun y _ => ZSB y (max k1 k2) n (b1 + b2))
      (max k1 k2) (b1 + b2) := by
  apply DHoare_scale_k; apply DHoare_weaken; apply DHoare_conseq
  apply DHoare_Zset_sub
  intro y _ hy; subst hy
  apply ZSB_sub <;> tauto
  simp; apply Dom_add_Dom <;> tauto
  simp

lemma DHoare_ZSB_distinct {x: stream Z[A]} {k b}
  (h: ZSB x k n b):
    DHoare n (c₁ (Zset.distinct)) x
      (fun y _ => ZSB y k n b) k b := by
  apply DHoare_scale_k; apply DHoare_weaken; apply DHoare_conseq
  apply DHoare_Zset_distinct
  intro y _ hy; subst hy
  apply ZSB_distinct; tauto
  apply h; simp

lemma DHoare_ZSB_map {f: A → B} {x: stream Z[A]} {k b}
  (h: ZSB x k n b):
    DHoare n (c₁ (Zset.map f)) x
      (fun y _ => ZSB y k n b) k b := by
  apply DHoare_scale_k; apply DHoare_weaken; apply DHoare_conseq
  apply DHoare_Zset_map
  intro y _ hy; subst hy
  apply ZSB_map; tauto
  apply h; simp

lemma DHoare_ZSB_filter {p: A → Prop} [DecidablePred p] {x: stream Z[A]} {k b}
  (h: ZSB x k n b):
    DHoare n (c₁ (filter p)) x
      (fun y _ => ZSB y k n b) k b := by
  apply DHoare_scale_k; apply DHoare_weaken; apply DHoare_conseq
  apply DHoare_Zset_filter
  intro y _ hy; subst hy
  apply ZSB_filter; tauto
  apply h; simp

lemma DHoare_ZSB_H {x1 x2: stream Z[A]} {k1 b1 k2 b2}
  (h1: ZSB x1 k1 n b1) (h2: ZSB x2 k2 n b2):
    DHoare n (c₂ (Zset_H)) (sprod (x1, x2))
      (fun y _ => ZSB y (max k1 k2) n (b1 + b2))
      (max k1 k2) (b1 + b2) := by
  apply DHoare_scale_k; apply DHoare_weaken; apply DHoare_conseq
  apply DHoare_Zset_H
  intro y _ hy; subst hy
  apply ZSB_H <;> tauto
  simp; apply Dom_add_Dom <;> tauto
  simp

lemma DHoare_ZSB_join {π1 : A → C} {π2 : B → C}
  {x1: stream Z[A]} {x2: stream Z[B]} {k1 b1 k2 b2}
  (h1: ZSB x1 k1 n b1) (h2: ZSB x2 k2 n b2):
    DHoare n (c₂ (Zset_join π1 π2)) (sprod (x1, x2))
      (fun y _ => ZSB y (k1 * k2) n (fun i => b1 i * b2 i))
      (k1 * k2) (fun i => b1 i * b2 i) := by
  apply DHoare_scale_k; apply DHoare_weaken; apply DHoare_conseq
  apply DHoare_Zset_join
  intro y _ hy; subst hy
  apply ZSB_join <;> tauto
  simp; apply Dom_mul_Dom <;> tauto
  simp

lemma Zset_size_delay (x: stream Z[A]):
    ↑↑Zset.size (z⁻¹ x) = z⁻¹ (↑↑Zset.size x) := by
  funext n; rcases n <;> simp

theorem DHoare_ZSB_delay {x: stream Z[A]} {k d b}
  (h: ZSB x k n b) (hb: DelayDom d b):
    DHoare n (@Ckt.delay 0 [Z[A]]v) x
      (fun y _ => ZSB y (d * k) n b) k b := by
  apply DHoare_scale_k; apply DHoare_weaken; apply DHoare_conseq
  apply DHoare_delay
  intro y _ hy; subst hy
  unfold ZSB; rw [Zset_size_delay]
  apply dom_DelayDom <;> tauto
  apply h; simp

lemma ZSB_integral {x: stream Z[A]} {k b}
  (h: ZSB x k n b):
    ZSB (I x) k n (I b) := by
  have: I b = fun x => sumVals b x.succ := by
    funext n; rw [integral_sumVals]
  rw [this]
  induction n
  · simp [ZSB]; intro m hm
    have : m = 0 := by omega
    subst this; simp
    apply h; simp
  · rename_i i n ih
    specialize ih (by intro m hm; apply h; omega)
    simp [ZSB] at *; intro m hm
    by_cases m ≤ n
    · apply ih ; tauto
    have: m = n + 1 := by omega
    subst this; simp [integral_sumVals]
    specialize ih n (by rfl); simp [integral_sumVals] at ih
    apply le_trans; apply Zset_size_add
    simp; rw [mul_add]
    apply add_le_add
    apply h; simp; apply ih

theorem DHoare_ZSB_I {x: stream Z[A]} {k b} (h: ZSB x k n b):
    DHoare n (@cI false [Z[A]]v) x
      (fun y _ => ZSB y k n (I b)) (3 * k) (I b) := by
  apply DHoare_scale_k; apply DHoare_weaken; apply DHoare_conseq
  apply DHoare_Zset_I
  · intro y _ hy; subst hy
    apply ZSB_integral; tauto
  · rw [Zset_size_delay]
    have hI := ZSB_integral h
    unfold ZSB at hI
    have hzI := dom_DelayDom hI (by apply DelayDom_integral_N)
    simp at hzI
    have hx := Dom_integral h
    have h1 := Dom_add_Dom (Dom_add_Dom hx hzI) hI
    simp at h1
    have h2 : I b + I b + I b <[3, n] I b := by
      intro i hi; simp; omega
    apply Dom_trans <;> tauto
  · omega

theorem DHoare_ZSB_D {x: stream Z[A]} {k b d}
  (h: ZSB x k n b) (hb: DelayDom d b):
    DHoare n (@cD false [Z[A]]v) x
      (fun y _ => ZSB y ((1+d)*k) n b) ((2+d)*k) b := by
  apply DHoare_scale_k; apply DHoare_weaken; apply DHoare_conseq
  apply DHoare_Zset_D
  · intro y _ hy; subst hy
    simp [D, add_mul]
    intro m hm; simp [-Zset.size]
    apply le_trans (by apply Zset_size_sub)
    revert m; apply Dom_add_same_bound; apply h
    conv_lhs => change ↑↑Zset.size (z⁻¹ x)
    rw [Zset_size_delay]; apply dom_DelayDom h hb
  · rw [Zset_size_delay];
    apply Dom_add_same_bound; apply Dom_add_same_bound <;> tauto
    apply dom_DelayDom h hb
  · simp [add_mul]; omega

-- Lemmas about stream_id_distinct
omit [DecidableEq B] in
lemma DHoare_sid_I {x: stream Z[A]} {k b} {π: A → B}
  (hs: ZSB x k n b) (hd: stream_id_distinct π x):
    DHoare n (@cI false [Z[A]]v) x
      (fun y _ => ZSB y k n (I b) ∧ stream_id_distinct π y)
      (3 * k) (I b) := by
  apply DHoare_conj_ncausal
  · apply DHoare_ZSB_I; tauto
  · cons_value DHoare_Zset_I
    apply integral_id_distinct; tauto

omit [DecidableEq B] in
lemma DHoare_sid_delay {x: stream Z[A]} {k d b} {π: A → B}
  (h: ZSB x k n b) (hb: DelayDom d b)
  (hd: stream_id_distinct π x):
    DHoare n (@Ckt.delay 0 [Z[A]]v) x
      (fun y _ => ZSB y (d * k) n b ∧ stream_id_distinct π y)
      k b := by
  apply DHoare_conj_ncausal
  · apply DHoare_ZSB_delay <;> tauto
  · cons_value DHoare_delay
    apply delay_id_distinct; tauto

omit [DecidableEq B] in
lemma DHoare_sid_filter {p: A → Prop} [DecidablePred p]
  {x: stream Z[A]} {k b} {π: A → B}
  (h: ZSB x k n b) (hd: stream_id_distinct π x):
    DHoare n (c₁ (filter p)) x
      (fun y _ => ZSB y k n b ∧ stream_id_distinct π y)
      k b := by
  apply DHoare_conj_ncausal
  · apply DHoare_ZSB_filter; tauto
  · cons_value DHoare_Zset_filter
    apply lifting_filter_id_distinct; tauto

omit [DecidableEq C] in
lemma DHoare_sid_map
  {x: stream Z[A]} {k b} {f: A → B} {g: B → C}
  (h: ZSB x k n b) (hd: stream_id_distinct (g ∘ f) x):
    DHoare n (c₁ (Zset.map f)) x
      (fun y _ => ZSB y k n b ∧ stream_id_distinct g y)
      k b := by
  apply DHoare_conj_ncausal
  · apply DHoare_ZSB_map; tauto
  · cons_value DHoare_Zset_map
    apply lifting_map_id_distinct; tauto

lemma DHoare_sid_join {π1 : A → C} {π2 : B → C}
  {x1: stream Z[A]} {x2: stream Z[B]} {k1 b1 k2 b2}
  (h1: ZSB x1 k1 n b1) (h2: ZSB x2 k2 n b2)
  (h1d: stream_id_distinct π1 x1) (h2d: stream_id_distinct π2 x2):
    DHoare n (c₂ (Zset_join π1 π2)) (sprod (x1, x2))
      (fun y _ => ZSB y 1 n (fun i => min (k1 * b1 i) (k2 * b2 i)))
      (k1 * k2) (fun i => b1 i * b2 i) := by
  cons_apply DHoare_conj
  case hy =>
    rintro _ _ ⟨hq1, hq2⟩; apply hq2
  · apply DHoare_ZSB_join <;> tauto
  · cons_value DHoare_Zset_join
    intro m hm; simp only [lifting, Zset.size, Zset_join]
    trans; apply equiJoin_id_distinct_size
    · apply stream_id_distinct_to_id_distinct; tauto
    · apply stream_id_distinct_to_id_distinct; tauto
    simp; constructor <;> tauto

lemma DHoare_sid_join_l {π1 : A → C} {π2 : B → C}
  {x1: stream Z[A]} {x2: stream Z[B]} {k1 b1 k2 b2}
  (h1: ZSB x1 k1 n b1) (h2: ZSB x2 k2 n b2)
  (h1d: stream_id_distinct π1 x1) (h2d: stream_id_distinct π2 x2):
    DHoare n (c₂ (Zset_join π1 π2)) (sprod (x1, x2))
      (fun y _ => ZSB y k1 n b1)
      (k1 * k2) (fun i => b1 i * b2 i) := by
  cons_apply DHoare_sid_join <;> try tauto
  simp [ZSB]; intro y hy
  intro m hm
  trans; apply hy
  tauto; simp

lemma DHoare_sid_join_r {π1 : A → C} {π2 : B → C}
  {x1: stream Z[A]} {x2: stream Z[B]} {k1 b1 k2 b2}
  (h1: ZSB x1 k1 n b1) (h2: ZSB x2 k2 n b2)
  (h1d: stream_id_distinct π1 x1) (h2d: stream_id_distinct π2 x2):
    DHoare n (c₂ (Zset_join π1 π2)) (sprod (x1, x2))
      (fun y _ => ZSB y k2 n b2)
      (k1 * k2) (fun i => b1 i * b2 i) := by
  cons_apply DHoare_sid_join <;> try tauto
  simp [ZSB]; intro y hy
  intro m hm
  trans; apply hy
  tauto; simp

end ZsetCkt

-- ZsetCkt Notation
notation "zdistinct" => c₁ Zset.distinct
notation "zmap" f:max => c₁ (Zset.map f)
notation "zfilter" p:max => c₁ (filter p)
notation "zprod" => c₂ Zset_product
notation "zjoin" π1:max π2:max => c₂ (Zset_join π1 π2)
notation "zH" => c₂ Zset_H

namespace ZsetCktExamples

--- unoptimized incremental circuit
def ckt1 : Ckt false ([Z[ℤ×ℤ×ℤ]]v ×ᵥ [Z[ℤ×ℤ×ℤ]]v) ([Z[ℤ×ℤ]]v) :=
  (c1st >>c cI >>c zfilter (fun x => x.1 > 2) >>c zmap (fun x => x.2) &&c
    c2nd >>c cI >>c zfilter (fun x => x.1 > 5) >>c zmap (fun x => x.2)) >>c
  zjoin (fun x => x.2) (fun x => x.1) >>c
  zmap (fun (t1, t2) => (t1.1, t2.1)) >>c zdistinct >>c
  cD

@[simp]
lemma I1_simp:
  I (fun _ => 1) = fun i => i.succ := by
  funext b2; simp [integral_sumVals]; induction b2 <;> simp
  rename_i ih; rw [ih]; omega

theorem ckt1_DHoare {n k1 k2: ℕ} {x1 x2} {b1 b2: stream ℕ}
  (h1: ZSB x1 k1 n b1) (h2: ZSB x2 k2 n b2):
    DHoare n ckt1 (sprod (x1, x2))
      (fun y _ => ZSB y (2 * (k1 * k2)) n (fun i ↦ I b1 i * I b2 i))
      (4 * max (9 * max k1 k2) (3 * (k1 * k2)))
      (fun i => (I b1 i + 1) * (I b2 i + 1)) := by
  unfold ckt1; apply DHoare_conseq; Dweaken
  repeat (apply DHoare_seq_ncausal)
  wapply DHoare_par_ncausal
  · repeat (apply DHoare_seq_ncausal)
    apply DHoare_fst
    seq_intro
    apply DHoare_ZSB_I; tauto
    seq_intro
    apply DHoare_ZSB_filter; tauto
    seq_intro
    apply DHoare_ZSB_map; tauto
  · repeat (apply DHoare_seq_ncausal)
    apply DHoare_snd
    seq_intro
    apply DHoare_ZSB_I; tauto
    seq_intro
    apply DHoare_ZSB_filter; tauto
    seq_intro
    apply DHoare_ZSB_map; tauto
  · simp; apply Dom_absorb_k
    apply le_Dom; intro i; simp
    le_refine 3 * (I b1 i + I b2 i)
  · simp; le_refine 9 * (max k1 k2)
  par_intro; apply DHoare_ZSB_join <;> tauto
  seq_intro; apply DHoare_ZSB_map; tauto
  seq_intro; apply DHoare_ZSB_distinct; tauto
  seq_intro; apply DHoare_ZSB_D; tauto
  · apply DelayDom_mono
    apply Monotone.mul' <;> apply mono_integral
  · apply Dom_absorb_k (k:=4)
    intro i _; simp; nlinarith
  · trans; simp
    rewrite [max_eq_right (a:= k1 * k2)]; rfl
    omega; rfl
  · simp

theorem ckt1_DHoare_tight {n k1 k2: ℕ} {x1 x2} {s1 s2: stream ℕ}
  (h1: ZSB x1 k1 n s1) (h2: ZSB x2 k2 n s2):
    DHoare n ckt1 (sprod (x1, x2))
      (fun y _ => ZSB y (2 * (k1 * k2)) n (fun i ↦ I s1 i * I s2 i)) 1
      (fun i => (5 * k1) * I s1 i + (5 * k2) * I s2 i +
        (6 * (k1 * k2)) * I s1 i * I s2 i) := by
  unfold ckt1; apply DHoare_conseq
  repeat (apply DHoare_seq_ncausal_tight)
  apply DHoare_par_ncausal_tight
  · repeat (apply DHoare_seq_ncausal_tight)
    apply DHoare_fst
    seq_intro
    apply DHoare_ZSB_I; tauto
    · intros; apply Dom_add_zero_l <;> tauto
    seq_intro
    apply DHoare_ZSB_filter; tauto
    · intros; apply Dom_scale_k (4 * k1)
      apply Dom_add_same_bound <;> tauto
      omega
    seq_intro
    apply DHoare_ZSB_map; tauto
    · intros; apply Dom_scale_k (5 * k1)
      apply Dom_add_same_bound <;> tauto
      omega
  · repeat (apply DHoare_seq_ncausal_tight)
    apply DHoare_snd
    seq_intro
    apply DHoare_ZSB_I; tauto
    · intros; apply Dom_add_zero_l <;> tauto
    seq_intro
    apply DHoare_ZSB_filter; tauto
    · intros; apply Dom_scale_k (4 * k2)
      apply Dom_add_same_bound <;> tauto
      omega
    seq_intro
    apply DHoare_ZSB_map; tauto
    · intros; apply Dom_scale_k (5 * k2)
      apply Dom_add_same_bound <;> tauto
      omega
  · intros x1 x2 hx1 hx2
    apply Dom_release_k at hx1; apply Dom_release_k at hx2
    apply Dom_add_Dom <;> tauto
  par_intro; apply DHoare_ZSB_join <;> tauto
  · intro x1 x2 hx1 hx2
    apply Dom_release_k at hx2
    simp at hx1 hx2
    apply Dom_add_Dom <;> tauto
  seq_intro; apply DHoare_ZSB_map; tauto
  · intro x1 x2 hx1 hx2
    apply Dom_release_k at hx2
    simp at hx1 hx2
    apply Dom_le_weaken
    apply Dom_add_Dom <;> tauto
    rewrite [add_assoc, <- add_smul, <- two_mul]; rfl
  seq_intro; apply DHoare_ZSB_distinct; tauto
  · intro x1 x2 hx1 hx2
    apply Dom_release_k at hx2
    simp at hx1 hx2
    apply Dom_le_weaken
    apply Dom_add_Dom <;> tauto
    rewrite [add_assoc, <- add_smul, <- add_one_mul]
    simp; rfl
  seq_intro; apply DHoare_ZSB_D; tauto
  · apply DelayDom_mono
    apply Monotone.mul' <;> apply mono_integral
  · intro x1 x2 hx1 hx2
    apply Dom_release_k at hx2
    simp at hx1 hx2
    apply Dom_le_weaken; apply Dom_scale_k
    apply Dom_add_Dom <;> tauto
    simp
    intro i; simp; nlinarith
  simp

theorem ckt1_DHoare_1 {n k1 k2: ℕ} {x1 x2}
  (h1: ZSB x1 k1 n (fun _ => 1)) (h2: ZSB x2 k2 n (fun _ => 1)):
    DHoare n ckt1 (sprod (x1, x2))
      (fun y _ => ZSB y (2 * (k1 * k2)) n (fun i ↦ (i + 1) * (i + 1)))
      (4 * max (9 * max k1 k2) (3 * (k1 * k2)))
      (fun i => (i+2) * (i+2)) := by
  apply DHoare_conseq; wapply ckt1_DHoare
  apply h1; apply h2
  simp; apply le_Dom; simp
  simp; simp

--- optimized incremental circuit
def opt_join: Ckt false ([Z[ℤ×ℤ]]v ×ᵥ [Z[ℤ×ℤ]]v) ([Z[(ℤ×ℤ)×(ℤ×ℤ)]]v) :=
   letI j := zjoin (fun x => x.2) (fun x => x.1);
  ((c1st >>c cI &&c c2nd) >>c j
    &&c
    (c1st &&c c2nd >>c cI >>c cz⁻¹) >>c j)
  >>c cadd

def opt_distinct: Ckt false ([Z[ℤ×ℤ]]v) ([Z[ℤ×ℤ]]v) :=
  (cI >>c cz⁻¹ &&c cid) >>c zH

def ckt2 : Ckt false ([Z[ℤ×ℤ×ℤ]]v ×ᵥ [Z[ℤ×ℤ×ℤ]]v) ([Z[ℤ×ℤ]]v) :=
  (c1st >>c zfilter (fun x:ℤ×ℤ×ℤ => x.1 > 2) >>c zmap (fun x:ℤ×ℤ×ℤ => x.2) &&c
    c2nd >>c zfilter (fun x: ℤ×ℤ×ℤ => x.1 > 5) >>c zmap (fun x:ℤ×ℤ×ℤ => x.2)) >>c
  opt_join >>c
  zmap (fun (t1, t2) => (t1.1, t2.1)) >>c
  opt_distinct

lemma DHoare_ZSB_opt_join {n k1 k2: ℕ} {x1 x2} {s1 s2}
  (h1s: ZSB x1 k1 n s1) (h2s: ZSB x2 k2 n s2)
  (h1d: stream_id_distinct Prod.snd x1)
  (h2d: stream_id_distinct Prod.fst x2):
    DHoare n opt_join (sprod (x1, x2))
      (fun y _ => ZSB y (max k1 k2) n (s1 + s2))
      (max (max (3 * k1) (k1 * k2)) (max 6 k1 * k2))
      (fun i => (I s1 i + 1) * (s2 i + 1) + (s1 i + 1) * (I s2 i + 1)) := by
  unfold opt_join; apply DHoare_conseq
  wapply DHoare_seq_ncausal
  wapply DHoare_par_ncausal
  · wapply DHoare_seq_ncausal
    wapply DHoare_par_ncausal
    · wapply DHoare_seq_ncausal
      apply DHoare_fst
      seq_intro
      apply DHoare_sid_I <;> tauto
      · simp; apply Dom_rfl
      · simp; rfl
    · apply DHoare_snd
    · simp; apply Dom_rfl
    · simp; rfl
    par_intro; rename_i hy2
    simp at hy2; subst hy2
    apply DHoare_sid_join_r <;> tauto
    · simp; apply Dom_rfl
    · rfl
  · wapply DHoare_seq_ncausal
    wapply DHoare_par_ncausal
    · apply DHoare_fst
    · repeat wapply DHoare_seq_ncausal
      apply DHoare_snd
      seq_intro
      apply DHoare_sid_I <;> tauto
      · simp; apply Dom_rfl
      · simp; rfl
      seq_intro
      rename_i hy; rcases hy with ⟨hy ,hd⟩
      apply DHoare_sid_delay hy _ hd; exact 1
      · apply DelayDom_integral_N
      · apply Dom_add_same
      · rfl
    · simp; apply Dom_rfl
    · simp; rfl
    par_intro; rename_i hy1 _
    simp at hy1; subst hy1
    apply DHoare_sid_join_l <;> tauto
    · simp; apply Dom_rfl
    · rewrite [max_eq_left (b:=k2)]; swap; omega
      rewrite [<- mul_assoc]; simp; rfl
  · apply le_Dom; intro i; simp
    le_refine (I s1 i * (s2 i + 1) + (s1 i + 1) * I s2 i)
    nlinarith
  · simp_rw [one_mul]; rfl
  par_intro
  apply DHoare_ZSB_add <;> tauto
  · apply le_Dom; intro i; simp
    nlinarith
  · nth_rewrite 1 [max_eq_left]; omega
    apply max_le
    · trans; swap
      apply le_max_right
      trans; le_refine 6 * k2
      gcongr; omega
    · omega
  simp [ZSB]; intro y hy
  rw [max_comm, add_comm] at hy
  tauto

lemma DHoare_opt_distinct {n k: ℕ} {x s}
  (h1: ZSB x k n s):
    DHoare n opt_distinct x
      (fun y _ => ZSB y k n (I s + s))
      (12 * k) (I s + s) := by
  unfold opt_distinct; apply DHoare_conseq
  wapply DHoare_seq_ncausal
  wapply DHoare_par_ncausal
  · wapply DHoare_seq_ncausal
    apply DHoare_ZSB_I; tauto
    seq_intro
    apply DHoare_ZSB_delay <;> try tauto
    · apply DelayDom_integral_N
    · simp; apply Dom_add_same
    · rewrite [max_eq_left]
      le_refine 6 * k
      omega
  · apply DHoare_id
  · simp; apply Dom_rfl
  · simp; rfl
  par_intro
  rename_i _ _ hy1 hy2; simp at hy1 hy2; subst hy2
  apply DHoare_ZSB_H <;> tauto
  · apply Dom_add_same_bound
    apply le_Dom; intro _; simp
    apply le_Dom; intro _; simp
  · omega
  simp

theorem ckt2_DHoare {n k1 k2: ℕ} {x1 x2} {s1 s2}
  (h1s: ZSB x1 k1 n s1) (h2s: ZSB x2 k2 n s2)
  (h1d: stream_id_distinct (fun x => x.2.2) x1)
  (h2d: stream_id_distinct (fun x => x.2.1) x2):
    DHoare n ckt2 (sprod (x1, x2))
      (fun y _ => ZSB y (max k1 k2) n (I (s1 + s2) + (s1 + s2)))
      (8 * max (3 * k1) (max 6 k1 * k2))
      (fun i => (I s1 i + 1) * (s2 i + 1) + (s1 i + 1) * (I s2 i + 1)) := by
  unfold ckt2
  repeat (wapply DHoare_seq_ncausal)
  wapply DHoare_par_ncausal
  · repeat (wapply DHoare_seq_ncausal)
    apply DHoare_fst
    seq_intro
    apply DHoare_sid_filter <;> tauto
    · simp; apply Dom_rfl
    · simp; rfl
    rintro y ⟨hys, hyd⟩
    have: (fun x:ℤ×ℤ×ℤ => x.2.2) = Prod.snd ∘ Prod.snd := by
      funext; simp
    rewrite [this] at hyd
    apply DHoare_sid_map <;> tauto
    · apply Dom_add_same
    · simp; rfl
  · repeat (wapply DHoare_seq_ncausal)
    apply DHoare_snd
    seq_intro
    apply DHoare_sid_filter <;> tauto
    · simp; apply Dom_rfl
    · simp; rfl
    rintro y ⟨hys, hyd⟩
    have: (fun x:ℤ×ℤ×ℤ => x.2.1) = Prod.fst ∘ Prod.snd := by
      funext; simp
    rewrite [this] at hyd
    apply DHoare_sid_map <;> tauto
    · apply Dom_add_same
    · simp; rfl
  · apply Dom_rfl
  · simp; rfl
  par_intro
  apply DHoare_ZSB_opt_join <;> tauto
  · rw [add_comm]
    apply Dom_add_ignore
    apply le_Dom; intro i; simp; nlinarith
  · simp
    rewrite [max_eq_right]; rfl
    rw [mul_max]
    apply max_le; omega
    trans; swap
    apply le_max_right
    trans; le_refine 6 * k2
    gcongr; omega
  seq_intro; apply DHoare_ZSB_map; tauto
  · apply Dom_add_ignore
    apply le_Dom; intro i; simp; nlinarith
  · rewrite [max_eq_left]; simp; rfl
    apply max_le; omega
    nth_rw 1 [<- one_mul k2]
    gcongr; omega
    trans; swap
    apply le_max_right
    trans; le_refine 6 * k2
    gcongr; omega
  seq_intro; apply DHoare_opt_distinct; tauto
  · apply Dom_add_ignore
    apply le_Dom; intro i; simp
    rw [integral_linear]; simp; nlinarith
  · have: 8 = 2 * 4 := by omega
    rw [this]; rw [mul_assoc]
    apply mul_le_mul; omega
    apply max_le <;> try omega
    simp_rw [mul_max]
    apply max_le; omega
    trans; swap; apply le_max_right
    rw [<- mul_assoc, mul_max]
    gcongr
    all_goals simp

theorem ckt2_DHoare_1 {n k1 k2: ℕ} {x1 x2}
  (h1s: ZSB x1 k1 n (fun _ => 1)) (h2s: ZSB x2 k2 n (fun _ => 1))
  (h1d: stream_id_distinct (fun x => x.2.2) x1)
  (h2d: stream_id_distinct (fun x => x.2.1) x2):
    DHoare n ckt2 (sprod (x1, x2))
      (fun y _ => ZSB y (2 * max k1 k2) n (fun i => i + 2))
      (32 * max (3 * k1) (max 6 k1 * k2))
      (fun i => i + 2) := by
  apply DHoare_conseq; wapply ckt2_DHoare
  apply h1s; apply h2s
  apply h1d; apply h2d
  case h.h.k2 => exact 4
  simp; intro i _; simp
  nlinarith
  omega
  intro y _
  rw [integral_linear]; simp [ZSB]
  intro h i hi; specialize h i hi
  simp at h; simp
  linarith

end ZsetCktExamples

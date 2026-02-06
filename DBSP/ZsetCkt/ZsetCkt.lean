-- consider splitting the ZsetCkt definition part and the resource anlysis part
import DBSP.Circuits.Circuits
import DBSP.ZSets.Zset
import DBSP.ZSets.Relational
import DBSP.ZSets.RelationalIncremental
import DBSP.Practical.Incrementalize
import DBSP.Practical.Sequiv
open CktBasic

section ZsetCkt
variable {A B C: Type} [DecidableEq A] [DecidableEq B] [DecidableEq C]

-- We are conceptually doing a rough asymptotic analysis
-- so we ignore constant factors like the type of elments in a Zset
-- and only consider the size of the Zset
-- Therefore the result should be regarded in the form of O(size)
@[simp]
instance ZsetBaseType: BaseType (Z[A]) where
  has_group := by infer_instance
  size := fun x => Zset.size x
  add_cost := fun (x, y) => x.size + y.size
  sub_cost := fun (x, y) => x.size + y.size

@[simp]
def DistinctUnaryNode: UnaryNode Z[A] Z[A] := {
  f := @Zset.distinct A _
  cost := fun x => x.size
}

@[simp]
def MapUnaryNode (f: A -> B): UnaryNode Z[A] Z[B] := {
  f := Zset.map f
  cost := fun x => x.size
}

@[simp]
def FilterUnaryNode (p: A -> Prop) [DecidablePred p]: UnaryNode Z[A] Z[A] := {
  f := filter p
  cost := fun x => x.size
}

@[simp]
def HBinaryNode: BinaryNode Z[A] Z[A] Z[A] := {
  f := fun x => distinctH x.1 x.2
  cost := fun x => x.fst.size + x.snd.size
}

@[simp]
def ProductBinaryNode: BinaryNode Z[A] Z[B] Z[A × B] := {
  f := fun x => product x.1 x.2
  cost := fun x => x.fst.size * x.snd.size
}

@[simp]
def EquiJoinBinaryNode {A B C: Type}
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  (π1 : A → C) (π2 : B → C):
    BinaryNode Z[A] Z[B] Z[A × B] := {
  f := fun x => equiJoin π1 π2 x.1 x.2
  cost := fun x => x.fst.size * x.snd.size
}

-- incrementalizable instances and theorems
instance (f: A -> B): IncUnary (@MapUnaryNode A B _ _ f) := by
  apply IncUnaryLinear
  intro x y; simp [MapUnaryNode]
  apply Zset.map_linear

instance (p: A -> Prop) [DecidablePred p]: IncUnary (@FilterUnaryNode A _ p _) := by
  apply IncUnaryLinear
  intro x y; simp [FilterUnaryNode]
  apply filter_linear

instance : IncBinary (@ProductBinaryNode A B _ _) := by
  apply IncBinaryBilinear
  intro x y; simp [ProductBinaryNode]
  apply product_bilinear.1
  apply product_bilinear.2

instance (π1 : A → C) (π2 : B → C):
    IncBinary (@EquiJoinBinaryNode A B C _ _ _ π1 π2) := by
  apply IncBinaryBilinear
  intro x y; simp [EquiJoinBinaryNode]
  apply (equiJoin_bilinear _ _).1
  apply (equiJoin_bilinear _ _).2

def incr_dist {ns: Bool}: Ckt [Z[A]]v [Z[A]]v ns :=
  (cI >>c cz⁻¹ &&c cid) >>c (c₂ HBinaryNode)

lemma Sequiv_incr_dist {ns: Bool}:
    cΔ (c₁ (DistinctUnaryNode (A:=A))) ≃ incr_dist (ns:=ns) := by
  constructor; swap
  · simp [Terminate, cΔ, incr_dist]
  simp [denote, incr_dist]
  funext x; simp
  rcases ns
  · funext i; simp [incremental, D]
    ext a; rcases i <;> simp [distinctHAt]
    omega
  · funext i j; simp [incremental, D]
    ext a; rcases i <;> simp [distinctHAt]
    omega

lemma Preserve1_incr_dist {ns: Bool}:
    (c₁ (DistinctUnaryNode (A:=A))) ↝₁ incr_dist (ns:=ns) := by
  intro x n _ h
  simp [IntFP1, ExtFP1] at h
  rcases h with ⟨hx, _⟩
  have hx' := FixedAfter1_mono (n2:=n+1) hx (by simp)
  have hdx := ZeroAfter_succ_D_FixedAfter1.2 hx
  have hdx' := ZeroAfter_impl_FixedAfter1 hdx
  have hzx := FixedAfter1_delay_succ.2 hx
  have Hin := FixedAfter1_sprodO.2 ⟨hzx, hdx'⟩
  have Hout := FixedAfter1_liftO (f:= fun x => distinctH x.1 x.2) Hin
  simp [incr_dist, IntFP1, denote, ExtFP1, *, liftO_id]
  apply I_IntFP1; rcases ns <;> simp [hx]

lemma Presreve2_incr_dist:
    (c₁ (DistinctUnaryNode (A:=A))) ↝₂ incr_dist := by
  intro x r _ h
  simp [IntFP2Vec, IntFP2, ExtFP2] at h
  rw [forall_and_iff] at h; rcases h with ⟨hx, _⟩
  rw [<- FixedAfter2Vec] at hx
  set r' := fun i ↦ max (r i) (z⁻¹ r i)
  have hdx := FixedAfter2Vec_D hx
  have hzx := FixedAfter2Vec_delay.1 hx
  have hzx' := FixedAfter2Vec_mono hzx (b2:= r') (by intro _; simp [r'])
  have Hin := FixedAfter2Vec_sprod2.2 ⟨hzx', hdx⟩
  have Hout := FixedAfter2Vec_lifting (f:= fun x => distinctH x.1 x.2) Hin
  intro i; unfold r' at *
  have := hx i
  specialize hdx i
  specialize hzx' i
  specialize Hin i
  specialize Hout i
  simp at *
  simp [incr_dist, IntFP2, ExtFP2, denote, *]
  constructor
  apply I_IntFP2Vec; tauto
  apply FixedAfter2_mono; tauto; simp

instance : IncUnary (@DistinctUnaryNode A _) where
  opt := incr_dist
  sequiv := by intro _; apply Sequiv_incr_dist
  preserve1 := by intro _; apply Preserve1_incr_dist
  preserve2 := Presreve2_incr_dist

-- H can use the default unoptimized instance

-- Helper functions for backward compatibility
@[simp]
def Zset_H (x: Z[A] × Z[A]): Z[A] := distinctH x.1 x.2

@[simp]
def Zset_product (x: Z[A] × Z[B]): Z[A × B] := product x.1 x.2

@[simp]
def Zset_join (π1 : A → C) (π2 : B → C) (x: Z[A] × Z[B]): Z[A × B] :=
  equiJoin π1 π2 x.1 x.2

-- TODO: intersection

--- Zset.size Lemmas
lemma Zset_size_add (x1 x2: Z[A]):
    Zset.size (x1 + x2) ≤ Zset.size x1 + Zset.size x2 := by
  simp [Zset.size]; rw [Zset.add_support]
  apply le_trans
  · apply Finset.card_filter_le
  · apply le_trans
    · apply Finset.card_union_le
    · rfl

lemma Zset_size_sub (x1 x2: Z[A]):
    Zset.size (x1 - x2) ≤ Zset.size x1 + Zset.size x2 := by
  simp [Zset.size]; rw [Zset.sub_support]
  apply le_trans
  · apply Finset.card_filter_le
  · apply le_trans
    · apply Finset.card_union_le
    · rfl

lemma Zset_size_distinct (x: Z[A]):
    Zset.size (Zset.distinct x) ≤ Zset.size x := by
  simp [Zset.size]; rw [Zset.distinct_support]
  apply le_trans; apply Finset.card_filter_le; rfl

lemma Zset_size_map (f: A → B) (x: Z[A]):
    Zset.size (Zset.map f x) ≤ Zset.size x := by
  simp [Zset.size]; apply le_trans
  apply Finset.card_le_card; apply Zset.map_support_image
  apply le_trans; apply Finset.card_image_le; tauto

lemma Zset_size_filter (p: A → Prop) [DecidablePred p] (x: Z[A]):
    Zset.size (filter p x) ≤ Zset.size x := by
  simp [Zset.size]; rw [filter_support]
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
  simp [Zset.size]; rw [product_support]; simp

lemma Zset_size_join (π1 : A → C) (π2 : B → C) (x1: Z[A]) (x2: Z[B]):
    Zset.size (Zset_join π1 π2 (x1, x2)) ≤ Zset.size x1 * Zset.size x2 := by
  simp [Zset.size]; unfold equiJoin
  rw [filter_support, product_support]; simp
  apply le_trans; apply Finset.card_filter_le; simp

end ZsetCkt

-- ZsetCkt Notation
notation "zdistinct" => c₁ DistinctUnaryNode
notation "zmap" f:max => c₁ (MapUnaryNode f)
notation "zfilter" p:max => c₁ (FilterUnaryNode p)
notation "zprod" => c₂ ProductBinaryNode
notation "zjoin" π1:max π2:max => c₂ (EquiJoinBinaryNode π1 π2)
notation "zH" => c₂ HBinaryNode

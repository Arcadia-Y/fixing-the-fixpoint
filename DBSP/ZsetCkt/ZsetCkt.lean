-- consider splitting the ZsetCkt definition part and the resource anlysis part
import DBSP.Circuits.Circuits
import DBSP.ZSets.Zset
import DBSP.ZSets.Relational
import DBSP.ZSets.RelationalIncremental
open CktBasic

section ZsetCkt
variable {A B C: Type} [DecidableEq A] [DecidableEq B] [DecidableEq C]

-- We are conceptually doing a rough asymptotic analysis
-- so we ignore constant factors like the type of elments in a Zset
-- and only consider the size of the Zset
-- Therefore the result should be regarded in the form of O(size)
instance ZsetBaseType: BaseType (Z[A]) where
  has_group := by infer_instance
  size := fun x => Zset.size x
  add_cost := fun (x, y) => x.size + y.size
  sub_cost := fun (x, y) => x.size + y.size

def DistinctUnaryNode: UnaryNode Z[A] Z[A] := {
  f := @Zset.distinct A _
  cost := fun x => x.size
}

def MapUnaryNode (f: A -> B): UnaryNode Z[A] Z[B] := {
  f := Zset.map f
  cost := fun x => x.size
}

def FilterUnaryNode (p: A -> Prop) [DecidablePred p]: UnaryNode Z[A] Z[A] := {
  f := filter p
  cost := fun x => x.size
}

def HBinaryNode: BinaryNode Z[A] Z[A] Z[A] := {
  f := fun x => distinctH x.1 x.2
  cost := fun x => x.fst.size + x.snd.size
}

def ProductBinaryNode: BinaryNode Z[A] Z[B] Z[A × B] := {
  f := fun x => product x.1 x.2
  cost := fun x => x.fst.size * x.snd.size
}

def EquiJoinBinaryNode (π1 : A → C) (π2 : B → C): BinaryNode Z[A] Z[B] Z[A × B] := {
  f := fun x => equiJoin π1 π2 x.1 x.2
  cost := fun x => x.fst.size * x.snd.size
}

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

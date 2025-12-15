import DBSP.Circuits
import DBSP.ZSets.Zset
import DBSP.ZSets.Relational
import DBSP.ZSets.RelationalIncremental
import DBSP.DHoare
import DBSP.Dominate
open CktBasic

section ZsetCkt
variable {A B C: Type} [DecidableEq A]  [DecidableEq B]  [DecidableEq C]
-- We currently only care about the size of a Zset and ignore its contents
instance ZsetBaseTypeG: BaseTypeG (Z[A]) where
  has_group := by infer_instance
  size := Zset.size
  size_zpp := by rfl
  add_cost := fun (x, y) => x.size + y.size
  sub_cost := fun (x, y) => x.size + y.size
  neg_cost := fun x => x.size

instance DistinctUnaryNode:
    UnaryNode (@Zset.distinct A _) where
  zpp := by rfl
  cost := fun x => x.size

instance MapUnaryNode (f: A -> B):
    UnaryNode (Zset.map f) where
  zpp := by apply Zset.map_zpp
  cost := fun x => x.size

instance FilterUnaryNode (p: A -> Prop) [DecidablePred p]:
    UnaryNode (filter p) where
  zpp := by apply filter_0
  cost := fun x => x.size

@[simp]
def Zset_H (x: Z[A] × Z[A]): Z[A] := distinctH x.1 x.2
instance HBinaryNode:
    BinaryNode (@Zset_H A _) where
  zpp := by rfl
  cost := fun x => x.fst.size + x.snd.size

@[simp]
def Zset_product (x: Z[A] × Z[B]): Z[A × B] := product x.1 x.2
instance ProductBinaryNode:
    BinaryNode (@Zset_product A B _ _) where
  zpp := by simp
  cost := fun x => x.fst.size * x.snd.size

@[simp]
def Zset_join (π1 : A → C) (π2 : B → C) (x: Z[A] × Z[B]): Z[A × B] :=
  equiJoin π1 π2 x.1 x.2
instance EquiJoinBinaryNode (π1 : A → C) (π2 : B → C):
    BinaryNode (Zset_join π1 π2) where
  zpp := by simp
  cost := fun x => x.fst.size * x.snd.size

-- TODO: intersection

--- ZSet operations' SizeBound rules
lemma SizeBound_Zset_add:
    SizeBound (c₂ (@base_add Z[A] _)) (fun x i => (x i).1 + (x i).2) := by
  intros input i_bound hi
  intro t; simp
  simp [denote, base_add, BaseTypeG.size]
  specialize hi t; simp [VType_size, BaseTypeG.size] at hi
  rw [Zset.add_support]
  apply le_trans
  · apply Finset.card_filter_le
  · apply le_trans
    · apply Finset.card_union_le
    · exact Nat.add_le_add hi.1 hi.2

lemma SizeBound_Zset_sub:
    SizeBound (c₂ (@base_sub Z[A] _)) (fun x i => (x i).1 + (x i).2) := by
  intros input i_bound hi
  intro t; simp
  simp [denote, base_sub, BaseTypeG.size]
  specialize hi t; simp [VType_size, BaseTypeG.size] at hi
  rw [Zset.sub_support]
  apply le_trans
  · apply Finset.card_filter_le
  · apply le_trans
    · apply Finset.card_union_le
    · exact Nat.add_le_add hi.1 hi.2

syntax "sb_intro": tactic
macro_rules
  | `(tactic| sb_intro) => `(tactic|
    intros input i_bound hi;
    intro t; simp;
    simp [denote, BaseTypeG.size];
    specialize hi t; simp [VType_size, BaseTypeG.size] at hi
    )

lemma SizeBound_Zset_distinct:
    SizeBound (c₁ (@Zset.distinct A _)) id := by
  sb_intro
  rw [Zset.distinct_support]
  apply le_trans; apply Finset.card_filter_le; tauto

lemma SizeBound_Zset_map (f: A → B):
    SizeBound (c₁ (Zset.map f)) id := by
  sb_intro
  apply le_trans
  apply Finset.card_le_card; apply Zset.map_support_image
  apply le_trans; apply Finset.card_image_le; tauto

lemma SizeBound_Zset_filter (p: A → Prop) [DecidablePred p]:
    SizeBound (c₁ (filter p)) id := by
  sb_intro
  rw [filter_support]
  apply le_trans; apply Finset.card_filter_le; tauto

lemma SizeBound_Zset_H:
    SizeBound (c₂ (@Zset_H A _)) (fun x i => (x i).1 + (x i).2) := by
  sb_intro
  rename_i i ib t ih
  suffices h:
    (DFinsupp.support (distinctH (i t).1 (i t).2)).card ≤
    (DFinsupp.support (i t).1 ∪ DFinsupp.support (i t).2).card by
    apply le_trans h
    apply le_trans; apply Finset.card_union_le
    rcases ih with ⟨h1, h2⟩; simp at h1 h2
    exact Nat.add_le_add h1 h2
  apply Finset.card_le_card
  intro a; simp [distinctH]
  contrapose; simp

lemma SizeBound_Zset_product:
    SizeBound (c₂ (@Zset_product A B _ _)) (fun x i => (x i).1 * (x i).2) := by
  sb_intro
  rw [product_support]; simp
  rename_i hi; rcases hi with ⟨h1, h2⟩; simp at h1 h2
  apply Nat.mul_le_mul <;> tauto

lemma SizeBound_Zset_join (π1 : A → C) (π2 : B → C):
    SizeBound (c₂ (Zset_join π1 π2)) (fun x i => (x i).1 * (x i).2) := by
  sb_intro
  unfold equiJoin
  rw [filter_support, product_support]; simp
  rename_i hi; rcases hi with ⟨h1, h2⟩; simp at h1 h2
  apply le_trans; apply Finset.card_filter_le
  simp; apply Nat.mul_le_mul <;> tauto

--- ZSet operations' CostBound rules
lemma CostBound_Zset_add:
    CostBound (c₂ (@base_add Z[A] _)) (fun x i => (x i).1 + (x i).2) := by
  intros input i_bound hi
  intro t; simp
  simp [cost_f, base_add, BinaryNode.cost]
  specialize hi t; simp [VType_size, BaseTypeG.size] at hi
  rcases hi with ⟨h1, h2⟩; simp at h1 h2
  simp [BaseTypeG.add_cost]
  apply Nat.add_le_add <;> tauto

lemma CostBound_Zset_sub:
    CostBound (c₂ (@base_sub Z[A] _)) (fun x i => (x i).1 + (x i).2) := by
  intros input i_bound hi
  intro t; simp
  simp [cost_f, base_sub, BinaryNode.cost]
  specialize hi t; simp [VType_size, BaseTypeG.size] at hi
  rcases hi with ⟨h1, h2⟩; simp at h1 h2
  simp [BaseTypeG.sub_cost]
  apply Nat.add_le_add <;> tauto

syntax "cb_intro": tactic
macro_rules
  | `(tactic| cb_intro) => `(tactic|
    intros input i_bound hi;
    intro t; simp;
    simp [cost_f, UnaryNode.cost, BinaryNode.cost];
    specialize hi t; simp [VType_size, BaseTypeG.size] at hi;
    try tauto
    )

lemma CostBound_Zset_distinct:
    CostBound (c₁ (@Zset.distinct A _)) id := by cb_intro

lemma CostBound_Zset_map (f: A → B):
    CostBound (c₁ (Zset.map f)) id := by cb_intro

lemma CostBound_Zset_filter (p: A → Prop) [DecidablePred p]:
    CostBound (c₁ (filter p)) id := by cb_intro

lemma CostBound_Zset_product:
    CostBound (c₂ (@Zset_product A B _ _)) (fun x i => (x i).1 * (x i).2) := by
  cb_intro; rename_i hi; rcases hi with ⟨h1, h2⟩; simp at h1 h2
  apply Nat.mul_le_mul <;> tauto

lemma CostBound_Zset_join (π1 : A → C) (π2 : B → C):
    CostBound (c₂ (Zset_join π1 π2)) (fun x i => (x i).1 * (x i).2) := by
  cb_intro; rename_i hi; rcases hi with ⟨h1, h2⟩; simp at h1 h2
  apply Nat.mul_le_mul <;> tauto

lemma CostBound_Zset_H:
    CostBound (c₂ (@Zset_H A _)) (fun x i => (x i).1 + (x i).2) := by
  cb_intro; rename_i hi; rcases hi with ⟨h1, h2⟩; simp at h1 h2
  apply Nat.add_le_add <;> tauto

--- ZSet operations' DHoare rules
theorem DHoare_Zset_add:
    DHoare (c₂ (@base_add Z[A] _)) (fun x i => (x i).1 + (x i).2) (fun x i => (x i).1 + (x i).2) := by
  simp [DHoare]; constructor
  apply SizeBound_Zset_add; apply CostBound_Zset_add

theorem DHoare_Zset_sub:
    DHoare (c₂ (@base_sub Z[A] _)) (fun x i => (x i).1 + (x i).2) (fun x i => (x i).1 + (x i).2) := by
  simp [DHoare]; constructor
  apply SizeBound_Zset_sub; apply CostBound_Zset_sub

theorem DHoare_Zset_distinct:
    DHoare (c₁ (@Zset.distinct A _)) id id := by
  simp [DHoare]; constructor
  apply SizeBound_Zset_distinct; apply CostBound_Zset_distinct

theorem DHoare_Zset_map (f: A → B):
    DHoare (c₁ (Zset.map f)) id id := by
  simp [DHoare]; constructor
  apply SizeBound_Zset_map; apply CostBound_Zset_map

theorem DHoare_Zset_filter (p: A → Prop) [DecidablePred p]:
    DHoare (c₁ (filter p)) id id := by
  simp [DHoare]; constructor
  apply SizeBound_Zset_filter; apply CostBound_Zset_filter

theorem DHoare_Zset_H:
    DHoare (c₂ (@Zset_H A _)) (fun x i => (x i).1 + (x i).2) (fun x i => (x i).1 + (x i).2) := by
  simp [DHoare]; constructor
  apply SizeBound_Zset_H; apply CostBound_Zset_H

theorem DHoare_Zset_product:
    DHoare (c₂ (@Zset_product A B _ _)) (fun x i => (x i).1 * (x i).2) (fun x i => (x i).1 * (x i).2) := by
  simp [DHoare]; constructor
  apply SizeBound_Zset_product; apply CostBound_Zset_product

theorem DHoare_Zset_join (π1 : A → C) (π2 : B → C):
    DHoare (c₂ (Zset_join π1 π2)) (fun x i => (x i).1 * (x i).2) (fun x i => (x i).1 * (x i).2) := by
  simp [DHoare]; constructor
  apply SizeBound_Zset_join; apply CostBound_Zset_join

theorem DHoare_Zset_I:
    DHoare (@cI Z[A] _) (fun x i => sumVals x i.succ) (fun x i => /-x i + sumVals x i +-/ sumVals x i.succ) := by
  -- apply DHoare_weaken
  -- apply DHoare_loop (sb' := fun x i => sumVals x i.succ)
  -- apply DHoare_Zset_add
  -- · intro x; intro t; simp
  --   rw [delay_sumVals]
  -- · simp
  -- · simp; intro x; intro t; simp
  --   rw [delay_sumVals]
  sorry

theorem DHoare_Zset_D:
    DHoare (@cD Z[A] _) (fun x => x) (fun x => x) := by
  apply DHoare_weaken
  simp [cD]; apply DHoare_seq
  apply DHoare_par
  apply DHoare_id; apply DHoare_delay
  apply DHoare_Zset_sub
  · intro x; intro t; simp; sorry
  · intro x; intro t; simp; sorry

end ZsetCkt

-- ZsetCkt Notation
notation "zdistinct" => c₁ Zset.distinct
notation "zmap" f:max => c₁ (Zset.map f)
notation "zfilter" p:max => c₁ (filter p)
notation "zprod" => c₂ Zset_product
notation "zjoin" π1:max π2:max => c₂ (Zset_join π1 π2)
notation "zH" => c₂ Zset_H

-- DHoare Auto Tactic
open Lean Elab Tactic Meta

syntax "DHoare_Zset_auto_aux": tactic
elab_rules : tactic
  | `(tactic| DHoare_Zset_auto_aux) => do
    let goal_type ← getMainTarget
    -- Pattern match on the goal structure
    if goal_type.isAppOf ``DHoare then
      let ckt := goal_type.getArg! 2
      -- Handle sequential composition (>>c)
      if ckt.isAppOf ``CktBasic.Ckt.seq then
        evalTactic (← `(tactic| apply DHoare_seq <;> try DHoare_Zset_auto_aux))
      -- Handle parallel composition (&&c)
      else if ckt.isAppOf ``CktBasic.Ckt.par then
        evalTactic (← `(tactic| apply DHoare_par <;> try DHoare_Zset_auto_aux))
      else if ckt.isAppOf ``CktBasic.Ckt.id then
        evalTactic (← `(tactic| apply DHoare_id))
      else if ckt.isAppOf ``CktBasic.Ckt.fst then
        evalTactic (← `(tactic| apply DHoare_fst))
      else if ckt.isAppOf ``CktBasic.Ckt.snd   then
        evalTactic (← `(tactic| apply DHoare_snd))
      else if ckt.isAppOf ``CktBasic.Ckt.delay then
        evalTactic (← `(tactic| apply DHoare_delay))
      -- Handle basic operations
      else if ckt.isAppOf ``CktBasic.Ckt.node1 then
        let op := ckt.getArg! 4
        if op.isAppOf ``Zset.distinct then
          evalTactic (← `(tactic| apply DHoare_Zset_distinct))
        else if op.isAppOf ``Zset.map then
          evalTactic (← `(tactic| apply DHoare_Zset_map))
        else if op.isAppOf ``filter then
          evalTactic (← `(tactic| apply DHoare_Zset_filter))
        else
          return
      else if ckt.isAppOf ``CktBasic.Ckt.node2 then
        let op := ckt.getArg! 6
        if op.isAppOf ``base_add then
          evalTactic (← `(tactic| apply DHoare_Zset_add))
        else if op.isAppOf ``base_sub then
          evalTactic (← `(tactic| apply DHoare_Zset_sub))
        else if op.isAppOf ``Zset_product then
          evalTactic (← `(tactic| apply DHoare_Zset_product))
        else if op.isAppOf ``Zset_join then
          evalTactic (← `(tactic| apply DHoare_Zset_join))
        else if op.isAppOf ``Zset_H then
          evalTactic (← `(tactic| apply DHoare_Zset_H))
        else
          return
      -- Handle I and D
      else if ckt.isAppOf ``cI then
        evalTactic (← `(tactic| apply DHoare_Zset_I))
      else if ckt.isAppOf ``cD then
        evalTactic (← `(tactic| apply DHoare_Zset_D))
    else
      evalTactic (← `(tactic| try simp))

elab "DHoare_Zset_auto": tactic => do evalTactic (← `(tactic|
  apply DHoare_weaken <;> DHoare_Zset_auto_aux))

namespace ZsetCktExamples

def ckt1 : Ckt ([Z[ℤ×ℤ×ℤ]]v ×ᵥ [Z[ℤ×ℤ×ℤ]]v) ([Z[ℤ×ℤ]]v) :=
  (c1st >>c cI >>czfilter (fun x => x.1 > 2) >>c zmap (fun x => x.2) &&c
    c2nd >>c cI >>c zfilter (fun x => x.1 > 5) >>c zmap (fun x => x.2)) >>c
  zjoin (fun x => x.2) (fun x => x.1) >>c
  zmap (fun (t1, t2) => (t1.1, t2.1)) >>c zdistinct >>c
  cD

theorem ckt1_DHoare:
    DHoare (ckt1)
      (fun x i => (sumVals (↑↑Prod.fst x) i.succ) * (sumVals (↑↑Prod.snd x) i.succ))
      (fun x i =>
        let t1 := (sumVals (↑↑Prod.fst x) i.succ);
        let t2 := (sumVals (↑↑Prod.snd x) i.succ)
        3 * (t1 + t2) + 4 * t1 * t2) := by
  unfold ckt1; DHoare_Zset_auto
  · intro x; intro t; simp
  · intro x; intro t; simp
    have :(x t).1 + sumVals (↑↑Prod.fst x) t = (sumVals (↑↑Prod.fst x) t.succ) := by simp
    rw [this]
    have :(x t).2 + sumVals (↑↑Prod.snd x) t = (sumVals (↑↑Prod.snd x) t.succ) := by simp
    rw [this]
    linarith

def opt_join: Ckt ([Z[ℤ×ℤ]]v ×ᵥ [Z[ℤ×ℤ]]v) ([Z[(ℤ×ℤ)×(ℤ×ℤ)]]v) :=
   letI j := zjoin (fun x => x.2) (fun x => x.1);
  ((c1st >>c cI &&c c2nd) >>c j
    &&c
    (c1st &&c c2nd >>c cI >>c cz⁻¹) >>c j)
  >>c cadd

def opt_distinct: Ckt ([Z[ℤ×ℤ]]v) ([Z[ℤ×ℤ]]v) :=
  (cI >>c cz⁻¹ &&c cid) >>c zH

def ckt2 : Ckt ([Z[ℤ×ℤ×ℤ]]v ×ᵥ [Z[ℤ×ℤ×ℤ]]v) ([Z[ℤ×ℤ]]v) :=
  (c1st >>c zfilter (fun x:ℤ×ℤ×ℤ => x.1 > 2) >>c zmap (fun x:ℤ×ℤ×ℤ => x.2) &&c
    c2nd >>c zfilter (fun x: ℤ×ℤ×ℤ => x.1 > 5) >>c zmap (fun x:ℤ×ℤ×ℤ => x.2)) >>c
  opt_join >>c
  zmap (fun (t1, t2) => (t1.1, t2.1)) >>c
  opt_distinct

theorem ckt2_DHoare:
    DHoare ckt2
      (fun x t =>
        z⁻¹ (fun i ↦
        ((x i).1 + sumVals (↑↑Prod.fst fun n ↦ x n) i) * (x i).2 +
            (x i).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) i +
          sumVals
            (fun i ↦
              ((x i).1 + sumVals (↑↑Prod.fst fun n ↦ x n) i) * (x i).2 +
                (x i).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) i)
            i)
         t +
      (((x t).1 + sumVals (↑↑Prod.fst fun n ↦ x n) t) * (x t).2 +
        (x t).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) t))
      (fun x t =>
            (x t).1 + (x t).1 + ((x t).2 + (x t).2) +
        ((x t).1 + sumVals (↑↑Prod.fst fun n ↦ x n) t + ((x t).1 + sumVals (↑↑Prod.fst fun n ↦ x n) t) * (x t).2 +
              ((x t).2 + sumVals (↑↑Prod.snd fun n ↦ x n) t + ((x t).2 + sumVals (↑↑Prod.snd fun n ↦ x n) t) +
                (x t).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) t) +
            (((x t).1 + sumVals (↑↑Prod.fst fun n ↦ x n) t) * (x t).2 +
              (x t).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) t) +
          (((x t).1 + sumVals (↑↑Prod.fst fun n ↦ x n) t) * (x t).2 +
              (x t).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) t +
            (((x t).1 + sumVals (↑↑Prod.fst fun n ↦ x n) t) * (x t).2 +
                    (x t).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) t +
                  sumVals
                    (fun i ↦
                      ((x i).1 + sumVals (↑↑Prod.fst fun n ↦ x n) i) * (x i).2 +
                        (x i).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) i)
                    t +
                (((x t).1 + sumVals (↑↑Prod.fst fun n ↦ x n) t) * (x t).2 +
                    (x t).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) t +
                  sumVals
                    (fun i ↦
                      ((x i).1 + sumVals (↑↑Prod.fst fun n ↦ x n) i) * (x i).2 +
                        (x i).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) i)
                    t) +
              (z⁻¹
                  (fun i ↦
                    ((x i).1 + sumVals (↑↑Prod.fst fun n ↦ x n) i) * (x i).2 +
                        (x i).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) i +
                      sumVals
                        (fun i ↦
                          ((x i).1 + sumVals (↑↑Prod.fst fun n ↦ x n) i) * (x i).2 +
                            (x i).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) i)
                        i)
                  t +
                (((x t).1 + sumVals (↑↑Prod.fst fun n ↦ x n) t) * (x t).2 +
                  (x t).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) t)))))) := by
  unfold ckt2 opt_join opt_distinct
  DHoare_Zset_auto
  · intro x; intro t; simp
  · intro x; intro t; simp

lemma dominate_example1 (x : stream (ℕ × ℕ))
  (h1: ↑↑Prod.fst x << (fun _ => 1)) (h2: ↑↑Prod.snd x << (fun _ => 1)):
    (fun t =>
        z⁻¹ (fun i ↦
        ((x i).1 + sumVals (↑↑Prod.fst fun n ↦ x n) i) * (x i).2 +
            (x i).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) i +
          sumVals
            (fun i ↦
              ((x i).1 + sumVals (↑↑Prod.fst fun n ↦ x n) i) * (x i).2 +
                (x i).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) i)
            i)
          t +
      (((x t).1 + sumVals (↑↑Prod.fst fun n ↦ x n) t) * (x t).2 +
        (x t).1 * z⁻¹ (fun i ↦ (x i).2 + sumVals (↑↑Prod.snd fun n ↦ x n) i) t)) << (fun t => t.succ ^ 2) := by
  have hs: (sumVals fun x ↦ 1) << (fun x => x) := by
    use 1; intro n; simp
    induction n; simp
    simp; linarith
  apply dom_trans
  apply dom_add_dom
  · apply dom_DelayInv
    · apply dom_trans
      apply dom_add_dom
      apply dom_add_dom
      apply dom_mul_dom
      apply dom_add_dom; apply h1
      apply dom_trans
      apply MonoDom_sumVals; apply h1; apply hs
      apply h2
      apply dom_mul_dom; apply h1
      apply dom_DelayInv
      · apply dom_add_dom; apply h2
        apply dom_trans
        apply MonoDom_sumVals; apply h2; apply hs
      · apply DelayInv_mono
        apply Monotone.add <;> simp [Monotone]
      apply dom_trans
      apply MonoDom_sumVals
      apply dom_add_dom
      apply dom_mul_dom
      apply dom_add_dom; apply h1
      apply dom_trans
      apply MonoDom_sumVals; apply h1; apply hs
      apply h2
      apply dom_mul_dom; apply h1
      apply dom_DelayInv
      apply dom_add_dom; apply h2
      apply dom_trans; apply MonoDom_sumVals; apply h2; apply hs
      apply DelayInv_mono; apply Monotone.add <;> simp [Monotone]
      apply MonoDom_sumVals
      apply dom_trans
      apply dom_add_ignore
      use 1; intro n; simp
      apply dom_trans
      rw [add_comm]; simp
      swap; exact (fun x => x + 1)
      use 2; intro n; simp
      simp
      apply dom_add_dom
      apply dom_add_same
      swap; exact (fun x => (x+1)^ 2)
      use 1; intro n; simp; induction n; simp
      simp; rw [add_sq, add_comm, add_assoc]
      gcongr; simp
      rw [two_mul, add_assoc _ 1]; simp
    · apply DelayInv_mono
      conv => rhs; intro x; simp
      apply Monotone.add
      simp [Monotone]
      apply Monotone.pow_const
      apply Monotone.add_const
      simp [Monotone]
  · apply dom_refl









end ZsetCktExamples

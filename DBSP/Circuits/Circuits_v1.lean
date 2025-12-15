import DBSP.StreamTheory.Operators
import DBSP.StreamTheory.Stream
import DBSP.StreamTheory.Linear
import DBSP.Circuits.ProdType

namespace CktBasic

class BaseType (T: Type) where
  has_zero: Zero T
  size: T -> ℕ
  -- For size of delay to be delay
  -- Another option is to define `delay_with` which specifies the first value
  size_zpp: size 0 = 0

instance (T: Type) [BaseType T]: Zero T := BaseType.has_zero

-- BaseType with Abelian group structure
class BaseTypeG (T:Type) where
  has_group: AddCommGroup T
  size: T -> ℕ
  size_zpp: size 0 = 0
  add_cost: T × T -> ℕ
  sub_cost: T × T -> ℕ
  neg_cost: T -> ℕ

instance GroupBaseTypeG (T: Type) [BaseTypeG T]: AddCommGroup T :=
  BaseTypeG.has_group

@[simp]
instance BaseTypeGToBaseType (T: Type) [BaseTypeG T]: BaseType T where
  has_zero := {zero := 0}
  size := BaseTypeG.size
  size_zpp := BaseTypeG.size_zpp

-- the type of the basetype values with Cartesian product
inductive VType: Type 1 where
  | base (T: Type) [BaseType T]: VType
  | prod (a b: VType) : VType

macro "[" t:term "]v" : term => `(VType.base $t)

notation a "×ᵥ" b :30 => VType.prod a b

@[reducible]
def VType_interp (a: VType): Type :=
  match a with
  | VType.base T => T
  | VType.prod a b => VType_interp a × VType_interp b

@[reducible]
def VType_struct (T: Type) (a: VType): PType T :=
  match a with
  | VType.base _ => PType.base
  | VType.prod a b => PType.prod (VType_struct T a) (VType_struct T b)

@[reducible]
def VType_Nat (a: VType) : Type :=
  PType_interp (VType_struct ℕ a)

instance (a: VType) : AddCancelCommMonoid (VType_Nat a) :=
  by infer_instance

instance (a: VType) : AddCancelCommMonoid (stream (VType_Nat a)) :=
  by infer_instance

instance (a: VType) : CanonicallyOrderedAdd (VType_Nat a) where
  exists_add_of_le := by
    induction a
    · intros a b h;
      simp [VType_Nat, PType_interp] at a b
      use (b-a); rw [add_comm]; symm
      rw [tsub_add_cancel_iff_le]; tauto
    · rename_i ih1 ih2; simp; intros
      constructor
      apply ih1; tauto
      apply ih2; tauto
  le_self_add := by
    induction a <;> simp; tauto

instance (a: VType) : CanonicallyOrderedAdd (stream (VType_Nat a)) :=
  by infer_instance

@[simp]
def VType_size {A: VType}: (VType_interp A) -> (VType_Nat A) :=
  match A with
  | VType.base _ => BaseType.size
  | VType.prod _ _ => fun x => (VType_size x.fst, VType_size x.snd)

instance VType_interp_Zero (a: VType) : Zero (VType_interp a) :=
  match a with
  | VType.base T => by infer_instance
  | VType.prod a b => by haveI := VType_interp_Zero a; haveI := VType_interp_Zero b; infer_instance

@[simp]
lemma VType_size_zpp {A: VType}: VType_size (0: VType_interp A) = 0 := by
  induction A <;> simp
  · apply BaseType.size_zpp
  · tauto

lemma VType_size_Timeinvariant {A: VType}: TimeInvariant (↑↑(@VType_size A)) := by
  apply lifting_timeInvariant; simp

-- Primitive node typeclass
class UnaryNode {A B: Type} [BaseType A] [BaseType B] (f: A -> B) where
  zpp: f 0 = 0
  cost: A -> ℕ

class BinaryNode {A B C: Type} [BaseType A] [BaseType B] [BaseType C] (f: (A × B) -> C) where
  zpp: f 0 = 0
  cost: A × B -> ℕ

@[simp]
def base_add (A: Type) [BaseTypeG A] (x: A × A): A := x.fst + x.snd
@[simp]
def base_sub (A: Type) [BaseTypeG A] (x: A × A): A := x.fst - x.snd
@[simp]
def base_neg (A: Type) [BaseTypeG A] (x: A): A := -x

instance AddBinaryNode {A: Type} [BaseTypeG A]: BinaryNode (base_add A) where
  zpp := by simp
  cost := BaseTypeG.add_cost

instance SubBinaryNode {A: Type} [BaseTypeG A]: BinaryNode (base_sub A) where
  zpp := by simp
  cost := BaseTypeG.sub_cost

instance NegUnaryNode {A: Type} [BaseTypeG A]: UnaryNode (base_neg A) where
  zpp := by simp
  cost := BaseTypeG.neg_cost

-- Well-Formed Circuit
inductive Ckt: VType -> VType -> Type 1
  -- primitive nodes (lifted by default)
  | node1 {A B: Type} [BaseType A] [BaseType B] (f: A -> B) [UnaryNode f] : Ckt (VType.base A) (VType.base B)
  | node2 {A B C: Type} [BaseType A] [BaseType B] [BaseType C]
      (f: (A × B) -> C) [BinaryNode f] : Ckt (VType.base A ×ᵥ VType.base B) (VType.base C)
  -- product combinators
  | id {a: VType} : Ckt a a
  | fst {a b} : Ckt (a ×ᵥ b) a
  | snd {a b} : Ckt (a ×ᵥ b) b
  -- sequential composition
  | seq {a b c} (c1 : Ckt a b) (c2 : Ckt b c) : Ckt a c
  -- parallel composition
  | par {a b c} (c1 : Ckt a b) (c2 : Ckt a c) : Ckt a (b ×ᵥ c)
  -- delay
  | delay {a} : Ckt a a
  -- -- lifting
  -- | lifting {a b} (c: Ckt a b) : Ckt (VType.stream a) (VType.stream b)
  -- feedback loop
  | loop {a b} (c: Ckt (a ×ᵥ b) b): Ckt a b

--- Notation for circuits
-- Sequential Composition
infixr:60 " >>c "  => Ckt.seq
-- Parallel Composition
infixr:50 " &&c " => Ckt.par

notation "cid" => Ckt.id
notation "c1st" => Ckt.fst
notation "c2nd" => Ckt.snd
notation:max "c↑" c => Ckt.lifting c
notation "cz⁻¹" => Ckt.delay
notation "cloop " c => Ckt.loop c
notation:max "c₁" f => Ckt.node1 f
notation:max "c₂" f => Ckt.node2 f
notation "cadd" => Ckt.node2 (base_add _)
notation "csub" => Ckt.node2 (base_sub _)
notation "cneg" => Ckt.node1 (base_neg _)

-- denotational semantics of circuits
-- which means both input and output types are streams
def denote {a b: VType}: (Ckt a b) -> (Operator (VType_interp a) (VType_interp b))
  | Ckt.node1 f => lifting f
  | Ckt.node2 f => lifting f
  | Ckt.id => lifting id
  | Ckt.fst => lifting Prod.fst
  | Ckt.snd => lifting Prod.snd
  | Ckt.seq c1 c2 => denote c2 ∘ denote c1
  | Ckt.par c1 c2 => fun x => sprod (denote c1 x, denote c2 x)
  | Ckt.delay => delay
  -- | Ckt.lifting c => lifting (denote c)
  | Ckt.loop c => fun a => fix (fun s => denote c (sprod (a, z⁻¹ s)))

theorem ckt_causal {a b: VType} (c: Ckt a b): Causal (denote c) := by
  induction c <;> simp [denote]
  case seq a b c c1 c2 h1 h2 =>
    apply causal_comp_causal (denote c1) <;> tauto
  case par a b c c1 c2 h1 h2 =>
    apply causal_sprod_causal <;> tauto
  case delay =>
    apply delay_causal
  case loop a b c ih =>
    apply loop1_causal delay _ (fun a' s => denote c (sprod (a', s)))
    rw [uncurryOp_sprod_eq]; assumption
    apply delay_strict

lemma loop_denote_ind {a b: VType} s (c: Ckt (a ×ᵥ b) b) x
    (h: s = denote c (sprod (x, z⁻¹ s))):
    denote (Ckt.loop c) x = s := by
  simp [denote]
  symm
  apply fix_unique
  · apply loop1_body_strict delay delay_strict (fun x s => denote c (sprod (x, s)))
    rw [uncurryOp_sprod_eq]; apply ckt_causal
  · tauto

theorem ckt_time_invariant {a b: VType} (c: Ckt a b): TimeInvariant (denote c) := by
  induction c <;> simp [denote] <;> try apply lift_timeInvariant <;> try simp
  case node1 =>
    apply UnaryNode.zpp
  case node2 =>
    apply BinaryNode.zpp
  case seq a b c c1 c2 h1 h2 =>
    rw [timeInvariant_comp] at *
    rw [Function.comp_assoc, h1, ← Function.comp_assoc, h2, Function.comp_assoc]
  case par a b c c1 c2 h1 h2 =>
    simp [TimeInvariant]; intro s
    rw [delay_sprod, h1, h2]
  case delay =>
    apply delay_timeInvariant
  -- case lifting n a b c ih =>
  --   apply timeInvariant_zpp at ih; tauto
  case loop a b c ih =>
    apply loop1_timeInvariant delay _ _ (fun a' s => denote c (sprod (a', s)))
    · rw [uncurryOp_sprod_eq]; apply ckt_causal
    · rw [uncurryOp_sprod_eq]; assumption
    · apply delay_strict
    · apply delay_timeInvariant

-- Cost model for circuits based on the continuous stream computation assumption
-- For a circuit `c`, `cost_f c` is a function maps an input of `c` to the cost of computing the output
def cost_f {a b: VType}: (Ckt a b) -> (Operator (VType_interp a) ℕ)
  | Ckt.node1 f => lifting (UnaryNode.cost f)
  | Ckt.node2 f => lifting (BinaryNode.cost f)
  | Ckt.id => lifting (fun _ => 0)
  | Ckt.fst => lifting (fun _ => 0)
  | Ckt.snd => lifting (fun _ => 0)
  | Ckt.seq c1 c2 => fun x i => cost_f c1 x i + cost_f c2 (denote c1 x) i
  | Ckt.par c1 c2 => fun x i => cost_f c1 x i + cost_f c2 x i
  | Ckt.delay => fun x i => PType_sum (VType_size (x i))
  -- This definition is based on the continuous stream computation assumption
  | Ckt.loop c => fun x i => let o := denote (Ckt.loop c) x
      cost_f c (sprod (x, z⁻¹ o)) i + PType_sum (VType_size (o i))

@[simp]
def costZ_f {a b: VType} (c: Ckt a b): (Operator (VType_interp a) ℤ) :=
  fun x => ↑↑Int.ofNat (cost_f c x)

-- I and D circuits
def cI {A: Type} [BaseTypeG A]: Ckt (VType.base A) (VType.base A) := cloop cadd
def cD {A: Type} [BaseTypeG A]: Ckt (VType.base A) (VType.base A) := (cid &&c cz⁻¹) >>c csub

@[simp]
lemma cI_denote {A: Type} [BaseTypeG A]:
    denote cI = (@I A _) := by rfl
@[simp]
lemma cD_denote {A: Type} [BaseTypeG A]:
    denote cD = (@D A _) := by rfl
@[simp]
lemma cI_cost {A: Type} [BaseTypeG A]:
    cost_f (@cI A _) = fun x i =>
      BaseTypeG.add_cost ((sprod (x, z⁻¹ (I x))) i) + BaseTypeG.size ((I x) i) := by rfl
@[simp]
lemma cD_cost {A: Type} [BaseTypeG A]:
    cost_f (@cD A _) = fun x i =>
      BaseTypeG.sub_cost ((sprod (x, z⁻¹ x)) i) + BaseTypeG.size (x i) := by
  simp [cost_f, cD]; funext x i; abel

end CktBasic

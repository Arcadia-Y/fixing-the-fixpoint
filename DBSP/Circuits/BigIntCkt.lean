import DBSP.Circuits
import Mathlib.Algebra.Order.Group.Unbundled.Abs

namespace BigInt
open CktBasic

@[simp]
def VType_Nat {n: ℕ} (a: VType n): Type :=
  match a with
  | VType.base _ => ℕ
  | VType.prod a b => VType_Nat a × VType_Nat b
  | VType.stream a => stream (VType_Nat a)

instance Zero_VType_Nat {n: ℕ} (a: VType n) : Zero (VType_Nat a) :=
  match a with
  | VType.base T => by simp; infer_instance
  | VType.prod a b => by haveI := Zero_VType_Nat a; haveI := Zero_VType_Nat b; simp; infer_instance
  | VType.stream a => by haveI := Zero_VType_Nat a; simp; infer_instance

def VType_Nat_Add {n: ℕ} {a: VType n} (x y: VType_Nat a): VType_Nat a :=
  match a with
  | VType.base _ => by simp at x y; exact x + y
  | VType.prod a b => (VType_Nat_Add x.1 y.1, VType_Nat_Add x.2 y.2)
  | VType.stream a => fun n => VType_Nat_Add (x n) (y n)

instance {n: ℕ} {a: VType n} : Add (VType_Nat a) where
  add := VType_Nat_Add

-- a quantity of certain type
inductive QNat: Type where
  | base (v: ℕ): QNat
  | prod (a b: QNat) : QNat
  | stream (a: QNat) : QNat

@[reducible]
instance QNatBaseCoe : Coe ℕ QNat :=
  ⟨fun n => QNat.base n⟩

instance BaseTypeNat : BaseType ℕ where
  haszero := ⟨0⟩

@[simp] def Zadd (x: ℕ × ℕ) := x.1 + x.2
@[simp] def Zmul (x: ℕ × ℕ) := x.1 * x.2

def log2 (x: ℕ) : ℕ :=
  Nat.log 2 (Int.toNat |x|)

def Nsize (x: ℕ) : ℕ :=
  log2 x + 1

instance BinaryNodeAdd : BinaryNode Zadd where
  zpp := rfl
  cost := fun (x, y) => max (Nsize x) (Nsize y)

instance BinaryNodeMul : BinaryNode Zmul where
  zpp := rfl
  cost := fun (x, y) =>
    let k := max (Nsize x) (Nsize y)
    let m := min (Nsize x) (Nsize y)
    k * log2 m

inductive CktSize: ∀ {n: ℕ} {A B: VType n}, Ckt A B -> QNat -> QNat -> Prop where
  | add (a b: ℕ): CktSize (c₂ Zadd) (QNat.prod a b) (QNat.base (max a b + 1))
  | mul (a b: ℕ): CktSize (c₂ Zmul) (QNat.prod a b) (a + b)

def add_ckt := c₂ Zadd

lemma test (i: ℕ):
  cost_f add_ckt (sprod ((fun x: ℕ => (x: ℕ)), (fun x: ℕ => (x: ℕ)))) i <= Nsize i + 1 := by
  simp [cost_f, add_ckt, BinaryNode.cost, Nsize]
  
end BigInt

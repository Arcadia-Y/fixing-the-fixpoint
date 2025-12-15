import DBSP.Circuits
import Mathlib.Data.Num.Basic
import DBSP.StreamTheory.Linear
open CktBasic

instance BaseTypeBool : BaseType Bool where
  has_zero := ⟨0⟩
  size := fun b => 0
  size_zpp := by rfl

instance BaseTypeNum : BaseType Num where
  has_zero := ⟨0⟩
  size := fun n => if n = 0 then 0 else 1
  size_zpp := by rfl

def incr: (Bool × Num) -> Num :=
  fun (b, x) => if b then x.succ else x

def trailing1_aux (x: PosNum): ℤ :=
  match x with
  | PosNum.one => 1
  | PosNum.bit1 p => trailing1_aux p + 1
  | PosNum.bit0 _ => 0

def trailing1 (x: Num): ℤ :=
  match x with
  | Num.zero => 0
  | Num.pos p => trailing1_aux p

@[simp]
instance BinaryNodeIncr: BinaryNode incr where
  zpp := rfl
  cost := fun (b, x) => if b then (trailing1 x + 1).toNat else 0

def counter :=
  cloop (c₂ incr)

@[simp]
def Atrue : ℕ -> Bool := fun _ => true

def bit1_count_aux (x: PosNum): ℤ :=
  match x with
  | PosNum.one => 1
  | PosNum.bit1 p => bit1_count_aux p + 1
  | PosNum.bit0 p => bit1_count_aux p

def bit1_count (x: Num): ℤ :=
  match x with
  | Num.zero => 0
  | Num.pos p => bit1_count_aux p

def amortized_f (c: Ckt (VType.base Bool) (VType.base Num)) :=
  fun x => let o := denote c x
    (costZ_f c x) + D (lifting bit1_count o)

theorem amortized_correct (c: Ckt (VType.base Bool) (VType.base Num)) x:
    I (costZ_f c x) = I (amortized_f c x) - lifting bit1_count (denote c x) := by
  simp [amortized_f]
  rw [integral_linear, derivative_integral]
  simp

lemma output_seq:
    denote counter Atrue = fun i => Num.ofNat' (i + 1) := by
  apply loop_denote_ind
  funext i
  simp [denote, incr, Atrue, delay]
  rcases i <;> simp
  · decide
  · rw [Num.add_one]

lemma trailing1_nonneg (x: Num):
    0 ≤ trailing1 x := by
  rcases x <;> simp [trailing1]
  rename_i p; induction p
  case one => decide
  case pos.bit1 p ih => simp [trailing1_aux]; omega
  case pos.bit0 p ih => simp [trailing1_aux]

lemma real_cost (i: ℕ):
    cost_f counter Atrue i = trailing1 (↑i) + 2 := by
  simp [cost_f, counter]; rw [<- counter]
  rw [output_seq]; simp [delay, BaseType.size]
  rcases i <;> simp
  · simp [trailing1]
  · split_ifs with h <;> rw [<- Num.to_nat_inj] at h; simp at h
    rename_i n; have := trailing1_nonneg (↑n + 1)
    omega

lemma bit1_count_succ (x: Num):
    bit1_count (x + 1) = bit1_count x - trailing1 x + 1 := by
  rw [Num.add_one]
  rcases x <;> simp [bit1_count, Num.succ, trailing1, bit1_count_aux, Num.succ']
  rename_i p; induction p
  case one => decide
  case pos.bit1 p ih =>
    simp [PosNum.succ, bit1_count_aux, trailing1_aux]; tauto
  case pos.bit0 p ih =>
    simp [PosNum.succ, bit1_count_aux, trailing1_aux]

theorem amortized_cost:
    amortized_f counter Atrue = fun _ => 3 := by
  funext i; simp [amortized_f]
  rw [real_cost, output_seq]
  simp [delay]
  rcases i; simp; decide
  simp [D]; rw [bit1_count_succ]
  omega

lemma sumVals_constant (c: ℤ) (n: ℕ):
    sumVals (fun _ => c) n = c * n := by
  induction' n with n n_ih
  · simp
  · simp; rw [n_ih]; ring

lemma bit1_count_nonneg (x: Num):
    0 ≤ bit1_count x := by
  rcases x <;> simp [bit1_count]
  rename_i p; induction p <;> simp [bit1_count_aux, PosNum.succ] <;> omega

theorem total_real_cost (n: ℕ):
    I (costZ_f counter Atrue) n ≤ 3 * (n+1) := by
  rw [amortized_correct, amortized_cost, output_seq]
  simp; rw [integral_sumVals, sumVals_constant]
  have := bit1_count_nonneg (↑n + 1)
  omega

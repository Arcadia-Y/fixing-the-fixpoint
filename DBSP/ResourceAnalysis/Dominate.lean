import DBSP.StreamTheory.Stream
import DBSP.StreamTheory.Linear
import DBSP.StreamTheory.StreamElim
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

section dominate
variable {A B C: Type}
  [PartialOrder A] [AddCommMonoid A]
  [PartialOrder B] [AddCommMonoid B]
  [PartialOrder C] [AddCommMonoid C]

omit [PartialOrder A] in
@[simp]
lemma smul_stream_apply (s: stream A) (k n: ℕ) :
    (k • s) n = k • (s n) := by rfl

instance [IsOrderedAddMonoid A] : CovariantClass ℕ A HSMul.hSMul LE.le := by
  constructor
  intros k x y h
  induction k; simp
  simp_rw [succ_nsmul]
  apply add_le_add <;> tauto

instance [IsOrderedAddMonoid A] : CovariantClass ℕ (stream A) HSMul.hSMul LE.le := by
  constructor
  intros k s1 s2 h
  induction k; simp
  simp_rw [succ_nsmul]
  apply add_le_add <;> tauto

instance [CanonicallyOrderedAdd A] : IsOrderedAddMonoid A := by
  apply CanonicallyOrderedAdd.toIsOrderedAddMonoid

theorem delay_le [CanonicallyOrderedAdd A] (s: stream A) (h: Monotone s): (z⁻¹ s) ≤ s := by
  intro m
  simp [delay]; split_ifs; simp
  apply h; simp

variable {k k1 k2: ℕ}

theorem Dom_trans [IsOrderedAddMonoid A] {x y z: stream A}
  (h1: x ≤ k1 • y) (h2: y ≤ k2 • z):
    x ≤ (k1 * k2) • z := by
  apply le_trans h1
  apply le_trans (nsmul_le_nsmul_right h2 k1)
  rw [mul_smul]

theorem Dom_scale_k [CanonicallyOrderedAdd A] (k2 k1: ℕ)(x y: stream A)
  (h: x ≤ k1 • y) (hk: k1 ≤ k2) :
    x ≤ k2 • y := by
  apply le_trans h
  apply nsmul_le_nsmul_left _ hk
  simp

theorem Dom_add_Dom [CanonicallyOrderedAdd A]
  {k1 k2: ℕ} {a1 a2 b1 b2: stream A}
  (ha: a1 ≤ k1 • a2) (hb: b1 ≤ k2 • b2) :
    a1 + b1 ≤ (max k1 k2) • (a2 + b2) := by
  have ha' := Dom_scale_k (max k1 k2) k1 _ _ ha (by simp)
  have hb' := Dom_scale_k (max k1 k2) k2 _ _ hb (by simp)
  apply le_trans (add_le_add ha' hb')
  simp [nsmul_add]

theorem mul_le_mul_of_le (x1 x2 y1 y2: stream ℕ)
  (h1: x1 ≤ x2) (h2: y1 ≤ y2):
    (fun i => (x1 i) * (y1 i)) ≤ (fun i => (x2 i) * (y2 i)) := by
  intro m
  apply mul_le_mul' (h1 m) (h2 m)

theorem add_self_le_two_co [CanonicallyOrderedAdd A] {s: stream A}:
    s + s ≤ 2 • s := by
  simp [two_smul]

theorem add_le_two_co [CanonicallyOrderedAdd A] {s1 s2 b: stream A}
  (h1: s1 ≤ b) (h2: s2 ≤ b):
    s1 + s2 ≤ 2 • b := by
  simp [two_smul]
  apply add_le_add h1 h2

theorem Dom_add_same_bound [CanonicallyOrderedAdd A] {k1 k2: ℕ} {s1 s2 b: stream A}
  (h1: s1 ≤ k1 • b) (h2: s2 ≤ k2 • b):
    s1 + s2 ≤ (k1 + k2) • b := by
  apply le_trans (add_le_add h1 h2)
  simp [add_nsmul]

theorem Dom_add_ignore [CanonicallyOrderedAdd A] (s1 s2: stream A) (h: s2 ≤ k • s1):
    s1 + s2 ≤ (k+1) • s1 := by
  rw [add_comm, succ_nsmul]
  apply add_le_add h
  rfl

theorem le_integral [CanonicallyOrderedAdd A] {s b: stream A} (h: s ≤ b):
    s ≤ I b := by
  intro m
  simp [integral_sumVals]
  apply le_trans (h m)
  simp

theorem mono_integral:
    Monotone (@I ℕ _) := by
  intro x y hl
  intro i; induction i
  case zero => apply hl
  case succ n ih =>
    simp_rw [integral_sumVals] at ih ⊢
    simp at ih ⊢
    apply add_le_add
    apply hl
    apply ih

variable [CanonicallyOrderedAdd A]

theorem mono_integral_stream {s: stream ℕ}:
    Monotone (I s) := by
  intro a b h; simp_rw [integral_sumVals]
  revert a; induction b; simp
  rename_i n ih; intros a ha
  by_cases ha2: a ≤ n
  · apply le_trans
    apply ih; tauto
    simp
  · have : a = n + 1 := by omega
    rw [this]

theorem delay_Monotone {s b: stream A}
  (hs: s ≤ k1 • b) (hb: Monotone b) :
    z⁻¹ s ≤ k1 • b := by
  have h1 : z⁻¹ s ≤ z⁻¹ (k1 • b) := by
    intro n
    simp [delay]
    split_ifs; simp
    apply hs
  apply le_trans h1
  intro n
  simp [delay]; split_ifs; simp
  apply nsmul_le_nsmul_right
  apply hb
  omega

end dominate

import DBSP.StreamTheory.Stream
import DBSP.StreamTheory.Linear
import DBSP.StreamTheory.StreamElim
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

section dominate
variable {A B C: Type}
  [PartialOrder A] [AddCancelCommMonoid A]
  [PartialOrder B] [AddCancelCommMonoid B]
  [PartialOrder C] [AddCancelCommMonoid C]

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

structure Dom (s1 s2: A) where
  k: ℕ
  h: s1 ≤ k • s2

infix:50 " << " => Dom
def Dom_refl (x: A): x << x := by
  use 1; simp

def Dom_trans [IsOrderedAddMonoid A] {x y z: A} (h1: Dom x y) (h2: Dom y z): Dom x z where
  k := h1.k * h2.k
  h := by
    rcases h1 with ⟨k1, h1⟩
    rcases h2 with ⟨k2, h2⟩
    apply smul_le_smul_left k1 at h2; simp at h2
    rw [smul_smul] at h2
    apply le_trans <;> tauto

def delay_Dom [CanonicallyOrderedAdd A] (s: stream A) (h: Monotone s): Dom (z⁻¹ s) s := by
  use 1; simp; intro n
  simp [delay]; split_ifs; simp
  apply h; simp

def le_Dom (s1 s2: A) (h:s1 ≤ s2): Dom s1 s2 := by
  use 1; simp [h]

def Dom_self_add [CanonicallyOrderedAdd A] (s1 s2: A): Dom s1 (s1 + s2) := by
  use 1; simp

def add_Dom_add_r [CanonicallyOrderedAdd A] (s3 s1 s2: A)
  (h: s1 << s2) : s1 + s3 << s2 + s3 := by
  rcases h with ⟨k, h⟩
  cases k
  · simp at h; subst h
    use 1; simp
  · rename_i n; use (n+1)
    simp; apply add_le_add
    · tauto
    · rw [succ_nsmul]; simp

def Dom_self_add_r [CanonicallyOrderedAdd A] (s3 s1 s2: A)
  (h: Dom s1 s2): Dom (s1 + s3) (s2 + s3) := by
  rcases h with ⟨k, h⟩
  cases k
  · simp at h; subst h
    use 1; simp
  · rename_i n; use (n+1)
    simp; apply add_le_add
    · tauto
    · rw [succ_nsmul]; simp

def add_Dom_add_l [CanonicallyOrderedAdd A] (s3 s1 s2: A)
  (h: s1 << s2) : s3 + s1 << s3 + s2 := by
  rw [add_comm s3, add_comm s3]
  apply add_Dom_add_r; tauto

def Dom_self_add_l [CanonicallyOrderedAdd A] (s3 s1 s2: A)
  (h: Dom s1 s2): Dom (s3 + s1) (s3 + s2) := by
  rw [add_comm s3, add_comm s3]
  apply Dom_self_add_r; tauto

lemma smul_le_strenth [CanonicallyOrderedAdd A] (x y: A) (k1 k2: ℕ)
  (h: x ≤ k1 • y) (hk: k1 ≤ k2) :
    x ≤ k2 • y := by
  revert x y
  have : k2 = k1 + (k2 - k1) := by omega
  rw [this]; rw [this] at hk
  set d := (k2-k1); clear this hk
  induction d; simp
  rename_i ih
  intro x y h
  rw [<- add_assoc, succ_nsmul]
  apply le_trans; apply ih <;> tauto
  simp

def Dom_add_Dom [CanonicallyOrderedAdd A] (a1 a2 b1 b2: A)
  (ha: Dom a1 a2) (hb: Dom b1 b2) :
    Dom (a1 + b1) (a2 + b2) := by
  rcases ha with ⟨k1, h1⟩
  rcases hb with ⟨k2, h2⟩
  use (max k1 k2)
  apply (smul_le_strenth (k2:= max k1 k2)) at h1
  apply (smul_le_strenth _ _ k2 (max k1 k2)) at h2
  simp; apply add_le_add
  · apply h1; simp
  · apply h2; simp

def Dom_mul_Dom (x1 x2 y1 y2: stream ℕ)
  (hx: x1 << x2) (hy: y1 << y2):
    (fun i => (x1 i) * (y1 i)) << (fun i => (x2 i) * (y2 i)) := by
  rcases hx with ⟨k1, h1⟩
  rcases hy with ⟨k2, h2⟩
  use (k1 * k2)
  intro n; simp
  specialize h1 n
  specialize h2 n
  have := mul_le_mul h1 h2 (by simp) (by simp)
  apply le_trans; apply this; simp
  rw [mul_assoc, <- mul_assoc (x2 n), mul_comm (x2 n), mul_assoc, <- mul_assoc]

def Dom_add_same [CanonicallyOrderedAdd A] (s: A):
    s + s << s := by
  use 2; simp [two_smul]

def Dom_add_ignore [CanonicallyOrderedAdd A] (s1 s2: A) (h: s2 << s1):
    s1 + s2 << s1 := by
  apply Dom_trans
  apply add_Dom_add_l; tauto
  apply Dom_add_same

-- A stream bounded by a monotone stream
-- def MonoBound (s: stream A) : Prop :=
--   ∃ (s': stream A), Monotone s' /\ s << s'
section MonoDom
variable [IsOrderedAddMonoid A] [IsOrderedAddMonoid B] [IsOrderedAddMonoid C]
-- Monotone with respect to domination relation
def MonoDom (f: A -> B) :=
  ∀ s1 s2, s1 << s2 -> f s1 << f s2

def MonoDom.comp (f: A -> B) (g: B -> C)
  (hf: MonoDom f) (hg: MonoDom g):
    MonoDom (g ∘ f) := by
  intros s1 s2 h
  apply hg
  apply hf
  exact h

def MonoDom_id : MonoDom (id: Operator A A) := by
  intro x y h; apply h

def MonoDom_delay: MonoDom (@delay A _) := by
  rintro x y ⟨k, h⟩
  use k; intro n; simp [delay]
  split_ifs; simp
  apply h

def MonoDom_sumVals: MonoDom (@sumVals A _) := by
  rintro x y ⟨k, h⟩
  use k; intro n
  simp [sumVals]
  induction n; simp
  rename_i n ih
  simp; apply add_le_add <;> tauto

def MonoDom_fst: MonoDom (↑↑(@Prod.fst A B)) := by
  rintro x y ⟨k, h⟩
  use k; intro n; simp [lifting]
  apply (h n).1

def MonoDom_snd: MonoDom (↑↑(@Prod.snd A B)) := by
  rintro x y ⟨k, h⟩
  use k; intro n; simp [lifting]
  apply (h n).2

-- theorem MonoDom.MonoBound {s1: stream A} {f: Operator A B}
--   (hf: MonoDom f) (ha: MonoBound   1):
--     MonoBound (f s1) := by
end MonoDom

variable [CanonicallyOrderedAdd A]

def GoodBound (s: stream A) :=
  ∀ x, x << s -> z⁻¹ x << s

def DelayDom (s: stream A) :=
  z⁻¹ s << s

def GoodBound_to_DelayDom (s: stream A) (h: GoodBound s):
    DelayDom s := by
  unfold GoodBound at h; specialize h s (Dom_refl s)
  exact h

def DelayDom_to_GoodBound (s: stream A) (h: DelayDom s):
    GoodBound s := by
  intro x hx
  apply MonoDom_delay at hx
  apply Dom_trans <;> tauto

def DelayDom_mono (s: stream A) (h: Monotone s):
    DelayDom s := by
  use 1; intro n; simp [delay]
  split_ifs; simp
  apply h; omega

def DelayDom_meaning (s: stream A):
    (Nonempty (DelayDom s)) <->
    ∃ (k: ℕ), ∀ n, s n <= k • (s (n+1)) := by
  constructor
  · intro h
    rcases h with ⟨k, h⟩
    use k
    intro n
    specialize h (n+1)
    apply h
  · rintro ⟨k, h⟩
    constructor
    use k
    intro n; simp [delay]
    split_ifs; simp
    specialize h (n-1)
    have : n - 1 + 1 = n := by omega
    rw [this] at h; apply h

def dom_DelayDom (s b: stream A)
  (hs: s << b) (hb: DelayDom b) :
    z⁻¹ s << b := by
  apply DelayDom_to_GoodBound at hb
  apply hb; tauto

end dominate

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

def Dom (k n: ℕ) (s1 s2: stream A): Prop :=
  ∀ m ≤ n, s1 m ≤ (k • s2) m
notation:60 s1 " <[" k ", " n "] " s2 => Dom k n s1 s2

def Dom_all (k: ℕ) (s1 s2: stream A): Prop :=
  ∀ n, s1 n ≤ (k • s2) n

lemma Dom_iff_Dom_all (s1 s2: stream A) (k: ℕ):
    (∀ n, Dom k n s1 s2) <-> Dom_all k s1 s2 := by
  simp [Dom, Dom_all]; tauto

variable {n: ℕ}

theorem Dom_rfl (x: stream A): x <[1, n] x := by simp [Dom]

variable {k k1 k2: ℕ}

theorem Dom_trans [IsOrderedAddMonoid A] {x y z: stream A}
  (h1: Dom k1 n x y) (h2: Dom k2 n y z):
    Dom (k2 * k1) n x z := by
  intro m hm; specialize h1 m hm; specialize h2 m hm
  apply smul_le_smul_left k1 at h2; simp at h2
  rw [smul_smul, mul_comm] at h2
  apply le_trans <;> tauto

theorem delay_Dom [CanonicallyOrderedAdd A] (s: stream A) (h: Monotone s): (z⁻¹ s) <[1, n] s := by
  simp [Dom]; intro m hm
  simp [delay]; split_ifs; simp
  apply h; simp

theorem le_Dom (s1 s2: stream A) (h:s1 ≤ s2): s1 <[1, n] s2 := by
  simp [Dom]; intros; apply h

theorem Dom_le_weaken [IsOrderedAddMonoid A] {x y z: stream A}
  (h1: Dom k1 n x y) (h2: y ≤ z):
    Dom k1 n x z := by
  rw [<- one_mul k1]
  apply Dom_trans h1
  apply le_Dom; tauto

theorem Dom_self_add [CanonicallyOrderedAdd A] (s1 s2: stream A): s1 <[1, n] (s1 + s2) := by simp [Dom]

theorem add_Dom_add_r [CanonicallyOrderedAdd A] (s3 s1 s2: stream A)
  (h: s1 <[k, n] s2) : s1 + s3 <[max k 1, n] s2 + s3 := by
  intro m hm; specialize h m hm
  cases k
  · simp [Dom] at h
    simp [Dom]; rw [h]; simp
  · rename_i n
    simp [Dom]; apply add_le_add
    · tauto
    · rw [succ_nsmul]; simp

theorem Dom_self_add_r [CanonicallyOrderedAdd A] (s3 s1 s2: stream A)
  (h: s1 <[k, n] s2): s1 + s3 <[max k 1, n] s2 + s3 := by
  intro m hm; specialize h m hm
  cases k
  · simp [Dom] at h
    simp [Dom]; rw [h]; simp
  · rename_i n
    simp [Dom]; apply add_le_add
    · tauto
    · rw [succ_nsmul]; simp

theorem add_Dom_add_l [CanonicallyOrderedAdd A] (s3 s1 s2: stream A)
  (h: s1 <[k, n] s2) : s3 + s1 <[max k 1, n] s3 + s2 := by
  rw [add_comm s3, add_comm s3]
  apply add_Dom_add_r; tauto

theorem Dom_self_add_l [CanonicallyOrderedAdd A] (s3 s1 s2: stream A)
  (h: s1 <[k, n] s2): s3 + s1 <[max k 1, n] s3 + s2 := by
  rw [add_comm s3, add_comm s3]
  apply Dom_self_add_r; tauto

theorem Dom_scale_k [CanonicallyOrderedAdd A] (k2 k1: ℕ)(x y: stream A)
  (h: x <[k1, n] y) (hk: k1 ≤ k2) :
    x <[k2, n] y := by
  revert x y
  have : k2 = k1 + (k2 - k1) := by omega
  rw [this]; rw [this] at hk
  set d := (k2-k1); clear this hk
  induction d; simp
  rename_i ih
  intro x y h; simp [Dom]
  intro m hm
  rw [<- add_assoc, succ_nsmul]
  apply le_trans; apply ih <;> tauto
  simp

theorem Dom_add_Dom [CanonicallyOrderedAdd A]
  {k1 k2: ℕ} {a1 a2 b1 b2: stream A}
  (ha: a1 <[k1, n] a2) (hb: b1 <[k2, n] b2) :
    a1 + b1 <[max k1 k2, n] a2 + b2 := by
  apply (Dom_scale_k (max k1 k2)) at ha
  apply (Dom_scale_k (max k1 k2)) at hb
  simp [Dom]; intro m hm; apply add_le_add
  · apply ha; simp; tauto
  · apply hb; simp; tauto

theorem Dom_mul_Dom (x1 x2 y1 y2: stream ℕ)
  (h1: x1 <[k1, n] x2) (h2: y1 <[k2, n] y2):
    (fun i => (x1 i) * (y1 i)) <[k1*k2, n] (fun i => (x2 i) * (y2 i)) := by
  intro m hm; simp
  specialize h1 m hm
  specialize h2 m hm
  have := mul_le_mul h1 h2 (by simp) (by simp)
  apply le_trans; apply this; simp
  rw [mul_assoc, <- mul_assoc (x2 m), mul_comm (x2 m), mul_assoc, <- mul_assoc]

theorem Dom_add_same [CanonicallyOrderedAdd A] {s: stream A}:
    s + s <[2, n] s := by
  simp [Dom, two_smul]

theorem Dom_add_same_bound [CanonicallyOrderedAdd A] {k1 k2: ℕ} {s1 s2 b: stream A}
  (h1: s1 <[k1, n] b) (h2: s2 <[k2, n] b):
    s1 + s2 <[k1+k2, n] b := by
  intro m hm; specialize h1 m hm; specialize h2 m hm
  simp [add_smul]; apply add_le_add <;> tauto

theorem Dom_add_zero_l [CanonicallyOrderedAdd A] {k1 k2: ℕ} {s1 s2 b: stream A}
  (h1: s1 <[k1, n] 0) (h2: s2 <[k2, n] b):
    s1 + s2 <[k2, n] b := by
  intro m hm; specialize h1 m hm; specialize h2 m hm
  simp [add_smul]
  simp at h1; rw [h1]; simp; apply h2

theorem Dom_add_zero_r [CanonicallyOrderedAdd A] {k1 k2: ℕ} {s1 s2 b: stream A}
  (h1: s1 <[k1, n] b) (h2: s2 <[k2, n] 0):
    s1 + s2 <[k1, n] b := by
  rw [add_comm]; apply Dom_add_zero_l <;> tauto

theorem Dom_add_ignore [CanonicallyOrderedAdd A] (s1 s2: stream A) (h: s2 <[k, n] s1):
    s1 + s2 <[k+1, n] s1 := by
  intro m hm
  simp [Dom, succ_nsmul]; rw [add_comm]
  apply add_le_add <;> tauto

theorem Dom_integral [CanonicallyOrderedAdd A] {s b: stream A} (h: s <[k, n] b):
    s <[k, n] I b := by
  intro m hm; simp [integral_sumVals]
  apply le_trans; apply h; tauto
  simp

theorem Dom_release_k [CanonicallyOrderedAdd A] {s b: stream A}
  (h: s <[k, n] b):
    s <[1, n] k • b := by
  simp [Dom] at *; tauto

theorem Dom_absorb_k [CanonicallyOrderedAdd A] {s b: stream A}
  (h: s <[1, n] k • b):
    s <[k, n] b := by
  simp [Dom] at *; tauto

section MonoDom

-- Monotone with respect to domination relation
def MonoDom (sf: ℕ -> ℕ) (f: Operator A B) :=
  ∀ (k n: ℕ) (s1 s2: stream A), (s1 <[k, n] s2) -> f s1 <[sf k, n] f s2

theorem MonoDom.comp (f: Operator A B) (g: Operator B C)
  {sf1 sf2: ℕ -> ℕ}
  (hf: MonoDom sf1 f) (hg: MonoDom sf2 g):
    MonoDom (sf2 ∘ sf1) (g ∘ f) := by
  intros k n s1 s2 h
  apply hg
  apply hf
  exact h

variable [IsOrderedAddMonoid A] [IsOrderedAddMonoid B] [IsOrderedAddMonoid C]

def MonoDom_id : MonoDom id (id: Operator A A) := by
  intro k n x y; simp

def MonoDom_delay: MonoDom id (@delay A _) := by
  rintro k n x y h
  intro m hm; simp [delay]
  split_ifs; simp
  apply h; omega

def MonoDom_sumVals: MonoDom id (@sumVals A _) := by
  rintro k n x y h
  intro m hm
  simp [sumVals]
  induction m; simp
  rename_i m ih
  specialize ih (by omega)
  simp; apply add_le_add <;> try tauto
  apply h; omega

def MonoDom_fst: MonoDom id (↑↑(@Prod.fst A B)) := by
  rintro k n x y h
  intro m hm; simp [lifting]
  apply (h m hm).1

def MonoDom_snd: MonoDom id (↑↑(@Prod.snd A B)) := by
  rintro k n x y h
  intro m hm; simp [lifting]
  apply (h m hm).2

end MonoDom

variable [CanonicallyOrderedAdd A]

def GoodBound (sf: ℕ -> ℕ)(s: stream A) :=
  ∀ x k n, (x <[k, n] s) -> z⁻¹ x <[sf k, n] s

def DelayDom (k: ℕ) (s: stream A) :=
  ∀ n, z⁻¹ s <[k, n] s

omit [CanonicallyOrderedAdd A] in
lemma GoodBound_to_DelayDom (s: stream A)
  {sf: ℕ -> ℕ} (h: GoodBound sf s):
    DelayDom (sf 1) s := by
  intro n
  specialize h s 1
  apply h; simp [Dom]

lemma DelayDom_to_GoodBound (s: stream A) (h: DelayDom k s):
    GoodBound (fun n => k * n) s := by
  intro x k n hx
  apply MonoDom_delay at hx
  apply Dom_scale_k
  apply Dom_trans; apply hx
  apply h
  simp

theorem DelayDom_mono (s: stream A) (h: Monotone s):
    DelayDom 1 s := by
  intro n i; simp [delay]
  split_ifs; simp
  intro; apply h; omega

theorem mono_integral {s: stream ℕ}:
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

theorem DelayDom_integral_N {s: stream ℕ}:
    DelayDom 1 (I s) := by
  apply DelayDom_mono
  apply mono_integral

theorem DelayDom_meaning (s: stream A):
    DelayDom k s <->
    ∀ n, s n <= k • (s (n+1)) := by
  constructor
  · intro h n
    specialize h (n+1) (n+1) (by simp); simp at h
    apply h
  · intro h n i hi; simp [DelayDom, delay]
    split_ifs; simp
    specialize h (i-1)
    have : i - 1 + 1 = i := by omega
    rw [this] at h; apply h

theorem dom_DelayDom {s b: stream A}
  (hs: s <[k1, n] b) (hb: DelayDom k2 b) :
    z⁻¹ s <[k2 * k1, n] b := by
  apply DelayDom_to_GoodBound at hb
  apply hb; tauto

end dominate

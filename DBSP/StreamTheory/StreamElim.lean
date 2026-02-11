-- Copyright 2022-2023 VMware, Inc.
import DBSP.StreamTheory.Stream
import DBSP.StreamTheory.Linear
import DBSP.StreamTheory.Incremental
import Mathlib.Tactic.Abel

-- SPDX-License-Identifier: BSD-2-Clause
section Zero

variable {a : Type} [Zero a]

def δ0 (x : a) : stream a := fun t => if t = 0 then x else 0

@[simp]
theorem δ0_apply (x : a) (n : ℕ) : δ0 x n = if n = 0 then x else 0 :=
  rfl

@[simp]
theorem δ0_0 : δ0 (0 : a) = 0 := by funext n; simp

lemma delta_D_const {a: Type} [AddCommGroup a] (x: a): δ0 x = D (fun _ => x) := by
  funext n
  simp [δ0, D]
  rcases n <;> simp

def ZeroAfter (s : stream a) (n : ℕ) :=
  ∀ t ≥ n, s t = 0

theorem ZeroAfter_ge {s : stream a} {n1 : ℕ} (pf1 : ZeroAfter s n1) : ∀ n2 ≥ n1, ZeroAfter s n2 :=
  by
  intro n2 hge
  intro m hge2
  apply pf1; omega

lemma δ0_ZeroAfter (x : a) : ZeroAfter (δ0 x) 1 := by intro t hge; unfold δ0; rw [if_neg]; omega

lemma ZeroAfter_ex_Minimal {A: Type} [Zero A]
  (s: stream A) (n: ℕ) (h: ZeroAfter s n) :
    ∃ m, Minimal (ZeroAfter s) m := by
  induction n
  · use 0; constructor; tauto
    omega
  · rename_i n ih
    by_cases hz: (ZeroAfter s n)
    · tauto
    · use (n+1); constructor; tauto
      intro y hzy hy
      by_contra
      have : n ≥ y := by omega
      have := ZeroAfter_ge hzy _ this
      tauto

lemma ZeroAfter_neg_iff {A: Type} [AddCommGroup A]
  (s: stream A) (n: ℕ):
    ZeroAfter (-s) n <-> ZeroAfter s n := by
  constructor <;> intro h
  · intro m hm
    specialize h m hm
    simp at h; assumption
  · intro m hm; simp
    apply h; assumption

lemma Minimal_ZeroAfter
  {A: Type} [Zero A] (s: stream A) (m n: ℕ)
  (h: Minimal (ZeroAfter s) m) (hn: (ZeroAfter s) n):
    m ≤ n := by
  rcases h with ⟨h1, h2⟩
  apply h2 at hn
  omega

end Zero

section sumVals
variable {a : Type}
def drop (k : ℕ) (s : stream a) : stream a := fun n => s (k + n)

@[simp]
theorem drop_0 (s: stream a): drop 0 s = s := by
  funext n
  simp [drop]

@[simp]
theorem drop_0stream [Zero a] (x: ℕ): drop x (0: stream a) = 0 := by
  funext n
  simp [drop]

@[simp]
theorem drop_1_delay [Zero a] (s: stream a): drop 1 (delay s) = s := by
  funext n
  simp [drop, delay]

@[simp]
theorem drop_drop (k m : ℕ) (s : stream a) : drop m (drop k s) = drop (k + m) s  :=
  by
  funext n
  unfold drop
  rw [Nat.add_assoc]

lemma drop_le_drop [PartialOrder a] (m: ℕ) (s1 s2: stream a) (h: s1 ≤ s2):
    drop m s1 ≤ drop m s2 := by
  intro n; simp [drop]
  apply h

variable [AddCancelCommMonoid a]

@[simp]
theorem smul_drop_comm (k x: ℕ) (s: stream a):
    k • drop x s = drop x (k • s) := by rfl

@[simp]
theorem drop_linear (k: ℕ) (s1 s2: stream a):
    drop k (s1 + s2) = drop k s1 + drop k s2 := by
  funext n
  simp [drop, add_comm]

theorem sumVals_split (s : stream a) (n k : ℕ) :
    sumVals s (n + k) = sumVals s n + sumVals (drop n s) k :=
  by
  revert n
  induction' k with k_n k_ih <;> introv
  · simp
  · conv =>
      lhs; rhs
      change (n + k_n).succ
    simp
    rw [k_ih]
    simp [drop]; abel

theorem sumVals_succ (s : stream a) (n : ℕ) :
    sumVals s (n + 1) = sumVals s n + s n :=
  by
  simp [sumVals, drop]
  abel

theorem sumVals_zero_ge (s : stream a) (n m : ℕ) (hz : ZeroAfter s n) (hge : m ≥ n) :
    sumVals s n = sumVals s m :=
  by
  have h := sumVals_split s n (m - n)
  have hdiff : m = n + (m - n) := by omega
  rw [hdiff, h]
  rw [sumVals_zero (drop _ _)]; abel
  intro t; unfold drop; apply hz; omega

theorem sumVals_eq_helper (s : stream a) (n1 n2 : ℕ) (hz1 : ZeroAfter s n1): n1 ≤ n2 → sumVals s n1 = sumVals s n2 :=
  by
  intro hle
  rw [sumVals_zero_ge]
  assumption
  omega

theorem sumVals_eq (s : stream a) (n1 n2 : ℕ) (hz1 : ZeroAfter s n1) (hz2 : ZeroAfter s n2) :
    sumVals s n1 = sumVals s n2 := by
  by_cases n1 ≤ n2
  · rw [sumVals_eq_helper] <;> assumption
  · symm; rw [sumVals_eq_helper]; assumption; omega

noncomputable def streamElim (s : stream a) : a :=
  match Classical.propDecidable (∃ n, ZeroAfter s n) with
  | Decidable.isTrue h => sumVals s (Classical.choose h)
  | Decidable.isFalse _ => 0

theorem streamElim_zeroAfter (s : stream a) (n : ℕ) (pf : ZeroAfter s n) :
    streamElim s = sumVals s n := by
  unfold streamElim
  cases Classical.propDecidable _ <;> rename_i h
  · exfalso
    apply h; use n
  · simp
    apply sumVals_eq
    · apply Classical.choose_spec h
    · assumption

notation "∫0" => streamElim

@[simp]
theorem streamElim_0 : ∫0 (0 : stream a) = 0 :=
  by
  rw [streamElim_zeroAfter _ 0]
  · simp
  · intro t heq; simp

theorem streamElim_delta (x : a) : ∫0 (δ0 x) = x :=
  by
  rw [streamElim_zeroAfter _ 1]
  simp
  apply δ0_ZeroAfter

theorem delta_linear : ∀ x y : a, δ0 (x + y) = δ0 x + δ0 y :=
  by
  introv
  funext t; simp
  split_ifs <;> simp

theorem sumVals_linear (s1 s2 : stream a) (n : ℕ) :
    sumVals (s1 + s2) n = sumVals s1 n + sumVals s2 n :=
  by
  induction' n with n n_ih <;> simp
  rw [n_ih]; abel

theorem sum_zeroAfter {s1 s2 : stream a} {n1 : ℕ} (pf1 : ZeroAfter s1 n1) {n2 : ℕ}
    (pf2 : ZeroAfter s2 n2) : ZeroAfter (s1 + s2) (if n1 ≥ n2 then n1 else n2) :=
  by
  split_ifs
  · intro m hge; simp
    rw [pf1]; swap; omega
    rw [pf2]; swap; omega
    simp
  · intro m hge; simp
    rw [pf1]; swap; omega
    rw [pf2]; swap; omega
    simp

theorem streamElim_linear (s1 s2 : stream a) (n1 : ℕ) (pf1 : ZeroAfter s1 n1) (n2 : ℕ)
    (pf2 : ZeroAfter s2 n2) : ∫0 (s1 + s2) = ∫0 s1 + ∫0 s2 := by
  rw [streamElim_zeroAfter s1 _ pf1]
  rw [streamElim_zeroAfter s2 _ pf2]
  rw [streamElim_zeroAfter _ _ (sum_zeroAfter pf1 pf2)]
  simp
  generalize hmax : (if n2 ≤ n1 then n1 else n2) = maxn
  have hmax1 : maxn ≥ n1 := by subst hmax; split_ifs <;> omega
  have hmax2 : maxn ≥ n2 := by subst hmax; split_ifs <;> omega
  rw [sumVals_zero_ge s1 _ maxn pf1]; swap; omega
  rw [sumVals_zero_ge s2 _ maxn pf2]; swap; omega
  apply sumVals_linear

theorem streamElim_timeInvariant : TimeInvariant (↑↑(@streamElim a _)) := by
  apply lifting_timeInvariant; simp

theorem integral_zero (s : stream a) (n : ℕ) : ZeroAfter (I s) n → ZeroAfter s n.succ := by
  intro hz
  intro m hge
  have hm := hz m (by omega)
  rw [integral_unfold] at hm; simp at hm
  have hm' : z⁻¹ (I s) m = I s (m - 1) := by unfold delay; rw [if_neg]; omega
  rw [hm'] at hm
  rw [hz (m - 1)] at hm
  simp at hm; assumption
  omega

theorem integral_nested_unfold (s : stream (stream a)) (t : ℕ) :
    0 < t → I s t = s t + I s (t - 1) := by
  intro hnz
  conv_lhs =>
    rw [integral_unfold]
    simp
  simp
  rw [delay_sub_1]; omega

-- stream_elim_incremental is not provable
example {a : Type} [AddCommGroup a] : True :=
  by
  have h : (↑↑(@streamElim a _))^Δ = ↑↑streamElim :=
    by
    unfold incremental
    funext s
    unfold D
    funext t; simp
    by_cases ht : t = 0
    · subst t; simp
    rw [delay_sub_1]; swap; omega; simp
    -- this is not true: ∫0 (I s t) might converge while ∫0 (I s (t-1)) diverges and
    -- ∫0 (s t) converges for example. What does seem true is that if both
    -- integrals on the left hand side converge, then the right-hand side
    -- converges and the equality holds.
    by_cases h: ∃ n, ZeroAfter (I s t) n
    · cases' h with n hz
      sorry
    -- this doesn't seem true
    sorry
  trivial

theorem integral_delta (x : a) : I (δ0 x) = fun _n => x := by
  funext t
  induction t
  · simp
  · rw [integral_unfold]; simp; assumption

@[simp]
theorem integral_delta_apply (x : a) (n : ℕ) : I (δ0 x) n = x := by rw [integral_delta]

variable {b : Type} [AddCancelCommMonoid b]

theorem nested_zpp (Q : Operator a b) : TimeInvariant Q → ∫0 (Q (δ0 0)) = 0 := by
  intro hti
  rw [δ0_0]
  rw [timeInvariant_zpp _ hti]
  rw [streamElim_0]

variable {c: Type} [AddCommGroup c]

lemma ZeroAfter_neg {s: stream c} {n: ℕ}:
    ZeroAfter (-s) n ↔ ZeroAfter s n := by
  constructor <;> intro h
  · intro m hm
    specialize h m hm
    simp at h; assumption
  · intro m hm; simp
    apply h; assumption

theorem streamElim_neg (s : stream c) : ∫0 (-s) = -∫0 s := by
  by_cases hz : ∃ n, ZeroAfter s n
  · cases' hz with n hz
    rw [streamElim_zeroAfter _ _ hz]
    rw [streamElim_zeroAfter _ _ (ZeroAfter_neg.2 hz)]
    simp
  · have hz2 : ¬∃ n, ZeroAfter (-s) n := by
      simp; intro x; rw [ZeroAfter_neg]
      tauto
    unfold streamElim
    split <;> rename_i h1
    · contradiction
    · split <;> rename_i h2
      · contradiction
      · simp

theorem sub_zeroAfter {s1 s2 : stream c} {n1 : ℕ} (pf1 : ZeroAfter s1 n1) {n2 : ℕ}
    (pf2 : ZeroAfter s2 n2) : ZeroAfter (s1 - s2) (if n1 ≥ n2 then n1 else n2) :=
  by
  split_ifs
  · intro m hge; simp
    rw [pf1]; swap; omega
    rw [pf2]; swap; omega
    simp
  · intro m hge; simp
    rw [pf1]; swap; omega
    rw [pf2]; swap; omega
    simp

@[simp]
theorem delta_incremental : ↑↑(@δ0 c _)^Δ = ↑↑δ0 :=
  by
  apply lti_incremental
  apply lifting_lti
  apply delta_linear

theorem integral_zero' (s : stream (stream c)) (t n : ℕ) :
    ZeroAfter (I s t) n → ZeroAfter (I s (t - 1)) n → ZeroAfter (s t) n.succ :=
  by
  by_cases t = 0
  · subst t; simp; intro hz _hz'
    apply ZeroAfter_ge hz; omega
  intro hz hz'
  intro m hge
  trans D (I s) t m
  · simp
  unfold D; simp
  rw [hz m]; swap; omega
  rw [delay_sub_1]; swap; omega
  rw [hz' m]; swap; omega
  abel

end sumVals

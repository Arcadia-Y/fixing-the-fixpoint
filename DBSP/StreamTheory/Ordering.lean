-- Copyright 2022-2023 VMware, Inc.
import DBSP.StreamTheory.Linear

-- SPDX-License-Identifier: BSD-2-Clause
variable {a : Type} [AddCommGroup a] [PartialOrder a] [IsOrderedAddMonoid a]

def Positive (s : stream a) :=
  0 ≤ s

def StreamMonotone (s : stream a) :=
  ∀ t, s t ≤ s (t + 1)

def IsPositive {b : Type} [AddCommGroup b] [PartialOrder b] [IsOrderedAddMonoid b] (f : stream a → stream b) :=
  ∀ s, Positive s → Positive (f s)

-- TODO: could not get library monotone definition to work, possibly due to
-- partial_order.to_preorder?
-- set_option pp.notation false.
-- set_option pp.implicit true.
-- prove that [stream_monotone] can be rephrased in terms of order preservation
omit [AddCommGroup a] [IsOrderedAddMonoid a] in
theorem streamMonotone_order (s : stream a) : StreamMonotone s ↔ ∀ t1 t2, t1 ≤ t2 → s t1 ≤ s t2 :=
  by
  unfold StreamMonotone; constructor <;> intro h <;> introv
  · intro hle; have heq : t2 = t1 + (t2 - t1) := by omega
    rw [heq] at *
    generalize t2 - t1 = d
    clear! t2
    induction' d with d_n
    · simp
    · trans s (t1 + d_n); assumption
      apply h
  · apply h; linarith

theorem integral_monotone (s : stream a) : Positive s → StreamMonotone (I s) :=
  by
  intro hp
  intro t
  repeat' rw [integral_sumVals]
  repeat' simp [sumVals]
  have h := hp (t + 1); simp at h
  assumption

theorem derivative_pos
    (s : stream a) :-- NOTE: paper is missing this, but it is also necessary (maybe they
        -- intend `s[-1] =0` in the definition of monotone)
        0 ≤
        s 0 →
      StreamMonotone s → Positive (D s) :=
  by
  intro h0 hp; intro t ; simp
  unfold D delay ; simp
  split_ifs
  · subst t; assumption
  · have hle := hp (t - 1)
    have heq : t - 1 + 1 = t := by omega
    rw [heq] at hle
    assumption

omit [IsOrderedAddMonoid a] in
theorem derivative_pos_counter_example :
    (∃ x : a, x < 0) → ¬∀ s : stream a, StreamMonotone s → Positive (D s) :=
  by
  intro h; cases' h with x hneg
  simp
  -- pushing the negation through, we're going to prove
  -- ∃ (x : stream a), stream_monotone x ∧ ¬positive (D x)
  use fun _n => x
  constructor
  · intro t; simp
  · unfold Positive
    rw [stream_le_ext]; simp
    use 0; simp [D]
    apply not_le_of_gt; assumption

-- Copyright 2022-2023 VMware, Inc.
import DBSP.ZSets.Relational

-- SPDX-License-Identifier: BSD-2-Clause
open Zset

section count

variable {a : Type} [DecidableEq a]

def count (m : Z[a]) : ℤ :=
  m.support.sum fun a => m a

def count' : Z[a] → Z[ℤ] := fun m => {count m}

theorem count_ok (s : Finset a) : count (Zset.fromSet s) = s.card :=
  by
  unfold count Zset.fromSet
  simp [DFinsupp.coe_finset_sum]
  rw [<- DFinsupp.toFun_eq_coe]; simp
  congr 1
  ext a; simp

theorem count_linear (m1 m2 : Z[a]) : count (m1 + m2) = count m1 + count m2 :=
  by
  unfold count
  rw [add_support]
  -- simp only [Ne.def]
  rw [Finset.sum_filter_of_ne]; swap
  · intro x; simp
  conv_lhs =>
    congr
    · skip
    ext
    simp
    skip
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [sum_union_zero_l]; simp
  · rw [Finset.union_comm]
    rw [sum_union_zero_l]; simp

theorem count'_ok (s : Finset a): Zset.toSet (count' (Zset.fromSet s)) = {↑s.card} :=
  by
  unfold count' Zset.toSet
  rw [count_ok]
  simp

end count

namespace Zset

-- NOTE: this could be generalized to any vector space with ℤ as its constants
protected def sum (m : Z[ℚ]) : ℚ :=
  m.support.sum fun a => a * m a

def sum' : Z[ℚ] → Z[ℚ] := fun m => {Zset.sum m}

theorem sum_ok (s : Finset ℚ) : Zset.sum (Zset.fromSet s) = Finset.sum s fun a => a :=
  by
  unfold Zset.sum Zset.fromSet
  simp
  apply Finset.sum_congr
  · ext a; simp
  · intros;
    rw [<- DFinsupp.toFun_eq_coe]
    simp
    tauto

theorem sum_linear (m1 m2 : Z[ℚ]) : Zset.sum (m1 + m2) = Zset.sum m1 + Zset.sum m2 :=
  by
  unfold Zset.sum
  apply general_sum_linear fun a m => a * (↑m : ℚ)
  · intros; simp
  · intros; simp; rw [mul_add]

theorem sum'_ok (s : Finset ℚ) : Zset.toSet (sum' (Zset.fromSet s)) = {Finset.sum s fun a => a} :=
  by
  unfold sum' Zset.toSet
  rw [sum_ok]
  simp

end Zset

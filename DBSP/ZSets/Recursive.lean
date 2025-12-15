-- Copyright 2022-2023 VMware, Inc.
import DBSP.ZSets.Relational
import DBSP.ZSets.RelationalIncremental
import DBSP.StreamTheory.StreamElim
import Mathlib.Logic.Function.Iterate

-- SPDX-License-Identifier: BSD-2-Clause
open Zset

section Recursion

variable {a : Type}

variable [DecidableEq a]

-- idea is that we're supposed to compute O such that R(O) = O
variable (R : Z[a] → Z[a])

private def approxs : stream Z[a] :=
  fix fun o : stream Z[a] => (↑↑R) (z⁻¹ o)

omit [DecidableEq a] in
theorem approxs_unfold : approxs R = (↑↑R) (z⁻¹ (approxs R)) :=
  by
  unfold approxs
  apply fix_eq
  apply causal_strict_strict; swap; simp
  apply delay_strict

noncomputable def recursiveFixpoint : Z[a] :=
  ∫0 (D (approxs R))

omit [DecidableEq a] in
theorem approxs_apply (n : ℕ) : approxs R n = (R^[n.succ]) 0 :=
  by
  induction' n with _ n_ih; simp
  · unfold approxs
    rw [fix_0]; simp
  · rw [approxs_unfold]; simp
    rw [n_ih]; simp
    repeat' rw [Function.Commute.iterate_self R]

omit [DecidableEq a] in
theorem approxs_unfold_succ (n : ℕ) : approxs R n.succ = R (approxs R n) :=
  by
  rw [approxs_apply]
  rw [approxs_apply]
  simp
  rw [Function.Commute.iterate_self R]

omit [DecidableEq a] in
private lemma eq_succ_is_fixpoint (n : ℕ) (heqn : R^[n.succ] 0 = R^[n] 0) :
    ∀ m ≥ n, R^[m] 0 = R^[n] 0 := by
  intro m hge
  by_cases m = n
  · cc
  generalize hdiff : m - n - 1 = d
  have hm : m = (n + d).succ := by omega
  rw [hm]
  rw [hm] at *
  clear! m
  induction' d with d_n d_ih
  · simp; assumption
  · have hnsucc : (n + d_n.succ) = (n + d_n).succ := by omega
    simp
    rw [Function.Commute.iterate_self]
    rw [hnsucc, d_ih] <;> try simp
    simp at heqn
    rw [Function.Commute.iterate_self] at heqn
    apply heqn

omit [DecidableEq a] in
theorem derivative_approx_almost_zero (n : ℕ) (heqn : (R^[n.succ]) 0 = (R^[n]) 0) :
    ZeroAfter (D (approxs R)) n.succ := by
  intro m hge
  rw [derivative_difference_t]; swap; omega
  repeat' rw [approxs_apply]
  have heq : (m - 1).succ = m := by omega
  rw [heq]; clear heq
  rw [eq_succ_is_fixpoint _ n heqn m.succ]; swap; omega
  rw [eq_succ_is_fixpoint _ n heqn m]; swap; omega
  simp

omit [DecidableEq a] in
theorem recursiveFixpoint_ok (n : ℕ) (heqn : (R^[n.succ]) 0 = (R^[n]) 0) :
    recursiveFixpoint R = (R^[n]) 0 :=
  by
  unfold recursiveFixpoint
  rw [streamElim_zeroAfter (D (approxs R)) n.succ]
  · rw [← integral_sumVals]
    simp
    rw [approxs_apply]; dsimp
    exact heqn
  apply derivative_approx_almost_zero _ n heqn

end Recursion

section seminaive

variable {a b : Type}

variable [DecidableEq a] [DecidableEq b]

variable (R : Z[b] → Z[a] → Z[a])

noncomputable def naive : Z[b] → Z[a] := fun i =>
  ∫0 (D (fix fun o : stream Z[a] => (↑²R) (I (δ0 i)) (z⁻¹ o)))

noncomputable def seminaive : Z[b] → Z[a] := fun i =>
  ∫0 (fix fun o : stream Z[a] => (↑²R^Δ2) (δ0 i) (z⁻¹ o))

omit [DecidableEq a] [DecidableEq b] in
theorem seminaive_equiv : seminaive R = naive R :=
  by
  ext x
  unfold naive seminaive
  congr 1
  congr 1
  conv => rhs; change
    ((fun i => fix fun o : stream Z[a] => (↑²R) i (z⁻¹ o))^Δ) (δ0 x)
  rw [cycle_incremental fun i o => (↑²R) i o]
  unfold uncurryOp; simp

omit [DecidableEq a] [DecidableEq b] in
theorem naive_ok (i : Z[b]) (n : ℕ) (heqn : ((R i)^[n.succ]) 0 = ((R i)^[n]) 0) :
    naive R i = ((R i)^[n]) 0 := by
  unfold naive
  have heq := (recursiveFixpoint_ok (R i)) _ heqn
  unfold recursiveFixpoint approxs at heq
  rw [← heq]
  congr 1
  apply congr; simp
  apply congr; simp
  funext o
  funext t; simp

omit [DecidableEq a] [DecidableEq b] in
theorem seminaive_ok (i : Z[b]) (n : ℕ) (heqn: (R i)^[n.succ] 0 = ((R i)^[n]) 0) :
  seminaive R i = ((R i)^[n]) 0 := by
  rw [seminaive_equiv]
  apply naive_ok; assumption

end seminaive

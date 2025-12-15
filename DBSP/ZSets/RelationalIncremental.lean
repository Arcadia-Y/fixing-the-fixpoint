-- Copyright 2022-2023 VMware, Inc.
import DBSP.ZSets.Relational
import DBSP.StreamTheory.Incremental

-- SPDX-License-Identifier: BSD-2-Clause
open Zset

variable {A B C : Type}

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

def distinctHAt (i d : Z[A]) : A → ℤ := fun x =>
  if 0 < i x ∧ (i + d) x ≤ 0 then -1 else if i x ≤ 0 ∧ 0 < (i + d) x then 1 else 0

def distinctH (i d : Z[A]) : Z[A] :=
  DFinsupp.mk (i.support ∪ d.support) fun x => distinctHAt i d x

@[simp]
theorem distinctH_apply (i d : Z[A]) (x : A) : distinctH i d x = distinctHAt i d x :=
  by
  unfold distinctH; rw [<- DFinsupp.toFun_eq_coe]; simp
  intro h1 h2
  simp [distinctHAt]; split_ifs <;> omega

def distinctIncremental : stream Z[A] → stream Z[A] := fun d => (↑²distinctH) (z⁻¹ (I d)) d

theorem distinctIncremental_ok : ↑↑distinct^Δ = @distinctIncremental A _ :=
  by
  funext d
  unfold incremental distinctIncremental
  unfold D
  conv_lhs =>
    congr
    · rw [integral_unfold]
      skip
    ·skip
  rw [← lifting_timeInvariant]; swap; simp
  repeat' rw [← integral_timeInvariant]
  funext t; ext a; unfold lifting2; simp
  generalize hi : I (z⁻¹ d) t = i
  generalize hd : d t = d_t
  clear hi hd d t
  unfold distinctHAt
  simp
  -- canonicalize the tests a little bit so splitting produces fewer cases
  repeat' rw [← ite_ite]
  split_ifs <;>
    first
    | rfl
    | · exfalso; omega

@[simp]
theorem flatmap_incremental (f : A → Z[B]) : ↑↑(Zset.flatmap f)^Δ = ↑↑(Zset.flatmap f) :=
  by
  apply lti_incremental
  apply lifting_lti
  apply flatmap_linear

@[simp]
theorem map_incremental (f : A → B) : ↑↑(Zset.map f)^Δ = ↑↑(Zset.map f) :=
  flatmap_incremental _

@[simp]
theorem lifting_map_incremental {A B} [DecidableEq A] [DecidableEq B] (f : A → B) :
    ↑↑↑↑(Zset.map f)^Δ = ↑↑↑↑(Zset.map f) :=
  by
  rw [lti_incremental]
  apply lifting_lti
  intro x y; rw [lifting_linear]; apply map_linear

@[simp]
theorem map_incremental_unfolded (f : A → B) (s : stream Z[A]) :
    D ((↑↑(Zset.map f)) (I s)) = (↑↑(Zset.map f)) s :=
  by
  conv_rhs => rw [← map_incremental]
  rw [incremental_unfold]

theorem equiJoin_incremental (π1 : A → C) (π2 : B → C) :
    ↑²(equiJoin π1 π2)^Δ2 = timesIncremental (↑²(equiJoin π1 π2)) :=
  by
  rw [bilinear_incremental (↑²(equiJoin π1 π2))]
  · rw [lifting2_timeInvariant]
    rfl
  · apply lifting_bilinear
    apply equiJoin_bilinear

@[simp]
theorem filter_incremental (p : A → Prop) [DecidablePred p] : ↑↑(filter p)^Δ = ↑↑(filter p) :=
  by
  apply lti_incremental
  apply lifting_lti
  apply filter_linear

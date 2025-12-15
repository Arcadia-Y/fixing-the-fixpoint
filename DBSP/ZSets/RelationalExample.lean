-- Copyright 2022-2023 VMware, Inc.
import DBSP.StreamTheory.Incremental
import DBSP.ZSets.Relational
import DBSP.ZSets.RelationalIncremental

-- SPDX-License-Identifier: BSD-2-Clause
open Zset

class Schema where
  -- the schemas for the two tables, T and R
  (T R : Type)
  -- t.a > 2
  -- r.s > 5
  σT : T → Prop
  σR : R → Prop
  -- the type of t1.x, t2.y, and the common id field
  (T1X T2Y Id : Type)
  π1 : T → T1X × Id
  π2 : R → Id × T2Y

def πxy (S : Schema) (t : (S.T1X × S.Id) × S.Id × S.T2Y) : S.T1X × S.T2Y :=
  (t.1.1, t.2.2)

class SchemaOk (S : Schema) where
  i1 : DecidableEq S.T
  i2 : DecidableEq S.R
  i3 : DecidablePred S.σT
  i4 : DecidablePred S.σR
  i5 : DecidableEq S.T1X
  i6 : DecidableEq S.T2Y
  i7 : DecidableEq S.Id

section Instances

open SchemaOk

attribute [instance] i1 i2 i3 i4 i5 i6 i7

end Instances

variable (S : Schema) [SchemaOk S]

def t1 : Z[S.T] → Z[S.T1X × S.Id] := fun t =>
  Zset.distinct (Zset.map S.π1 (Zset.distinct (filter S.σT (Zset.distinct t))))

def t2 : Z[S.R] → Z[S.Id × S.T2Y] := fun r =>
  Zset.distinct (Zset.map S.π2 (Zset.distinct (filter S.σR (Zset.distinct r))))

def v : Z[S.T] → Z[S.R] → Z[S.T1X × S.T2Y] := fun t r =>
  Zset.distinct (Zset.map (πxy S) (equiJoin Prod.snd Prod.fst (t1 S t) (t2 S r)))

-- set up optimizations
-- pos_equiv says f1 and f2 are equivalent on positive inputs
def PosEquiv {A B : Type} [DecidableEq A] [DecidableEq B] (f1 f2 : Z[A] → Z[B]) :=
  ∀ i, IsBag i → f1 i = f2 i

def PosEquiv2 {A B C : Type} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (f1 f2 : Z[A] → Z[B] → Z[C]) :=
  ∀ i1 i2, IsBag i1 → IsBag i2 → f1 i1 i2 = f2 i1 i2

infixl:50 " =≤= " => PosEquiv

infixl:50 " =≤2= " => PosEquiv2

/-- `same` is a technical device for automation purposes. It is just equality,
  but marked irreducible.

  The way this is used is that we can work on a goal `same x ?y` (where `?y` is
  an existential variable), gradually rewriting x to simplify it. If we tried to
  prove `x = ?y`, then `rw` an `simp` would always try to instantiate ?y with x,
  even if we want to continue rewriting.

  To make intermediate goals readable we provide `x === y` as notation for `same
  x y`.
   -/
def Same {A : Type} (x y : A) :=
  x = y

theorem same_def {A} (x y : A) : Same x y = (x = y) :=
  rfl

theorem same_intro {A : Type} (x y : A) : Same x y → x = y := by rw [same_def]; tauto

theorem same_elim {A : Type} (x : A) : Same x x := by rw [same_def]

infixl:50 " === " => Same

structure Sig (A : Type) (p : A → Prop) where
  witness : A
  pf : p witness

def t1OptGoal : Sig (Z[S.T] → Z[S.T1X × S.Id]) fun opt => t1 S =≤= opt :=
  by
  econstructor
  intro t hpos
  apply same_intro
  simp [t1]
  rw [filter_distinct_dedup]
  rw [map_distinct_dedup]
  swap; · apply filter_pos; assumption
  apply same_elim

-- TODO: reduce this first
def t1Opt :=
  (t1OptGoal S).witness

def t1Opt_ok : t1 S =≤= t1Opt S :=
  (t1OptGoal S).pf

def t2OptGoal : Sig (Z[S.R] → Z[S.Id × S.T2Y]) fun opt => t2 S =≤= opt :=
  by
  econstructor
  intro t hpos
  apply same_intro
  simp [t2]
  rw [filter_distinct_dedup]
  rw [map_distinct_dedup]
  swap; · apply filter_pos; assumption
  apply same_elim

def vOptGoal : Sig (Z[S.T] → Z[S.R] → Z[S.T1X × S.T2Y]) fun opt => v S =≤2= opt :=
  by
  econstructor; intro i1 i2 hpos1 hpos2
  apply same_intro
  simp [v]
  rw [(t1OptGoal S).pf _ (by assumption)]
  rw [(t2OptGoal S).pf _ (by assumption)]
  simp [t1OptGoal, t2OptGoal]
  rw [join_distinct_comm]; rotate_left
  · apply map_pos; apply filter_pos; assumption
  · apply map_pos; apply filter_pos; assumption
  rw [map_distinct_dedup]; rotate_left
  · apply equiJoin_pos <;> apply map_pos <;> apply filter_pos <;> assumption
  apply same_elim

-- The optimized ℤ-set query from the paper
def vopt (t1 : Z[S.T]) (t2 : Z[S.R]) :=
  distinct <|
    Zset.map (πxy S)
      (equiJoin Prod.snd Prod.fst (Zset.map Schema.π1 (filter Schema.σT t1))
        (Zset.map Schema.π2 (filter Schema.σR t2)))

-- the simplifications above produce exactly what's in the paper
theorem v_opt_ok : v S =≤2= vopt S :=
  (vOptGoal S).pf

theorem v_lifted :
    ↑²(vopt S) = fun t1 t2 =>
      ↑↑distinct
        (↑↑(Zset.map (πxy S))
          (↑²(equiJoin Prod.snd Prod.fst)
            (↑↑(Zset.map Schema.π1) (↑↑(filter Schema.σT) t1))
            (↑↑(Zset.map Schema.π2) (↑↑(filter Schema.σR) t2)))) :=
  by rfl

-- This is the intermediate incremental circuit
def vΔ1 (t1 : stream Z[S.T]) (t2 : stream Z[S.R]) :=
  (↑↑distinct)^Δ <|
    ↑↑(Zset.map (πxy S)) <|
      (↑²(equiJoin Prod.snd Prod.fst)^Δ2)
        (↑↑(Zset.map Schema.π1) (↑↑(filter Schema.σT) t1))
        (↑↑(Zset.map Schema.π2) (↑↑(filter Schema.σR) t2))

theorem vΔ1_ok : ↑²(vopt S)^Δ2 = vΔ1 S := by
  funext t1 t2
  -- hide the right-hand side
  trans
  · apply same_intro
    rw [v_lifted]
    dsimp only [incremental2]
    repeat'
      first
      | rw [D_push2]
      | rw [D_push];
    simp
    apply same_elim
  · rfl

def vΔ (t1 : stream Z[S.T]) (t2 : stream Z[S.R]) :=
  distinctIncremental <|
    ↑↑(Zset.map <| πxy S) <|
      timesIncremental ↑²(equiJoin Prod.snd Prod.fst)
        (↑↑(Zset.map Schema.π1) (↑↑(filter Schema.σT) t1))
        (↑↑(Zset.map Schema.π2) (↑↑(filter Schema.σR) t2))

theorem vΔ_ok : ↑²(vopt S)^Δ2 = vΔ S := by
  rw [vΔ1_ok]; funext t1 t2; unfold vΔ1
  rw [distinctIncremental_ok]
  rw [equiJoin_incremental]
  rfl

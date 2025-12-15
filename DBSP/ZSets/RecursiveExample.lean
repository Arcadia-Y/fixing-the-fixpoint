-- Copyright 2022-2023 VMware, Inc.
import DBSP.ZSets.Relational
import DBSP.ZSets.RelationalIncremental
import DBSP.ZSets.Recursive
import DBSP.StreamTheory.Linear
import DBSP.StreamTheory.Operators

-- SPDX-License-Identifier: BSD-2-Clause
open Zset

variable {Node : Type} [DecidableEq Node]

def Edge (Node : Type) :=
  Node × Node

instance : DecidableEq (Edge Node) := by apply instDecidableEqProd

-- get a self-edge for the head
def πh (input : Edge Node) : Edge Node :=
  (input.1, input.1)

-- get a self-edge for the tail
def πt (input : Edge Node) : Edge Node :=
  (input.2, input.2)

def πht (x : Edge Node × Edge Node) : Edge Node :=
  let r1 := x.1
  let e := x.2
  (r1.1, e.2)

local prefix:999 "↑" => lifting

def closure1 (E R1 : Z[Edge Node]) : Z[Edge Node] :=
  distinct <| Zset.map πht (equiJoin Prod.snd Prod.fst R1 E) + E + Zset.map πh E + Zset.map πt E

theorem lifting_closure1_eq (E R1 : stream Z[Edge Node]) :
    (↑²closure1) E R1 =
      (↑distinct)
        ((↑Zset.map πht) (↑²(equiJoin Prod.snd Prod.fst) R1 E) + E + (↑Zset.map πh) E +
          (↑Zset.map πt) E) :=
  rfl


noncomputable def closure0 : Z[Edge Node] → Z[Edge Node] :=
  naive closure1

noncomputable def closureSeminaive : Z[Edge Node] → Z[Edge Node] := fun E =>
  let E := δ0 E
  ∫0 <|
    fix fun R =>
      (↑distinct^Δ)
        ((↑Zset.map πht) ((↑²(equiJoin Prod.snd Prod.fst)^Δ2) (z⁻¹ R) E) + E + (↑Zset.map πh) E +
          (↑Zset.map πt) E)

set_option maxHeartbeats 400000

theorem closure_efficient_ok : @closureSeminaive Node _ = closure0 :=
  by
  unfold closure0
  symm
  rw [← seminaive_equiv]
  funext E
  unfold closureSeminaive seminaive
  dsimp
  congr 1
  apply congr; simp
  funext R1
  conv_lhs =>
    simp [incremental2]
    rw [lifting_closure1_eq]
    skip
  rw [D_push]; apply congr; simp
  repeat' rw [derivative_linear]; simp
  rw [D_push]; simp
  rw [incremental2_unfold]



noncomputable def incrementalClosure : Operator Z[Edge Node] Z[Edge Node] :=
  incremental fun dE =>
    let E := (↑δ0) dE
    (↑∫0) <|
      fix2 fun R =>
        (↑((↑distinct)^Δ))
        ((((↑(↑↑(Zset.map πht))) ((↑²((↑²(equiJoin Prod.snd Prod.fst)^Δ2))) ((↑z⁻¹) R) E) +
          E) +
          (↑(↑↑(Zset.map πh))) E) +
        (↑(↑↑(Zset.map πt))) E)


attribute [local simp] sum_causal causal_comp_causal

theorem incrementalClosure_ok : @incrementalClosure Node _ = ↑closure0^Δ :=
  by
  funext EΔ
  unfold incrementalClosure; unfold incremental; dsimp
  rw [← closure_efficient_ok]
  generalize heq : I EΔ = E; clear! EΔ
  apply congr; simp
  conv =>
    rhs
    change
    (↑∫0) ((↑(fun (E : stream (Z[Edge Node])) => fix (fun (R : stream (Z[Edge Node])) => ((↑distinct)^Δ) ((((↑(Zset.map πht)) (((↑²(equiJoin Prod.snd Prod.fst))^Δ2) (z⁻¹ R) E) + E) + (↑(Zset.map πh)) E) + (↑(Zset.map πt)) E)))) ((↑δ0) E))
  have := lifting_cycle fun E R : stream Z[Edge Node] =>
        ((↑distinct)^Δ)
          ((↑(Zset.map πht)) (((↑²(equiJoin Prod.snd Prod.fst))^Δ2) R E) + E + (↑(Zset.map πh)) E +
            (↑(Zset.map πt)) E)
  rw [this]
  · simp
    congr 2
  unfold uncurryOp; simp
  apply causal_comp_causal <;> try simp
  apply sum_causal <;> try simp
  apply sum_causal <;> try simp
  apply sum_causal <;> simp

noncomputable def incrementalClosure2 : Operator Z[Edge Node] Z[Edge Node] := fun dE =>
  let E : stream (stream (Z[Edge Node])) := (↑δ0) dE
  ((↑↑∫0)^Δ)
    (fix2
      (fun (R : stream (stream (Z[Edge Node]))) =>
          ((↑↑((↑↑distinct)^Δ))^Δ)
            ((((↑(↑↑(Zset.map πht)))
                (((↑²((↑²(equiJoin Prod.snd Prod.fst))^Δ2))^Δ2) ((↑z⁻¹) R) E) +
              E) +
              (↑(↑↑(Zset.map πh))) E) +
            (↑(↑↑(Zset.map πt))) E)))

theorem
  fix2_congr
  { a : Type } [ AddCommGroup a ] ( F1 F2 : Operator (stream a) (stream a) )
    : F1 = F2 → fix2 F1 = fix2 F2
  := by cc

@[simp]
theorem lifting_map_πht_incremental : ↑↑(↑↑(Zset.map (@πht Node)))^Δ = ↑↑(↑↑(Zset.map πht)) := by
  apply lifting_map_incremental

theorem incrementalClosure2_ok : @incrementalClosure2 Node _ = (↑closure0)^Δ :=
  by
  rw [← incrementalClosure_ok]
  funext dE; simp [incrementalClosure, incrementalClosure2]
  symm
  rw [incremental_comp (↑↑∫0 ) _ dE]
  apply congr; simp
  have := cycle2_incremental fun (s: stream (Z[Edge Node])) (R : stream (stream Z[Edge Node])) =>
      (↑↑((↑↑distinct)^Δ))
    ((((↑↑(↑↑(Zset.map πht))) ((↑²((↑²(equiJoin Prod.snd Prod.fst))^Δ2)) R ((↑↑δ0) s)) + (↑↑δ0) s) +
      (↑↑(↑↑(Zset.map πh))) ((↑↑δ0) s)) +
     (↑↑(↑↑(Zset.map πt))) ((↑↑δ0) s))
  rw [this] <;> clear this
  dsimp
  apply fix2_congr; funext R
  rw [incremental2_unfold _ dE]
  rw [D_push]
  apply congr; simp
  · rw [derivative_linear]
    rw [derivative_linear]
    rw [derivative_linear]
    rw [D_push]; simp
    rw [D_push2]; simp
    rw [D_push]; simp
    rw [D_push]; simp
    rw [D_push]; simp
    rw [D_push]; simp
    rw [D_push]; simp
  -- need to prove causal_nested
  · intro s;
    apply causalNested_comp <;> try simp
    apply sum_causalNested <;> try simp
    apply sum_causalNested <;> try simp
    apply sum_causalNested <;> try simp
    apply causalNested_comp; try simp
    apply causalNested_lifting2 <;> try simp
    · unfold uncurryOp
      apply causal_lifting2_incremental <;> simp
    · apply causalNested_id

def distinctDoubleIncremental {A : Type} [DecidableEq A] : Operator (stream Z[A]) (stream Z[A]) :=
  fun i => D <| ↑²↑²(@distinctH A _) ((↑z⁻¹) ((↑I) (I i))) (I i)

theorem distinctDoubleIncremental_ok {A : Type} [DecidableEq A] :
    ↑↑(↑↑(@distinct A _)^Δ)^Δ = distinctDoubleIncremental :=
  by
  funext s
  unfold distinctDoubleIncremental
  rw [distinctIncremental_ok]
  unfold distinctIncremental
  rw [incremental_unfold]
  rfl

section equiJoin

variable {A B C : Type}

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

variable (π1 : A → C) (π2 : B → C)

local notation:40 x "▹◃" y => lifting2 (lifting2 (equiJoin x y))

def joinDoubleIncremental1 : Operator2 (stream Z[A]) (stream Z[B]) (stream Z[A × B]) :=
  fun a b =>
  (↑²↑²(equiJoin π1 π2)^Δ2) a b + (↑²↑²(equiJoin π1 π2)^Δ2) (↑↑z⁻¹ <| ↑I <| a) b +
    (↑²↑²(equiJoin π1 π2)^Δ2) a (↑↑z⁻¹ <| ↑I <| b)

@[simp]
theorem lifting_i_delay_incremental {a : Type} [AddCommGroup a] :
    incremental (↑↑fun x : stream a => I (z⁻¹ x)) = ↑↑fun x => I (z⁻¹ x) :=
  by
  apply lti_incremental
  apply lifting_lti
  intro s1 s2
  rw [delay_linear, integral_linear]

omit [DecidableEq A] in
theorem lifting_i_delay_simplify (s : stream (stream Z[A])) :
    (↑↑fun x => I (z⁻¹ x)) s = (↑↑z⁻¹) ((↑↑I) s) :=
  by
  rw [← lifting_comp]
  funext t; simp
  rw [integral_timeInvariant]

theorem joinDoubleIncremental1_ok : ↑²(↑²(equiJoin π1 π2)^Δ2)^Δ2 = joinDoubleIncremental1 π1 π2 :=
  by
  unfold joinDoubleIncremental1
  rw [equiJoin_incremental]; unfold timesIncremental
  funext a b
  rw [lifting2_incremental_sum]
  rw [lifting2_incremental_sum]
  simp
  rw [lifting2_incremental_comp_1 _ fun x : stream Z[A] => I (z⁻¹ x)]
  rw [lifting2_incremental_comp_2 _ fun y : stream Z[B] => I (z⁻¹ y)]
  simp
  rw [lifting_i_delay_simplify]
  rw [lifting_i_delay_simplify]

-- this is the fully optimized circuit
def joinDoubleIncremental : Operator2 (stream Z[A]) (stream Z[B]) (stream Z[A × B]) := fun a b =>
  let join := ↑²↑²(equiJoin π1 π2)
  join (z⁻¹ (I a)) (↑z⁻¹ <| (↑I) b) + join (I <| ↑I <| a) b + join ((↑I) a) (z⁻¹ <| I b) +
    join a (↑z⁻¹ <| I <| (↑I) b)

theorem equiJoin_lifting2_time_invariant :
    ∀ s1 s2, z⁻¹ ((↑²↑²(equiJoin π1 π2)) s1 s2) = (↑²↑²(equiJoin π1 π2)) (z⁻¹ s1) (z⁻¹ s2) :=
  by
  intro s1 s2
  funext n t; simp
  unfold delay; split_ifs <;> simp

theorem equiJoin_double_lift_bilinear : Bilinear (↑²↑²(equiJoin π1 π2)) :=
  by
  constructor <;> intros
  · funext n t; simp; rw [(equiJoin_bilinear _ _).1]
  · funext n t; simp; rw [(equiJoin_bilinear _ _).2]

theorem equiJoin_i_1 :
    ∀ a b,
      (↑²↑²(equiJoin π1 π2)) (I a) b =
        (↑²↑²(equiJoin π1 π2)) a b + (↑²↑²(equiJoin π1 π2)) (z⁻¹ (I a)) b :=
  by
  intros
  conv_lhs => rw [integral_unfold]
  rw [(equiJoin_double_lift_bilinear _ _).1]

theorem equiJoin_lift_i_1 :
    ∀ a b,
      (↑²↑²(equiJoin π1 π2)) ((↑I) a) b =
        (↑²↑²(equiJoin π1 π2)) a b + (↑²↑²(equiJoin π1 π2)) ((↑I) ((↑z⁻¹) a)) b :=
  by
  intros
  funext n t; simp
  conv_lhs => rw [integral_unfold]
  simp
  rw [(equiJoin_bilinear _ _).1]
  rw [integral_timeInvariant]

theorem equiJoin_lift_i_2 :
    ∀ a b,
      (↑²↑²(equiJoin π1 π2)) a ((↑I) b) =
        (↑²↑²(equiJoin π1 π2)) a b + (↑²↑²(equiJoin π1 π2)) a ((↑I) ((↑z⁻¹) b)) :=
  by
  intros
  funext n t; simp
  conv_lhs => rw [integral_unfold]
  simp
  rw [(equiJoin_bilinear _ _).2]
  rw [integral_timeInvariant]

theorem equiJoin_i_2 :
    ∀ a b,
      (↑²↑²(equiJoin π1 π2)) a (I b) =
        (↑²↑²(equiJoin π1 π2)) a b + (↑²↑²(equiJoin π1 π2)) a (z⁻¹ (I b)) :=
  by
  intros
  conv_lhs => rw [integral_unfold]
  rw [(equiJoin_double_lift_bilinear _ _).2]

theorem equiJoin_i_unfold :
    ∀ a b,
      (↑²↑²(equiJoin π1 π2)) (I a) (I b) =
        (↑²↑²(equiJoin π1 π2)) a b + (↑²↑²(equiJoin π1 π2)) a (z⁻¹ (I b)) +
            (↑²↑²(equiJoin π1 π2)) (z⁻¹ (I a)) b +
          (↑²↑²(equiJoin π1 π2)) (z⁻¹ (I a)) (z⁻¹ (I b)) :=
  by
  intros
  repeat'
    first
    | rw [equiJoin_i_1]
    | rw [equiJoin_i_2]
  abel

private theorem neg_add_sub {α : Type} [AddCommGroup α] (x y : α) : (-1 : ℤ) • x + y = y - x := by
  abel

private theorem add_both_sides {G} [Add G] [IsRightCancelAdd G] (x : G) {a b : G} :
    a + x = b + x → a = b := by apply add_right_cancel

private theorem fold_join_helper :
    ∀ a b,
      (-1 : ℤ) • (π1▹◃π2) (I (z⁻¹ ((↑I) a))) b + (π1▹◃π2) (I (z⁻¹ ((↑I) ((↑z⁻¹) a)))) b =
        (-1 : ℤ) • (π1▹◃π2) (I (z⁻¹ a)) b :=
  by
  intros a b
  apply add_both_sides ((π1▹◃π2) (I (z⁻¹ a)) b)
  abel_nf
  rw [← add_assoc, add_comm]
  rw [neg_add_sub]
  rw [← add_sub_assoc]
  rw [← (equiJoin_double_lift_bilinear π1 π2).1]
  rw [← integral_linear]
  rw [← delay_linear]
  rw [← bilinear_sub_1 (equiJoin_double_lift_bilinear π1 π2)]
  rw [← linear_sub integral_linear]
  rw [← linear_sub delay_linear]
  have hz : a + (↑I) ((↑z⁻¹) a) - (↑I) a = 0 :=
    by
    have h : (↑I) a = a + (↑I) ((↑z⁻¹) a) := by
      funext n; simp
      conv_lhs => rw [integral_unfold]
      rw [integral_timeInvariant]
    rw [h]; abel
  rw [hz]; simp
  funext n t; simp

theorem joinDoubleIncremental_ok : ↑²(↑²(equiJoin π1 π2)^Δ2)^Δ2 = joinDoubleIncremental π1 π2 :=
  by
  rw [joinDoubleIncremental1_ok]
  unfold joinDoubleIncremental1 joinDoubleIncremental
  funext a b; simp
  unfold incremental2
  unfold D
  repeat' rw [equiJoin_lifting2_time_invariant]
  rw [equiJoin_i_unfold]
  rw [equiJoin_i_unfold]
  rw [equiJoin_i_unfold]
  abel_nf
  have :
  (↑²↑²(equiJoin π1 π2)) a b +
    ((↑²↑²(equiJoin π1 π2)) a (z⁻¹ (I b)) +
      ((↑²↑²(equiJoin π1 π2)) (z⁻¹ (I a)) b +
        ((↑²↑²(equiJoin π1 π2)) ((↑z⁻¹) ((↑I) a)) b +
          ((↑²↑²(equiJoin π1 π2)) ((↑z⁻¹) ((↑I) a)) (z⁻¹ (I b)) +
            ((↑²↑²(equiJoin π1 π2)) (z⁻¹ (I ((↑z⁻¹) ((↑I) a)))) b +
              ((↑²↑²(equiJoin π1 π2)) a ((↑z⁻¹) ((↑I) b)) +
                ((↑²↑²(equiJoin π1 π2)) a (z⁻¹ (I ((↑z⁻¹) ((↑I) b)))) +
                  (↑²↑²(equiJoin π1 π2)) (z⁻¹ (I a)) ((↑z⁻¹) ((↑I) b)))))))))
  =
  (π1▹◃π2) a b + ((π1▹◃π2) a (z⁻¹ (I b)) + ((π1▹◃π2) (z⁻¹ (I a)) b + ((π1▹◃π2) a ((↑z⁻¹) ((↑I) b)) + ((π1▹◃π2) ((↑z⁻¹) ((↑I) a)) b + ((π1▹◃π2) a (z⁻¹ (I ((↑z⁻¹) ((↑I) b)))) + ((π1▹◃π2) (z⁻¹ (I a)) ((↑z⁻¹) ((↑I) b)) + ((π1▹◃π2) ((↑z⁻¹) ((↑I) a)) (z⁻¹ (I b)) + (π1▹◃π2) (z⁻¹ (I ((↑z⁻¹) ((↑I) a)))) b)))))))
  := by abel
  rw [this] ; clear this
  have :
  (↑²↑²(equiJoin π1 π2)) (z⁻¹ (I a)) ((↑z⁻¹) ((↑I) b)) +
    ((↑²↑²(equiJoin π1 π2)) (I ((↑I) a)) b +
      ((↑²↑²(equiJoin π1 π2)) ((↑I) a) (z⁻¹ (I b)) + (↑²↑²(equiJoin π1 π2)) a ((↑z⁻¹) (I ((↑I) b)))))
  =
  (π1▹◃π2) (I ((↑I) a)) b + ((π1▹◃π2) ((↑I) a) (z⁻¹ (I b)) + ((π1▹◃π2) a ((↑z⁻¹) (I ((↑I) b))) + (π1▹◃π2) (z⁻¹ (I a)) ((↑z⁻¹) ((↑I) b))))
  := by abel
  rw [this] ; clear this
  repeat'
    first
    | rw [← integral_lift_time_invariant]
    | rw [← lift_integral_lift_time_invariant]
    | rw [← integral_timeInvariant]
  conv_rhs =>
    rw [equiJoin_i_1 π1 π2]
    rw [equiJoin_i_2 π1 π2 a _]
    rw [equiJoin_lift_i_1 π1 π2 a]
    rw [equiJoin_lift_i_1 π1 π2 a]
  repeat'
    first
    | rw [← integral_lift_time_invariant]
    | rw [← lift_integral_lift_time_invariant]
    | rw [← integral_timeInvariant]
  repeat' rw [add_assoc]
  apply eq_of_sub_eq_zero
  abel_nf
  conv_lhs =>
    rhs; rw [add_comm]; skip
  rw [fold_join_helper]
  abel

end equiJoin

noncomputable def incrementalClosureOpt : Operator Z[Edge Node] Z[Edge Node] := fun dE =>
  let E := (↑↑δ0) dE
  (↑↑∫0)^Δ <| fix2 (fun R => distinctDoubleIncremental
                  ((↑↑(↑↑(Zset.map πht)))
                    (joinDoubleIncremental Prod.snd Prod.fst ((↑z⁻¹) R) E) +
                  E +
                  (↑↑(↑↑(Zset.map πh))) E +
                  (↑↑(↑↑(Zset.map πt))) E))

theorem incrementalClosureOpt_ok : @incrementalClosureOpt Node _ = ↑closure0^Δ :=
  by
  rw [← incrementalClosure2_ok]
  unfold incrementalClosureOpt incrementalClosure2
  funext dE; dsimp
  funext R
  rw [distinctDoubleIncremental_ok]
  rw [joinDoubleIncremental_ok]

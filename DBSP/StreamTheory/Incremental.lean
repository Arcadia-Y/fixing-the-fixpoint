-- Copyright 2022-2023 VMware, Inc.
import DBSP.StreamTheory.Linear

/-!
# Incremental version of an operator

A key idea of DBSP is to define for any `Q: operator a b` an incremental version
of it, `Q^Δ := D ∘ Q ∘ I`. Notice that `Q^Δ : operator a b` - it has the same
type as `Q`, but it takes as input a stream of changes and outputs a stream of
diffs.
-/

-- SPDX-License-Identifier: BSD-2-Clause
section Groups

variable {a : Type} [AddCommGroup a]

variable {b : Type} [AddCommGroup b]

variable {c : Type} [AddCommGroup c]

/-- The core definition of DBSP is the incremental version of an operator Q, Q^Δ.

If we think of the operator Q as a transformation on databases, Q^Δ operates on
a stream of changes and outputs a stream of changes. It does this by simply
integrating the input, applying Q, and differentiating the output. The power of
DBSP comes from re-arranging incremental computations to produce more efficient plans.
-/
def incremental (Q : Operator a b) : Operator a b := fun s => D (Q (I s))

-- applied version of incremental that can be useful for rewriting
theorem incremental_unfold (Q : Operator a b) (s : stream a) : incremental Q s = D (Q (I s)) :=
  rfl

/-- A version of incremental for curried operators, defined directly. Written
T^Δ2.  -/
def incremental2 (T : Operator2 a b c) : Operator2 a b c := fun s1 s2 => D (T (I s1) (I s2))

-- applied version of incremental2 that can be useful for rewriting
theorem incremental2_unfold (Q : Operator2 a b c) (s1 : stream a) (s2 : stream b) :
    incremental2 Q s1 s2 = D (Q (I s1) (I s2)) :=
  rfl

postfix:90 "^Δ" => incremental

postfix:90 "^Δ2" => incremental2

private def incrementalInv (Q : Operator a b) : Operator a b :=
  I ∘ Q ∘ D

attribute [local simp] derivative_integral integral_derivative

theorem incrementalInversion_l : Function.LeftInverse (@incremental a _ b _) incrementalInv :=
  by
  intro Q
  unfold incremental incrementalInv
  funext s; simp

theorem incrementalInversion_r : Function.RightInverse (@incremental a _ b _) incrementalInv :=
  by
  intro Q
  unfold incremental incrementalInv
  funext s; simp

theorem incremental_bijection : Function.Bijective (@incremental a _ b _) :=
  by
  constructor
  · apply Function.LeftInverse.injective
    apply incrementalInversion_r
  · apply Function.RightInverse.surjective
    apply incrementalInversion_l

macro "prove_incremental" : tactic =>
  `(tactic|
    (try unfold incremental;
     try unfold incremental2;
     funext s;
     simp))

theorem delay_invariance : incremental (@delay a _) = delay :=
  by
  funext s; rw [incremental_unfold]
  rw [derivative_timeInvariant]
  simp

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3214051217.prove_incremental -/
theorem integral_invariance : incremental (@I a _) = I := by
  prove_incremental

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3214051217.prove_incremental -/
theorem derivative_invariance : incremental (@D a _) = D := by
  prove_incremental

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3214051217.prove_incremental -/
theorem integrate_push (Q : Operator a b) : Q ∘ I = I ∘ Q^Δ := by
  prove_incremental

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3214051217.prove_incremental -/
theorem derivative_push (Q : Operator a b) : D ∘ Q = (Q^Δ) ∘ D := by
  prove_incremental

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3214051217.prove_incremental -/
theorem i_push (Q : Operator a b) (s : stream a) : Q (I s) = I ((Q^Δ) s) := by
  prove_incremental

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3214051217.prove_incremental -/
theorem D_push (Q : Operator a b) (s : stream a) : D (Q s) = (Q^Δ) (D s) := by
  prove_incremental

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3214051217.prove_incremental -/
theorem D_push2 (Q : Operator2 a b c) (s1 : stream a) (s2 : stream b) :
    D (Q s1 s2) = (Q^Δ2) (D s1) (D s2) := by
  prove_incremental

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3214051217.prove_incremental -/
theorem chain_incremental (Q1 : Operator b c) (Q2 : Operator a b) : (Q1 ∘ Q2)^Δ = (Q1^Δ) ∘ Q2^Δ :=
  by
  prove_incremental

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3214051217.prove_incremental -/
theorem incremental_comp (Q1 : Operator b c) (Q2 : Operator a b) (s : stream a) :
    ((fun s => Q1 (Q2 s))^Δ) s = (Q1^Δ) ((Q2^Δ) s) := by
  prove_incremental

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3214051217.prove_incremental -/
theorem add_incremental (Q1 Q2 : Operator a b) : (Q1 + Q2)^Δ = Q1^Δ + Q2^Δ :=
  by
  prove_incremental
  rw [derivative_linear]

omit [AddCommGroup a] in
theorem cycle_body_strict (T : Operator2 a b b) (hcausal : Causal (uncurryOp T)) :
    ∀ s, Strict fun α : stream b => T s (z⁻¹ α) :=
  by
  intro s
  apply causal_strict_strict delay delay_strict _ _
  apply causal_uncurryOp_fixed; assumption

theorem cycle_body_integral_strict (T : Operator2 a b b) (hcausal : Causal (uncurryOp T)) :
    ∀ s, Strict fun α : stream b => T (I s) (z⁻¹ α) :=
  by
  intro s
  apply causal_strict_strict delay delay_strict _ _
  apply causal_uncurryOp_fixed; assumption

theorem cycle_body_incremental_strict (T : Operator2 a b b) (hcausal : Causal (uncurryOp T))
    (s : stream a) : Strict fun α => (T^Δ2) s (z⁻¹ α) :=
  by
  apply causal_strict_strict delay delay_strict (fun α => D (T (I s) (I α))) _
  apply causal_comp_causal _ _ _ derivative_causal
  apply causal_comp_causal _ integral_causal _ _
  apply causal_uncurryOp_fixed; assumption

theorem cycle_incremental (T : Operator2 a b b) (hcausal : Causal (uncurryOp T)) :
    (fun s : stream a => fix fun α => T s (z⁻¹ α))^Δ = fun s => fix fun α => (T^Δ2) s (z⁻¹ α) :=
  by
  funext s
  apply fix_unique
  ·-- strictness of the body
    apply cycle_body_incremental_strict;
    assumption
  · -- fixpoint equation
    unfold incremental incremental2
    rw [integral_timeInvariant]; simp
    apply congr; simp
    apply fix_eq; apply cycle_body_integral_strict ; assumption

theorem incremental_sprod (f : Operator (a × b) c) (s1 : stream a) (s2 : stream b) :
    (f^Δ) (sprod (s1, s2)) = ((fun s1 s2 => f (sprod (s1, s2)))^Δ2) s1 s2 :=
  by
  unfold incremental incremental2
  rw [integral_sprod]

omit [AddCommGroup a] [AddCommGroup b] in
lemma sprod_eq_self (s : stream (a × b)) :
    sprod ((↑↑Prod.fst) s, (↑↑Prod.snd) s) = s := by
  funext n; simp

/-- Rewrite the incremental of an operator on products into incremental2 form.
This is the converse direction of `incremental_sprod`: given any stream
`s : stream (a × b)`, we can decompose it and express `(f^Δ) s` using
`incremental2`. -/
theorem incremental_as_incremental2 (f : Operator (a × b) c) (s : stream (a × b)) :
    (f^Δ) s = ((fun s1 s2 => f (sprod (s1, s2)))^Δ2) ((↑↑Prod.fst) s) ((↑↑Prod.snd) s) := by
  conv_lhs => rw [← sprod_eq_self s]
  exact incremental_sprod f ((↑↑Prod.fst) s) ((↑↑Prod.snd) s)

omit [AddCommGroup a] in
theorem lifting_cycle_body_strict2 (T : Operator2 a b b) (hcausal : Causal (uncurryOp T)) :
    ∀ s, Strict2 fun α : stream (stream b) => (↑²T) s ((↑↑z⁻¹) α) :=
  by
  rw [causal2] at hcausal
  intro s
  intro s1 s2 n t heq
  apply hcausal; rfl
  intro n' hle
  by_cases n' = 0; · subst n'; simp
  simp
  rw [delay_sub_1]; swap; omega
  rw [delay_sub_1]; swap; omega
  apply heq <;> omega

theorem sumVals_nested (s : stream (stream a)) (n t : ℕ) :
    sumVals s n t = sumVals (fun n => s n t) n := by
  induction' n with n <;> simp; aesop

theorem integral_lift_time_invariant (s : stream (stream a)) : I ((↑↑z⁻¹) s) = (↑↑z⁻¹) (I s) :=
  by
  funext n t; simp
  repeat' rw [integral_sumVals]
  rw [sumVals_nested]
  by_cases ht: (t = 0)
  · subst ht; simp; rw [sumVals_zero]; tauto
  simp
  rw [delay_linear]; simp
  rw [delay_sub_1]; swap; omega
  rw [sumVals_nested]
  congr 1
  funext n
  rw [delay_sub_1]; omega

theorem lift_integral_lift_time_invariant (s : stream (stream a)) :
    (↑↑I) ((↑↑z⁻¹) s) = (↑↑z⁻¹) ((↑↑I) s) :=
  by
  funext n t; simp
  rw [integral_timeInvariant]

theorem lifting_delay_linear : Linear (↑↑(@delay a _)) :=
  by
  apply (lifting_lti _ _).1
  intros; rw [delay_linear]

theorem integral_causal_nested' (s1 s2 : stream (stream a)) (n t : ℕ)
    (heq : ∀ n' ≤ n, s1 n' t = s2 n' t) : I s1 n t = I s2 n t :=
  by
  rw [integral_sumVals, integral_sumVals]
  repeat' rw [sumVals_nested]
  simp; rw [heq] <;> try omega
  induction' n with n n_ih <;> simp
  rw [heq] <;> try omega
  apply n_ih
  intros; apply heq ; omega


@[simp]
theorem integral_causalNested : CausalNested (@I (stream a) _) :=
  by
  intro s1 s2 n t heq
  apply integral_causal_nested'
  intros; apply heq <;> omega

@[simp]
theorem derivative_causalNested : CausalNested (@D (stream a) _) :=
  by
  intro s1 s2 n t heq
  unfold D; simp
  rw [heq]; rotate_left; omega; omega
  simp
  unfold delay; split_ifs; simp
  rw [heq] <;> omega

omit [AddCommGroup a] in
theorem cycle_body_strict2 (T : Operator2 a (stream b) (stream b)) (s : stream a) :
    CausalNested (T s) → Strict2 fun α => T s ((↑↑z⁻¹) α) :=
  by
  intro hcausal
  unfold Strict2; intro s1 s2 n t hseq
  apply hcausal; intro _ _ _ _
  apply lifting_delay_strict2; intros
  apply hseq <;> omega

theorem cycle_body_incremental_strict2 (T : Operator2 a (stream b) (stream b)) (s : stream a) :
    CausalNested (T (I s)) → Strict2 fun α => (T^Δ2) s ((↑↑z⁻¹) α) :=
  by
  intro hcausal
  unfold incremental2
  unfold Strict2; intro s1 s2 n t hseq
  apply derivative_causalNested; intro _ _ _ _
  apply hcausal; intro _ _ _ _
  apply integral_causalNested; intro _ _ _ _
  apply lifting_delay_strict2; intros
  apply hseq <;> omega

omit [AddCommGroup a] in
theorem lifting_cycle (T : Operator2 a b b) (hcausal : Causal (uncurryOp T)) :
    (↑↑fun s => fix fun α => T s (z⁻¹ α)) = fun s => fix2 fun α => (↑²T) s ((↑↑z⁻¹) α) :=
  by
  funext s
  apply fix2_unique
  · apply lifting_cycle_body_strict2; assumption
  · funext t; simp
    apply fix_eq; apply cycle_body_strict; assumption

theorem cycle2_incremental (T : Operator2 a (stream b) (stream b))
    (hcausal : ∀ s, CausalNested (T s)) :
    (fun s : stream a => fix2 fun α => T s ((↑↑z⁻¹) α))^Δ = fun s =>
      fix2 fun α => (T^Δ2) s ((↑↑z⁻¹) α) :=
  by
  funext s
  apply fix2_unique
  ·-- strictness of the body
    apply cycle_body_incremental_strict2 T;
    aesop
  · -- fixpoint equation
    unfold incremental incremental2
    rw [integral_lift_time_invariant]; simp
    apply congr; simp
    apply fix2_eq; apply cycle_body_strict2; aesop

theorem lti_incremental (Q : Operator a b) (h : Lti Q) : Q^Δ = Q :=
  by
  funext s; unfold incremental
  unfold D
  rw [← h.2]
  rw [← integral_timeInvariant]
  rw [← linear_sub h.1]
  rw [← linear_sub integral_linear]
  conv =>
    lhs; rhs; rhs
    change D s
  simp

@[simp]
theorem i_incremental : I^Δ = @I a _ :=
  by
  apply lti_incremental
  apply integral_lti

@[simp]
theorem d_incremental : D^Δ = @D a _ :=
  by
  apply lti_incremental
  apply derivative_lti

theorem delay_lti : Lti (@delay a _) := by
  constructor
  apply delay_linear
  apply delay_timeInvariant

@[simp]
theorem delay_incremental : z⁻¹^Δ = @delay a _ :=
  by
  apply lti_incremental
  apply delay_lti

omit [AddCommGroup c] in
theorem sprod_time_invariant (s1 : stream a) (s2 : stream b) :
    ↑(z⁻¹ s1, z⁻¹ s2) = z⁻¹ (↑(s1, s2) : stream (a × b)) :=
  by
  funext t; simp
  unfold delay
  split_ifs <;> simp

theorem time_invariant_map_fst (s : stream (a × b)) (n : ℕ) :
    (z⁻¹ s n).fst = z⁻¹ (fun n : ℕ => (s n).fst) n :=
  by
  unfold delay
  split_ifs <;> simp

theorem time_invariant_map_snd (s : stream (a × b)) (n : ℕ) :
    (z⁻¹ s n).snd = z⁻¹ (fun n : ℕ => (s n).snd) n :=
  by
  unfold delay
  split_ifs <;> simp

theorem time_invariant2 (T : Operator2 a b c) :
    TimeInvariant (uncurryOp T) ↔ ∀ s1 s2, T (z⁻¹ s1) (z⁻¹ s2) = z⁻¹ (T s1 s2) :=
  by
  constructor
  · intro hti; intro _ _
    rw [uncurryOp_intro T]
    rw [uncurryOp_intro T]
    rw [← hti]
    apply congr; simp
    simp; simp_rw [← sprod_time_invariant]
  · intro h s
    funext t; simp [uncurryOp, lifting]
    rw [← h]
    congr 1 <;> funext t <;> simp
    · rw [time_invariant_map_fst]; aesop
    · rw [time_invariant_map_snd]; aesop

@[simp]
theorem causal_incremental (Q : Operator a b) : Causal Q → Causal (Q^Δ) :=
  by
  intro h
  unfold incremental
  apply causal_comp_causal; swap; apply derivative_causal
  apply causal_comp_causal; swap; apply h
  apply integral_causal

theorem causal_incremental2 (Q : Operator2 a b c) :
    Causal (uncurryOp Q) → Causal fun s => (Q^Δ2) ((↑↑Prod.fst) s) ((↑↑Prod.snd) s) :=
  by
  intro h
  apply causal_comp_causal; swap; apply derivative_causal
  rw [causal2] at h
  intro s1 s2 n heq; simp
  apply h
  · apply causal_respects_agreeUpto; apply integral_causal
    apply causal_respects_agreeUpto; apply lifting_causal
    assumption
  · apply causal_respects_agreeUpto; apply integral_causal
    apply causal_respects_agreeUpto; apply lifting_causal
    assumption

@[simp]
theorem causalNested_incremental (Q : Operator (stream a) (stream b)) :
    CausalNested Q → CausalNested (Q^Δ) := by
  intro h
  unfold CausalNested; intros; rename_i heq
  rw [incremental_unfold, incremental_unfold]
  apply causalNested_comp; apply derivative_causalNested
  apply h
  intro _ _ _ _
  apply integral_causalNested; intro _ _ _ _; apply heq <;> omega

omit [AddCommGroup a] [AddCommGroup b] [AddCommGroup c] in
@[simp]
theorem causalNested_lifting2 {D : Type} [AddCommGroup D] (f : stream b → stream c → stream D)
    (g : Operator (stream a) (stream b)) (h : Operator (stream a) (stream c)) :
    Causal (uncurryOp f) →
      CausalNested g → CausalNested h → CausalNested fun s => (↑²f) (g s) (h s) :=
  by
  intro hf hg hh
  intro s1 s2 n t heq; simp
  rw [causal2] at hf
  apply hf
  · intro n' hle; apply hg; intro _ _ _ _; apply heq <;> omega
  · intro n' hle; apply hh; intro _ _ _ _; apply heq <;> omega

omit [AddCommGroup a] in
@[simp]
theorem causalNested_lifting2_incremental {D : Type} [AddCommGroup D]
    (f : stream b → stream c → stream D) (g : Operator (stream a) (stream b))
    (h : Operator (stream a) (stream c)) :
    Causal (uncurryOp f) →
      CausalNested g → CausalNested h → CausalNested fun s => (↑²f^Δ2) (g s) (h s) :=
  by
  intro hf hg hh
  unfold incremental2
  apply causalNested_comp; simp
  apply causalNested_lifting2
  · assumption
  · apply causalNested_comp; simp; assumption
  · apply causalNested_comp; simp; assumption

omit [AddCommGroup a] [AddCommGroup b] [AddCommGroup c] in
@[simp]
theorem causal_lifting2 {D : Type} [AddCommGroup D] (f : b → c → D) (g : Operator a b)
    (h : Operator a c) : Causal g → Causal h → Causal fun s => (↑²f) (g s) (h s) :=
  by
  intro hg hh
  intro s1 s2 n heq; simp
  rw [hg, hh] <;> assumption

omit [AddCommGroup a] in
@[simp]
theorem causal_lifting2_incremental {D : Type} [AddCommGroup D] (f : b → c → D) (g : Operator a b)
    (h : Operator a c) : Causal g → Causal h → Causal fun s => (↑²f^Δ2) (g s) (h s) :=
  by
  intro hg hh
  apply causal_comp_causal; swap; simp
  apply causal_lifting2
  · apply causal_comp_causal
    assumption; apply integral_causal
  · apply causal_comp_causal
    assumption; apply integral_causal

omit [AddCommGroup a] [AddCommGroup b] in
theorem lifting2_sum (f g : a → b → c) : (↑²fun x y => f x y + g x y) = ↑²f + ↑²g := rfl

theorem lifting2_incremental_sum (f g : a → b → c) :
    (↑²fun x y => f x y + g x y)^Δ2 = ↑²f^Δ2 + ↑²g^Δ2 :=
  by
  unfold incremental2
  funext s1 s2 t; simp
  rw [lifting2_sum]; simp
  rw [derivative_linear]; simp

omit [AddCommGroup b] [AddCommGroup c] in
private lemma lifting2_incremental_unfold {d e : Type} [AddCommGroup d] [AddCommGroup e]
    (f : b → c → d) (g : a → b) (h : e → c) :
    (↑²fun x y => f (g x) (h y))^Δ2 = fun s1 s2 => D ((↑²f) ((↑↑g) (I s1)) ((↑↑h) (I s2))) := by rfl

theorem lifting2_incremental_comp {D e : Type} [AddCommGroup D] [AddCommGroup e] (f : b → c → D)
    (g : a → b) (h : e → c) :
    (↑²fun x y => f (g x) (h y))^Δ2 = fun s1 s2 => (↑²f^Δ2) ((↑↑g^Δ) s1) ((↑↑h^Δ) s2) :=
  by
  funext s1 s2
  rw [lifting2_incremental_unfold]; dsimp
  rw [incremental2_unfold]
  rw [D_push2]
  rfl

@[simp]
theorem incremental_id : (incremental fun x : stream a => x) = id := by
  funext s; rw [incremental_unfold]; simp

@[simp]
theorem incremental_id' : incremental (@id (stream a)) = id := by
  funext s; rw [incremental_unfold]; simp

theorem lifting2_incremental_comp_1' {D : Type} [AddCommGroup D] (f : b → c → D) (g : a → b) :
    (↑²fun x => f (g x))^Δ2 = fun s1 => (↑²f^Δ2) ((↑↑g^Δ) s1) :=
  by
  funext s1 s2
  rw [lifting2_incremental_comp]; simp

theorem lifting2_incremental_comp_1 {D : Type} [AddCommGroup D] (f : b → c → D) (g : a → b) :
    (↑²fun x y => f (g x) y)^Δ2 = fun s1 s2 => (↑²f^Δ2) ((↑↑g^Δ) s1) s2 :=
  by apply lifting2_incremental_comp_1'

theorem lifting2_incremental_comp_2 {D e : Type} [AddCommGroup D] [AddCommGroup e] (f : b → c → D)
    (h : e → c) : (↑²fun x y => f x (h y))^Δ2 = fun s1 s2 => (↑²f^Δ2) s1 ((↑↑h^Δ) s2) :=
  by
  funext s1 s2
  rw [lifting2_incremental_comp]; simp

end Groups

-- This theorem is much more clearly stated using the metavariables a, b, c for
-- terms (to match the paper), so here we instead use α, β, γ for the types.
section Bilinear

variable {α : Type} [AddCommGroup α]

variable {β : Type} [AddCommGroup β]

variable {γ : Type} [AddCommGroup γ]

variable (times : Operator2 α β γ)

-- write times a b as a ** b for this section
-- NOTE: this isn't printed, sadly
local notation:70 a " ** " b:70 => times a b

attribute [local simp] derivative_integral integral_derivative

def timesIncremental : stream α → stream β → stream γ := fun a b =>
  a ** b + I (z⁻¹ a) ** b + a ** I (z⁻¹ b)

theorem bilinear_incremental :
    TimeInvariant (uncurryOp times) → Bilinear times → times^Δ2 = timesIncremental times :=
  by
  intro hti hbil; funext a b
  -- this calculation is almost a transcription of the paper proof in
  -- https://github.com/vmware/database-stream-processor/blob/main/doc/spec.pdf
  calc
    (times^Δ2) a b = D (I a ** I b) := by rfl
    _ = I a ** I b - z⁻¹ (I a ** I b) := by rfl
    _ = I a ** I b - z⁻¹ (I a) ** z⁻¹ (I b) := by rw [(time_invariant2 _).mp hti]
    _ = I a ** I b - z⁻¹ (I a) ** z⁻¹ (I b) + z⁻¹ (I a) ** I b - z⁻¹ (I a) ** I b := by abel
    _ = D (I a) ** I b + z⁻¹ (I a) ** D (I b) :=
      by
      unfold D
      rw [bilinear_sub_1 hbil]
      rw [bilinear_sub_2 hbil]; abel
    _ = a ** I b + z⁻¹ (I a) ** b := by simp
    _ = a ** I b - a ** z⁻¹ (I b) + a ** z⁻¹ (I b) + z⁻¹ (I a) ** b := by abel
    _ = a ** D (I b) + a ** z⁻¹ (I b) + z⁻¹ (I a) ** b :=
      by
      unfold D
      rw [bilinear_sub_2 hbil]
    _ = a ** b + z⁻¹ (I a) ** b + a ** z⁻¹ (I b) := by simp; abel
    -- this one extra step is needed that the paper skips over
        _ =
        a ** b + I (z⁻¹ a) ** b + a ** I (z⁻¹ b) :=
      by repeat' rw [integral_timeInvariant]

-- NOTE: this is a much simpler proof than the one in the paper
theorem bilinear_incremental_forward_proof :
    TimeInvariant (uncurryOp times) →
      Bilinear times → ∀ a b, (times^Δ2) a b = a ** b + I (z⁻¹ a) ** b + a ** I (z⁻¹ b) :=
  by
  intro hti hbil a b
  unfold incremental2 D
  -- we're just going to expand (I a) and (I b) in the first occurrence
  conv =>
    pattern times (I a) (I b)
    rw [integral_unfold a, integral_unfold b]
  -- push delays as far inward as possible
  rw [← (time_invariant2 _).mp hti]
  repeat' rw [← integral_timeInvariant]
  -- and now we can expand using bilinearity
  repeat'
    first
    | rw [hbil.1]
    | rw [hbil.2]
  abel

-- variant of [bilinear_incremental_forward_proof] written with [conv] so the
-- proof itself is readable
theorem bilinear_incremental_short_paper_proof :
    TimeInvariant (uncurryOp times) →
      Bilinear times → ∀ a b, (times^Δ2) a b = a ** b + I (z⁻¹ a) ** b + a ** I (z⁻¹ b) :=
  by
  intro hti hbil a b
  calc
    (times^Δ2) a b = D (I a ** I b) := by rfl
    _ = I a ** I b - z⁻¹ (I a ** I b) := by rfl
    _ = I a ** I b - z⁻¹ (I a) ** z⁻¹ (I b) := by rw [← (time_invariant2 _).mp hti]
    _ = (a + z⁻¹ (I a)) ** (b + z⁻¹ (I b)) - z⁻¹ (I a) ** z⁻¹ (I b) :=
      by
      congr 1
      conv_lhs =>
        pattern times (I a) (I b)
        rw [integral_unfold a, integral_unfold b]
    _ =
        a ** b + z⁻¹ (I a) ** b + a ** z⁻¹ (I b) + z⁻¹ (I a) ** z⁻¹ (I b) -
          z⁻¹ (I a) ** z⁻¹ (I b) :=
      by
      -- bilinearity to distribute (a + b) × (c + D)
      rw [hbil.2, hbil.1, hbil.1]
      abel
    _ = a ** b + z⁻¹ (I a) ** b + a ** z⁻¹ (I b) :=
      by-- cancel terms
      abel
    _ = a ** b + I (z⁻¹ a) ** b + a ** I (z⁻¹ b) := by
      rw [integral_timeInvariant, integral_timeInvariant]

end Bilinear

-- #lint only doc_blame simp_nf

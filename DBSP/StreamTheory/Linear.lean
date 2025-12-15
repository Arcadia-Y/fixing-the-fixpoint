-- Copyright 2022-2023 VMware, Inc.
import DBSP.StreamTheory.Operators
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Ring.Basic

/-!
# Linearity, differentiation, and integration

This file extends DBSP with two key operators: differentiation and integration.
These are based on the idea of linearity, a property of streams over Abelian
(commutative) groups.
-/
section StreamAddMonoid

variable {a b c: Type}
         [AddCommMonoid a] [AddCommMonoid b] [AddCommMonoid c]

instance {a: Type} [AddCancelCommMonoid a] : AddCancelCommMonoid (stream a) := by
  unfold stream; infer_instance

instance : AddCommMonoid (stream a) := by
  simp [stream]; infer_instance

instance [PartialOrder a] [IsOrderedAddMonoid a] : IsOrderedAddMonoid (stream a) :=
  by unfold stream; infer_instance

instance [PartialOrder a] [CanonicallyOrderedAdd a] : CanonicallyOrderedAdd (stream a) :=
  by unfold stream; infer_instance

@[simp]
lemma stream_add_apply (s1 s2 : stream a) (t : ℕ) : (s1 + s2) t = s1 t + s2 t := rfl

/-- An operator `S` is linear if S (x + y) = S x + S y; that is, it should be a
homomorphism between `stream a` and `stream b`. -/
def Linear (S : Operator a b) :=
  -- note this is phrased in the stream group
  ∀ x y, S (x + y) = S x + S y

-- for symmetry with the other properties derived from linear (and to avoid
-- directly depending on this definition)
theorem linear_add {S : Operator a b} (h : Linear S) : ∀ s1 s2, S (s1 + s2) = S s1 + S s2 :=
  h

theorem linear_zero {b: Type} [AddCancelCommMonoid b] {S : Operator a b} (h : Linear S) : S 0 = 0 :=
  by
  have h0 := h 0 0
  simp at h0
  tauto

theorem lifting_linear (f : a → b) : (∀ x y, f (x + y) = f x + f y) → Linear (↑↑f) :=
  by
  intro hlin
  intro x y; funext t; simp; apply hlin

theorem add_causal : Causal (uncurryOp ((· + ·) : Operator2 a a a)) :=
  by
  unfold Causal; introv heq
  unfold uncurryOp; simp; rw [heq]; linarith

omit [AddCommMonoid a] in
theorem sum_causal (f g : Operator a b) : Causal f → Causal g → Causal fun x => f x + g x :=
  by
  unfold Causal; intro hf hg; introv heq
  simp; rw [hf, hg] <;> assumption

omit [AddCommMonoid a] in
theorem sum_causalNested (f g : Operator (stream a) (stream b)) :
    CausalNested f → CausalNested g → CausalNested fun x => f x + g x :=
  by
  unfold CausalNested; intro hf hg; introv heq
  simp; rw [hf, hg] <;> assumption

/-- LTI stands for linear time invariant. -/
def Lti (S : Operator a b) :=
  Linear S ∧ TimeInvariant S

-- a weak zero-preservation at only t=0
theorem lti_operator_zpp (S : Operator a b) : Lti S → S 0 0 = 0 := fun h => timeInvariant_0_0 S h.2

-- convenience for generating lti theorems
theorem lifting_lti {b: Type} [AddCancelCommMonoid b](f : a → b) : (∀ x y, f (x + y) = f x + f y) → Lti (↑↑f) :=
  by
  intro hlin
  constructor
  · apply lifting_linear; assumption
  · apply lifting_timeInvariant
    have h0 := hlin 0 0; simp at h0
    apply h0

/-- A function of two arguments is bilinear if it is linear in each argument
separately (holding the other constant). A classic example is multiplication. -/
def Bilinear (f : a → b → c) :=
  (-- linear in each argument, separately
    ∀ x1 x2 y, f (x1 + x2) y = f x1 y + f x2 y) ∧
    ∀ x y1 y2, f x (y1 + y2) = f x y1 + f x y2

theorem lifting_bilinear (f : a → b → c) : Bilinear f → Bilinear (↑²f) :=
  by
  intro hf; unfold lifting2
  constructor
  · intro x1 x2 z
    funext t; simp
    apply hf.1
  · intro x1 x2 z
    funext t; simp
    apply hf.2

-- note that this is for the specific group ℤ
theorem hMul_Z_bilinear : Bilinear (lifting2 fun z1 z2 : ℤ => z1 * z2) :=
  by
  apply lifting_bilinear
  constructor <;> intro _ _ _ <;> ring_nf

-- NOTE: it is important to take {a: Type} since we don't want to assume the
-- group and ring structures over a separately, we need the group structure to
-- be the one from the ring
theorem hMul_ring_bilinear {a : Type} [Ring a] :
    Bilinear (@lifting2 a a a fun z1 z2 : a => z1 * z2) :=
  by
  apply lifting_bilinear
  constructor <;> intro _ _ _ <;> ring_nf
  · rw [right_distrib]
  · rw [left_distrib]

/-- A "feedback" circuit that keeps adding its output from the previous time step,
defined using a fixpoint. To be well-defined, `S` must be causal.

```
                ┌─────┐
 s ────▶ + ────▶│  S  │───▶ α
         ▲      └─────┘
         │         │
      ┌─────┐      │
      │ z⁻¹ │◀─────┘
      └─────┘
```
-/
def feedback (S : Operator a a) : Operator a a := fun s => fix fun α => S (s + delay α)

theorem feedback_strict {S : Operator a a} (hcausal : Causal S) (s : stream a) :
    Strict fun α : stream a => S (s + delay α) :=
  by
  apply loop1_body_strict _ delay_strict fun s t => S (s + t)
  rw [causal2]
  introv h1 h2
  apply hcausal
  intro i hle; simp
  rw [h1, h2] <;> omega

/-- As long as `S` is [causal], the body of the feedback loop is strict and
[feedback] can be unfolded according to its recursive definition. -/
theorem feedback_unfold (S : Operator a a) :
    Causal S → ∀ s, feedback S s = S (s + delay (feedback S s)) :=
  by
  intro hcausal s
  unfold feedback
  apply fix_eq
  apply feedback_strict hcausal

theorem delay_linear : Linear (@delay a _) :=
  by
  intro x y
  funext t
  unfold delay; simp
  by_cases h_t : t = 0
  · repeat simp_rw [if_pos h_t]; simp
  · repeat' rw [if_neg h_t]

theorem add_linear : Linear (uncurryOp ((· + ·) : stream a → stream a → stream a)) :=
  by
  intro x y
  funext t
  unfold uncurryOp; simp
  abel

theorem agreeUpto_respects_add (s1 s2 s1' s2' : stream a) (n : ℕ) :
    (s1 =[ n ]= s1') → (s2 =[ n ]= s2') → (s1 + s2) =[n]= s1' + s2' :=
  by
  intro h1 h2
  intro t hle; simp
  rw [h1, h2] <;> assumption

-- TODO: can we give a general characterization of time invariance of fixpoints?
-- yes, see `feedback_ckt_timeInvariant` in `Operators.lean`
theorem feedback_timeInvariant (S : Operator a a) :
    Causal S → TimeInvariant S → TimeInvariant (feedback S) :=
  by
  intro hcausal hti
  intro s
  rw [agree_everywhere_eq]
  intro n
  induction' n with n
  · rw [agreeUpto_0]
    unfold feedback; simp
    rw [timeInvariant_t hti]; simp
  · rw [feedback_unfold] <;> try assumption
    rw [← delay_linear]
    rw [hti]
    apply delay_succ_upto
    have h : (s + feedback S (delay s)) =[n]= s + delay (feedback S s) :=
      by
      apply agreeUpto_respects_add
      rfl; assumption
    have heq := causal_respects_agreeUpto _ hcausal _ _ _ h
    trans; assumption
    rw [← feedback_unfold _ hcausal s]

theorem feedback_causal (S : Operator a a) : Causal S → Causal (feedback S) :=
  by
  intro hcausal
  have h := hcausal
  rw [causal_to_agree] at h ⊢
  introv heq
  induction' n with n n_ih
  · rw [feedback_unfold _ hcausal s1, feedback_unfold _ hcausal s2]
    apply h
    rw [agreeUpto_0] at heq ⊢; simp; assumption
  · rw [feedback_unfold _ hcausal s1, feedback_unfold _ hcausal s2]
    apply h
    apply agreeUpto_respects_add; assumption
    apply delay_succ_upto
    apply n_ih
    apply agreeUpto_weaken1; assumption

theorem feedback_linear (S : Operator a a) : Causal S → Lti S → Linear (feedback S) :=
  by
  intro hcausal hlti
  cases' hlti with hlin hti
  intro s1 s2
  symm; apply fix_unique
  · apply feedback_strict hcausal
  conv_lhs => rw [feedback_unfold _ hcausal s1, feedback_unfold _ hcausal s2]
  repeat'
    first
    | rw [hlin]
    | rw [delay_linear]
  abel

theorem feedback_lti (S : Operator a a) : Causal S → Lti S → Lti (feedback S) :=
  by
  intro hcausal hlti
  constructor
  · apply feedback_linear <;> assumption
  · apply feedback_timeInvariant <;> cases hlti <;> assumption

/-- The integral operator is another fundamental operator in DBSP. It takes a
stream of changes and computes the sum of the changes so far; this is
implemented recursively with a fixpoint.

Theorem names will use 'integral' even though the operator is named I.
-/
def I : Operator a a :=
  feedback id

omit [AddCommMonoid a] in
private theorem id_causal : Causal (@id (stream a)) :=
  by
  unfold Causal
  intro s s' t heq
  apply heq; omega

private theorem id_timeInvariant : TimeInvariant (@id (stream a)) :=
  by
  unfold TimeInvariant
  simp

private theorem id_lti : Lti (@id (stream a)) :=
  by
  constructor
  · intro s1 s2; simp
  apply id_timeInvariant

@[simp]
theorem integral_causal : Causal (@I a _) :=
  by
  apply feedback_causal
  apply id_causal

theorem integral_lti : Lti (@I a _) := by
  unfold I
  apply feedback_lti
  · apply id_causal
  · apply id_lti

theorem integral_timeInvariant : TimeInvariant (@I a _) :=
  integral_lti.2

theorem integral_linear : Linear (@I a _) :=
  integral_lti.1

theorem integral_unfold : ∀ s : stream a, I s = s + delay (I s) :=
  by
  intro s
  unfold I
  apply feedback_unfold
  apply id_causal

@[simp]
theorem integral_0 (s : stream a) : I s 0 = s 0 := by rw [integral_unfold]; simp

/-- The sum of `s[0] .. s[n-1]`. This is a closed form version of the integral
operator (offset by 1), as proven in [integral_sum_vals]. -/
@[simp]
def sumVals (s : stream a) : stream a
  | 0 => 0
  | Nat.succ n => s n + sumVals s n

@[simp]
theorem sumVals_0 (s : stream a) : sumVals s 0 = 0 :=
  rfl

@[simp]
theorem sumVals_1 (s : stream a) : sumVals s 1 = s 0 := by unfold sumVals; simp

-- The sum of an all-zero stream is zero.
theorem sumVals_zero (s : stream a) : (∀ n, s n = 0) → ∀ n : ℕ, sumVals s n = 0 :=
  by
  intro hz n
  induction' n with n n_ih
  · simp
  · simp; rw [hz, n_ih]; simp

theorem delay_sumVals (s : stream a) t:
    z⁻¹ (fun i ↦ s i + sumVals s i) t = sumVals s t := by
  simp [delay]
  split_ifs; simp [*]
  have : t = (t-1).succ := by omega
  conv_rhs => rw [this]
  simp [sumVals]

theorem integral_sumVals (s : stream a) (n : ℕ) : I s n = sumVals s n.succ :=
  by
  induction' n with n n_ih
  · simp
  · rw [integral_unfold]; simp
    rw [n_ih]; rfl

@[simp]
theorem integral_zpp : I (0 : stream a) = 0 :=
  by
  funext t
  rw [integral_sumVals]; simp
  rw [sumVals_zero]; tauto

theorem integral_sprod (s1 : stream a) (s2 : stream b) :
    I (sprod (s1, s2)) = sprod (I s1, I s2) :=
  by
  funext t; simp
  repeat' rw [integral_sumVals]
  simp
  induction t
  · simp
  · simp; rename_i t_ih; rw [t_ih]; rfl

theorem integral_sprod2 (s1 : stream (stream a)) (s2 : stream (stream b)) :
    I (sprod2 (s1, s2)) = sprod2 (I s1, I s2) :=
  by
  funext m n; simp
  repeat' rw [integral_sumVals]
  simp
  induction m
  · simp
  · simp; rename_i m_ih; rw [m_ih]; rfl

theorem lifted_linear (f : a → b) : (∀ x y, f (x + y) = f x + f y) → Linear (lifting f) :=
  by
  intro hlin s1 s2; funext s; simp
  aesop

theorem integral_lift_comm (f : a → b) (s : stream a) :
    (∀ x y, f (x + y) = f x + f y) → I ((↑↑f) s) = (↑↑f) (I s) :=
  by
  intro hlin
  funext t; simp
  repeat' rw [integral_sumVals]
  induction' t with t t_ih
  · simp
  · simp at t_ih ⊢
    rw [hlin, t_ih]

theorem integral_fst_comm (s : stream (a × b)) : I ((↑↑Prod.fst) s) = (↑↑Prod.fst) (I s) :=
  by
  apply integral_lift_comm
  intro x y; simp

theorem integral_snd_comm (s : stream (a × b)) : I ((↑↑Prod.snd) s) = (↑↑Prod.snd) (I s) :=
  by
  apply integral_lift_comm
  intro x y; simp

end StreamAddMonoid

section StreamAddCommGroup
-- SPDX-License-Identifier: BSD-2-Clause
variable {a : Type} [AddCommGroup a]

variable {b : Type} [AddCommGroup b]

variable {c : Type} [AddCommGroup c]

instance streamGroup : AddCommGroup (stream a) := by unfold stream; infer_instance

@[simp]
lemma stream_sub_apply (s1 s2 : stream a) (t : ℕ) : (s1 - s2) t = s1 t - s2 t := rfl

@[simp]
lemma stream_neg_apply (s : stream a) (t : ℕ) : (-s) t = - (s t) := rfl

theorem linear_neg {S : Operator a b} (h : Linear S) : ∀ s, S (-s) = -S s :=
  by
  intro s
  have h0 := h (-s) s; simp at h0
  rw [linear_zero h] at h0
  apply add_eq_zero_iff_eq_neg.mp; rw [← h0]

theorem linear_sub {S : Operator a b} (h : Linear S) : ∀ s1 s2, S (s1 - s2) = S s1 - S s2 :=
  by
  intros
  repeat' rw [sub_eq_add_neg]
  rw [h]
  rw [linear_neg h]

theorem agreeUpto_respects_sub (s1 s2 s1' s2' : stream a) (n : ℕ) :
    (s1 =[ n ]= s1') → (s2 =[ n ]= s2') → (s1 - s2) =[n]= s1' - s2' :=
  by
  intro h1 h2
  intro t hle; simp
  rw [h1, h2] <;> assumption

theorem bilinear_sub_1 {f : Operator2 a b c} (hblin : Bilinear f) :
    ∀ x1 x2 y, f (x1 - x2) y = f x1 y - f x2 y :=
  by
  intro x1 x2 y
  have h : Linear fun x => f x y := by
    unfold Linear
    intro _ _
    apply hblin.1
  apply linear_sub h

theorem bilinear_sub_2 {f : Operator2 a b c} (hblin : Bilinear f) :
    ∀ x y1 y2, f x (y1 - y2) = f x y1 - f x y2 :=
  by
  intro x _ _
  have h : Linear (f x) := hblin.2 x
  apply linear_sub h

/-- The derivative operator, written simply `D`, is a core operator in DBSP. It
"differentiates" a stream: `(D s)(t) = s(t) - s(t - 1)` (with `(D s)(0) = 0`),
producing a stream of what we can think of as changes, although both the input
and output are streams of a's.

Theorem names related to the derivative will use 'derivative'.
-/
def D : Operator a a := fun s => s - delay s

@[simp]
theorem derivative_causal : Causal (@D a _) :=
  by
  rw [causal_to_agree]
  unfold D
  intro s s' t hagree
  apply agreeUpto_respects_sub
  assumption
  apply agreeUpto_weaken1
  apply delay_succ_upto; assumption

theorem derivative_timeInvariant : TimeInvariant (@D a _) :=
  by
  unfold TimeInvariant D
  intro s
  rw [linear_sub delay_linear]

theorem derivative_linear : Linear (@D a _) :=
  by
  intro s1 s2
  unfold D
  funext s; simp
  repeat' rw [delay_linear]
  abel_nf; simp

theorem derivative_lti : Lti (@D a _) := by
  constructor; apply derivative_linear;
  apply derivative_timeInvariant

-- simple expression for the values of derivative s
@[simp]
theorem derivative_0 (s : stream a) : D s 0 = s 0 := by unfold D ; simp

theorem derivative_difference_t (s : stream a) (t : ℕ) : 0 < t → D s t = s t - s (t - 1) :=
  by
  intro hnz
  unfold D delay; dsimp
  rw [if_neg]; omega

@[simp]
theorem derivative_zpp : D (0 : stream a) = 0 := by
  funext t; unfold D; simp

theorem sumVals_succ_n (s : stream a) (t : ℕ) : sumVals (D s) t.succ = s t :=
  by
  induction' t with t t_ih
  · unfold sumVals D; simp
  simp only [sumVals] at t_ih ⊢
  rw [derivative_difference_t] <;> try omega
  rw [t_ih]; simp

@[simp]
theorem sumVals_neg (s : stream a) (t : ℕ) : sumVals (-s) t = -sumVals s t := by
  induction t <;> simp
  rename_i t ht
  rw [ht]; abel

@[simp]
theorem derivative_integral (s : stream a) : I (D s) = s :=
  by
  funext t
  rw [integral_sumVals]
  rw [sumVals_succ_n]

-- We can give an alternative proof based on the fact that I is the unique
-- fixpoint of α = α + z⁻¹ α.
private theorem derivative_integral_alt (s : stream a) : I (D s) = s :=
  by
  symm
  simp [I, feedback]
  apply fix_unique
  · apply loop1_body_strict
    apply delay_strict
    apply add_causal
  · unfold D; abel

-- And yet another proof, based on linearity, the fixpoint equation, and time
-- invariance.
private theorem derivative_integral_alt2 (s : stream a) : I (D s) = s :=
  by
  unfold D
  rw [linear_sub integral_linear]
  rw [integral_unfold s]
  rw [integral_timeInvariant]; abel

@[simp]
theorem integral_derivative (s : stream a) : D (I s) = s :=
  by
  unfold D
  calc
    I s - delay (I s) = s + delay (I s) - delay (I s) := by congr; apply integral_unfold
    _ = s := by rw [add_sub_cancel_right]

theorem derivative_integral_inverse (α s : stream a) : α = I s ↔ D α = s :=
  by
  constructor
  · intro h; subst α
    rw [integral_derivative]
  · intro h; subst s
    rw [derivative_integral]

theorem i_d_comp : I ∘ D = @id (stream a) := by funext s; simp

theorem d_i_comp : D ∘ I = @id (stream a) := by funext s; simp

theorem derivative_sprod (s1 : stream a) (s2 : stream b) :
    D (sprod (s1, s2)) = sprod (D s1, D s2) :=
  by
  funext t; simp
  by_cases t = 0
  · subst t; simp
  · repeat' rw [derivative_difference_t] <;> try omega
    simp

end StreamAddCommGroup

-- #lint only doc_blame simp_nf

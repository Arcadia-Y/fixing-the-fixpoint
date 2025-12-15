-- Copyright 2022-2023 VMware, Inc.
import DBSP.StreamTheory.Stream
import Mathlib.Algebra.Group.Prod
import Mathlib.Tactic.SplitIfs

/-!
# DBSP operators

We define the DBSP core constructs (lifting, delay, and fixpoints) and the
associated properties of causality, time invariance, and strict causality.

This file defines properties over `stream a` that only depend on the existence
of an arbitrary "zero" element `0 : a`. This zero need not have particular
properties.

NOTE: paper implicitly assumes groups throughout, here we are able to weaken
that assumption.
-/


-- SPDX-License-Identifier: BSD-2-Clause
-- for prod.has_zero
-- for prod.has_zero
universe u v

/-- An operator is a function between streams. -/
@[reducible]
def Operator (a b : Type u) : Type u :=
  stream a → stream b

/-- An operator2 is a function on two streams.

This is isomorphic to `operator (a × b) c`, but in Lean this is easier to use;
there may be a better way to use the uncurried version to avoid defining this
specially. -/
@[reducible]
def Operator2 (a b c : Type u) : Type u :=
  stream a → stream b → stream c

/-- ↑↑f turns an ordinary function into an operator by pointwise lifting.

The paper uses ↑f for this notion, but that means a different notion (also
called lift) in mathlib.
 -/
def lifting {a b : Type u} (f : a → b) : Operator a b := fun s => fun n => f (s n)

/- ././././Mathport/Syntax/Translate/Command.lean:483:9: unsupported: advanced prec syntax std.prec.max[std.prec.max] -/
prefix:max
  "↑↑" =>-- lifting binds very tightly (similar to ⁻¹), so that ↑↑f x is (↑↑f) x
  lifting

@[simp]
theorem lifting_eq {a b : Type u} (f : a → b) (s : stream a) (n : ℕ) : (↑↑f) s n = f (s n) :=
  rfl

/-- Lift a curried function. See [lifting]. -/
def lifting2 {a b c : Type u} (f : a → b → c) : Operator2 a b c := fun s1 s2 => fun n =>
  f (s1 n) (s2 n)

@[simp]
theorem lifting2_apply {a b c : Type u} (f : a → b → c) (s1 : stream a) (s2 : stream b) (n : ℕ) :
    lifting2 f s1 s2 n = f (s1 n) (s2 n) :=
  rfl

@[simp]
theorem lifting_id {a : Type u} : (lifting fun x : a => x) = id :=
  rfl

/- ././././Mathport/Syntax/Translate/Command.lean:483:9: unsupported: advanced prec syntax std.prec.max[std.prec.max] -/
prefix:max "↑²" => lifting2

variable {a : Type u} [Zero a]

variable {b : Type u} [Zero b]

variable {c : Type u} [Zero c]

-- this is moderately dangerous because ↑ is actually recursive, so without a
-- type from the environment this can lift to `operator (stream a) (stream b)`
-- (with an arbitrary number of streams).
instance streamLift : Coe (a → b) (Operator a b) :=
  ⟨lifting⟩

/-
note that we will overload 0 for
- 0 : ℕ
- 0 : a (the group element)
- 0 : stream a (which is just [λ _, (0:a)])
-/
/-- Product of two streams as a single stream.

This is part of how multi-argument streams are formalized, which is more
explicit than in the paper.
-/
def sprod {a b : Type u} : stream a × stream b → stream (a × b) := fun s => fun n => (s.1 n, s.2 n)

@[reducible]
instance sprodCoe : Coe (stream a × stream b) (stream (a × b)) :=
  ⟨fun ⟨s1, s2⟩ n => (s1 n, s2 n)⟩


omit [Zero a] [Zero b] in
@[simp]
theorem sprod_apply (s : stream a × stream b) (n : ℕ) : (sprod s) n = (s.1 n, s.2 n) := rfl

omit [Zero a] [Zero b] in
@[simp]
theorem sprodCoe_unfold (s : stream a × stream b) (n : ℕ) :
    (↑s : stream (a × b)) n = (s.1 n, s.2 n) :=
  by
  cases' s with s1 s2
  rfl

def sprod2 {a b : Type u} : stream (stream a) × stream (stream b) → stream (stream (a × b)) :=
  fun s => fun m n => (s.1 m n, s.2 m n)

omit [Zero a] [Zero b] in
@[simp]
theorem sprod2_apply (s:  stream (stream a) × stream (stream b)) (m n : ℕ) :
    (sprod2 s) m n = (s.1 m n, s.2 m n) := rfl

/-- Convert a curried [operator2] into an ordinary [operator] over a tuple. -/
def uncurryOp (T : Operator2 a b c) : Operator (a × b) c := fun s =>
  T ((↑↑Prod.fst) s) ((↑↑Prod.snd) s)

omit [Zero a] [Zero b] [Zero c] in
theorem uncurryOp_intro (T : Operator2 a b c) (s1 : stream a) (s2 : stream b) :
    T s1 s2 = uncurryOp T (s1, s2) := by funext t; rfl

omit [Zero a] [Zero b] [Zero c] in
theorem uncurryOp_intro_sprod (T : Operator2 a b c) (s1 : stream a) (s2 : stream b) :
    T s1 s2 = uncurryOp T (sprod (s1, s2)) := by funext t; rfl

omit [Zero a] [Zero b] [Zero c] in
theorem uncurryOp_sprod_eq (F : Operator (a × b) c) :
    uncurryOp (fun s1 s2 => F (sprod (s1, s2))) = F := by funext t; rfl

theorem lifting_distributivity {a b c : Type} (f : a → b) (g : b → c) :
    lifting (g ∘ f) = lifting g ∘ lifting f :=
  rfl

theorem lifting_comp {a b c : Type} (f : a → b) (g : b → c) (s : stream a) :
    (↑↑fun x => g (f x)) s = (↑↑g) ((↑↑f) s) :=
  rfl

theorem lifting2_comp {a b c d e : Type} (f : a → c) (g : b → d) (T : c → d → e) (s1 : stream a)
    (s2 : stream b) : (↑²fun x y => T (f x) (g y)) s1 s2 = (↑²T) ((↑↑f) s1) ((↑↑g) s2) :=
  rfl

theorem lifting2_comp' {a b c d e : Type} (f : a → c) (g : b → d) (T : c → d → e) :
    (↑²fun x y => T (f x) (g y)) = fun s1 s2 => (↑²T) ((↑↑f) s1) ((↑↑g) s2) :=
  rfl

/-- The delay operator `z⁻¹` is a fundamental DBSP operator that shifts a stream over by one time
step. For `t=0` it inserts a zero element, which is the main reason a `0 : a`
(expressed with `has_zero a` here) is required.
-/
def delay : Operator a a := fun s : stream a => fun t => if t = 0 then 0 else s (t - 1)

notation "z⁻¹" => delay

/-- Time invariance intuitively expresses that an operator does not depend on
the exact time, only the sequence. It is expressed by saying that `S ∘ z⁻¹ = z⁻¹
∘ S`, that is, that the operator commutes with delay (see [time_invariant_comp]
for a proof that this definition equals that one).

Essentially all operators considered in DBSP are time invariant (although this
may not be strictly necessary).
 -/
def TimeInvariant (S : Operator a b) :=
  ∀ s, S (z⁻¹ s) = z⁻¹ (S s)

/-- Show [time_invariant] is equivalent to the definition in the paper.

The definition of [time_invariant] is easier to use in Lean since it can be used
directly as a rewrite, whereas composed functions don't appear syntactically in
proofs. -/
theorem timeInvariant_comp (S : Operator a b) : TimeInvariant S ↔ S ∘ z⁻¹ = z⁻¹ ∘ S :=
  by
  constructor <;> intro h
  · funext s; simp; rw [h]
  · intro s; apply congr_fun h s

/-- Characterizes time invariance for lifted operators: they must satisfy the
"zero preservation property", namely `f 0 = 0`. This arises because the delay
inserts a 0 at `z⁻¹ (S ↑↑f) 0`, and the function must do the same in `S (z⁻¹ (↑↑
f)) 0`. -/
theorem lifting_time_invariance (f : a → b) : TimeInvariant (lifting f) ↔ f 0 = 0 :=
  by
  unfold TimeInvariant
  constructor
  · intro h
    have heq := congr_fun (h 0) 0
    simp [delay, lifting] at heq
    assumption
  · intro h0 s
    funext t
    simp [delay, lifting]
    split_ifs <;> tauto

theorem lifting_timeInvariant (f : a → b) : f 0 = 0 → TimeInvariant (↑↑f) :=
  (lifting_time_invariance f).mpr

-- delay by definition produces 0 at time t
@[simp]
theorem delay_t_0 (s : stream a) : z⁻¹ s 0 = 0 :=
  rfl

@[simp]
theorem delay_0 : z⁻¹ (0 : stream a) = 0 := by
  funext t; unfold delay; aesop

@[simp]
theorem delay_succ (s : stream a) (n : ℕ) : z⁻¹ s n.succ = s n :=
  rfl

theorem delay_sub_1 (s : stream a) (n : ℕ) : 0 < n → z⁻¹ s n = s (n - 1) :=
  by
  intro h
  unfold delay; rw [if_neg]; omega

lemma delay_sprod (s1: stream a) (s2: stream b): z⁻¹ (sprod (s1, s2)) = sprod (z⁻¹ s1, z⁻¹ s2) :=
  by
  funext t
  simp [delay, sprod]
  split_ifs <;> rfl

theorem delay_eq_at (s1 s2 : stream a) (t : ℕ) :
    (0 < t → s1 (t - 1) = s2 (t - 1)) → z⁻¹ s1 t = z⁻¹ s2 t :=
  by
  intro heq
  unfold delay; split_ifs; simp
  apply heq; omega

theorem timeInvariant_0_0 (S : Operator a b) : TimeInvariant S → S 0 0 = 0 :=
  by
  intro hti
  unfold TimeInvariant at hti
  have h := congr_fun (hti 0) 0
  simp at h
  assumption

-- time_invariant definition applied to a specific s and t
theorem timeInvariant_t {S : Operator a b} (h : TimeInvariant S) :
    ∀ s t, S (delay s) t = delay (S s) t :=
  by
  unfold TimeInvariant at h
  intro s t
  have heq := congr_fun (h s) t
  assumption

-- this is zero-preservation over zero streams
theorem timeInvariant_zpp (S : Operator a b) : TimeInvariant S → S 0 = 0 :=
  by
  intro hti
  funext t
  conv =>
    rhs; change (0 : b)
  induction t
  · apply timeInvariant_0_0; assumption
  · rw [← delay_0]
    rw [timeInvariant_t hti]; simp
    assumption

theorem lift_timeInvariant (f : a → b) : f 0 = 0 → TimeInvariant (↑↑f) :=
  by
  intro hzpp s
  funext t ; simp
  unfold delay; split_ifs
  · apply hzpp
  · simp

theorem delay_timeInvariant : TimeInvariant (@delay a _) := by intro s; rfl

theorem lifting2_timeInvariant (f : a → b → c) : TimeInvariant (uncurryOp (↑²f)) ↔ f 0 0 = 0 :=
  by
  constructor
  · intro h
    apply congr_fun (h 0) 0
  · intro h0 s
    funext t
    simp [delay, lifting2, uncurryOp]
    split_ifs <;> tauto

/-- A causal operator intuitively depends at time `t` only on previous inputs.
Note that an operator can use its input at time `t` itself; imagine all
operators operate synchronously, and we compute all of them before emitting the
output. The formal definition says that if two streams agree up to time t, then
S must return the same result at time t for both.
-/
def Causal (S : Operator a b) :=
  ∀ s s' : stream a, ∀ t, (s =[t]= s') → S s t = S s' t

omit [Zero a] [Zero b] in
@[simp]
theorem lifting_causal (f : a → b) : Causal (lifting f) :=
  by
  intro s s' t hpre
  simp [lifting]
  rw [hpre t]
  omega

theorem delay_causal : Causal (@delay a _) :=
  by
  intro s s' t hpre
  simp [Causal, delay]
  rw [hpre]
  omega

-- composition of two causal operators is causal
omit [Zero a] [Zero b] [Zero c] in
theorem causal_comp_causal (S1 : Operator a b) (h1 : Causal S1) (S2 : Operator b c)
    (h2 : Causal S2) : Causal fun s => S2 (S1 s) :=
  by
  intro s1 s2 n heq; simp
  apply h2
  intro i hle
  apply h1
  intro j hle_j; apply heq; omega

-- another version
omit [Zero a] [Zero b] [Zero c] in
theorem causal_comp (S1 : Operator a b) (h1 : Causal S1) (S2 : Operator b c)
    (h2 : Causal S2) : Causal (S2 ∘ S1) := by
  apply causal_comp_causal S1 <;> tauto

omit [Zero a] [Zero b] [Zero c] in
theorem causal_sprod_causal (S1 : Operator a b) (h1 : Causal S1) (S2 : Operator a c)
    (h2 : Causal S2) : Causal (fun x => sprod (S1 x, S2 x)) := by
  intro s1 s2 n heq; simp
  constructor
  · apply h1; tauto
  · apply h2; tauto

omit [Zero a] [Zero b] in
theorem causal_respects_agreeUpto (S : Operator a b) (h : Causal S) (s1 s2 : stream a) (n : ℕ) :
    (s1 =[ n ]= s2) → (S s1 =[ n ]= S s2) := by
  intro heq n hle
  apply h
  intro _ hle'; apply heq; omega

omit [Zero a] [Zero b] in
theorem causal_to_agree (S : Operator a b) : Causal S ↔ ∀ s1 s2 n, (s1 =[ n ]= s2) → (S s1 =[ n ]= S s2) :=
  by
  constructor
  · intro s1 s2 n h
    apply causal_respects_agreeUpto ; assumption
  intro heq_n
  intro s1 s2 t hagree
  apply heq_n _ _ t
  · intro i; apply hagree
  omega

-- More convenient definition of causal for two-argument operators. `causal
-- (uncurry_op T)` is a convenient way to re-use the definition of causal, but
-- this is easier to use for the curried operator directly.
omit [Zero a] [Zero b] [Zero c] in
theorem causal2 (T : Operator2 a b c) :
    Causal (uncurryOp T) ↔
      ∀ s1 s1' s2 s2' n, (s1 =[ n ]= s1') → (s2 =[ n ]= s2') → T s1 s2 n = T s1' s2' n :=
  by
  constructor
  · intro hcausal
    intro s1 s1' s2 s2' n h1 h2
    have h := hcausal (sprod (s1, s2)) (sprod (s1', s2')) n
    unfold uncurryOp sprod at h; simp at h
    apply h
    · intro i hle; simp
      rw [h1, h2] <;> try omega
      constructor <;> rfl
  · intro h; intro _ _ _ heq
    unfold uncurryOp
    apply h
    · intro i hle; simp
      rw [heq]; omega
    · intro i hle; simp
      rw [heq]; omega

omit [Zero a] [Zero b] [Zero c] in
theorem causal2_agree (T : Operator2 a b c) :
    Causal (uncurryOp T) →
      ∀ s1 s1' s2 s2' n, (s1 =[ n ]= s1') → (s2 =[ n ]= s2') → (T s1 s2 =[ n ]= T s1' s2') :=
  by
  rw [causal2]; introv hcausal heq1 heq2
  intro m hle
  apply hcausal
  apply agreeUpto_weaken; assumption; omega
  apply agreeUpto_weaken; assumption; omega

omit [Zero a] [Zero b] [Zero c] in
theorem uncurryOp_lifting {d : Type u} [AddCommGroup d] (f : c → d)
    (t : stream a → stream b → stream c) :
    (uncurryOp fun (x : stream a) (y : stream b) => (↑↑f) (t x y)) = ↑↑f ∘ uncurryOp t := by
  funext xy t; simp [uncurryOp]

-- causal (uncurry_op T) can be weakened to a specific fixed first argument
omit [Zero a] [Zero b] in
theorem causal_uncurryOp_fixed (T : Operator2 a b b) : Causal (uncurryOp T) → ∀ s, Causal (T s) :=
  by
  intro hcausal
  intro s s' n heq
  rw [causal2] at hcausal
  apply hcausal; rfl

omit [Zero a] [Zero b] [Zero c] in
theorem lifting_lifting2_comp {d : Type u} [Zero d] (f : c → d) (g : a → b → c) :
    ∀ s1 s2, (↑↑f) ((↑²g) s1 s2) = (↑²fun x y => f (g x y)) s1 s2 := by intro s1 s2; funext t; simp

omit [Zero a] [Zero b] [Zero c] in
theorem uncurryOp_lifting2 (f : a → b → c) : uncurryOp (↑²f) = ↑fun xy : a × b => f xy.1 xy.2 := rfl

/-- Strictly causal. Similar to [causal], a strictly causal (or simply _strict_)
operator depends only on past inputs; unlike causal, a strict operator at time
`n` can depend only on `t < n` and not `n` itself. -/
def Strict (S : Operator a b) :=
  ∀ s s' : stream a, ∀ t, (∀ i < t, s i = s' i) → S s t = S s' t

omit [Zero a] [Zero b] in
/-- Strictly causal operators have a unique output at time 0 (because they
aren't allowed to depend on the input at time 0), but it need not actually be 0.
That requirement can come from [time_invariant].
-/
theorem strict_unique_zero (S : Operator a b) (h : Strict S) : ∀ s s', S s 0 = S s' 0 :=
  by
  intro s s'
  apply h
  intro i hcontra
  by_contra
  apply Nat.not_lt_zero; assumption

omit [Zero a] [Zero b] in
theorem strict_causal_to_causal (S : Operator a b) : Strict S → Causal S :=
  by
  intro hstrict
  intro s s' t hpre
  apply hstrict
  intro i hlt
  apply hpre; omega

theorem delay_strict : Strict (@delay a _) :=
  by
  intro s s' t hpre
  simp [Causal, delay]
  split_ifs <;>
    try
      first
      | simp
      | assumption
  apply hpre; omega

omit [Zero a] [Zero b] [Zero c] in
theorem causal_strict_strict (F : Operator a b) (hstrict : Strict F) (T : Operator b c)
    (hcausal : Causal T) : Strict fun α => T (F α) :=
  by
  intro s1 s2 n hagree
  simp
  apply hcausal
  intro i hle
  apply hstrict
  intro j hjle
  apply hagree; omega

omit [Zero a] [Zero b] [Zero c] in
theorem strict_causal_strict (F : Operator a b) (hcausal : Causal F) (T : Operator b c)
    (hstrict : Strict T) : Strict fun α => T (F α) :=
  by
  intro s1 s2 n hagree
  simp
  apply hstrict
  intro i hle
  apply hcausal
  intro j hjle
  apply hagree; omega

/- To construct the fixpoint of F, we first define nth F n, which is F (F ... (F
0)) with (n+1) copies of F. The fixpoint [fix] turns out to be `nth F n n` - the nth
iterate is correct up to time n. -/
def nth (F : Operator a a) : ℕ → stream a
  |-- We apply F at the bottom so that fix F 0 is given by F rather than being
    -- forced to be (0 : a). This seems to generalize the paper, which doesn't
    -- consider such operators! (The assumption that everything is time invariant
    -- forces operators to have F 0 0 = 0, as proven in [time_invariant_0_0].)
    Nat.zero =>
    F 0
  | Nat.succ n => F (nth F n)

@[simp]
theorem nth_0 (F : Operator a a) : nth F 0 = F 0 :=
  rfl

@[simp]
theorem nth_succ (F : Operator a a) (n : ℕ) : nth F n.succ = F (nth F n) :=
  rfl

/-- `fix (α, F α)` for a [strict] operator `F` is a fundamental operator that
implements a form of recursion. It is a fixpoint in that `fix F` is a solution
to `α = F(α)`.  When `F` is [strict], this recursion is well-defined: `fix F = F
(fix F)` (see [fix_eq]), and the solution is unique (see [fix_unique]).

Note that in this formalization, `fix F` always produces _some_ stream; however,
if F is not strict, then it need not satisfy `fix F = F (fix F)`.
 -/
def fix (F : Operator a a) : stream a := fun t => nth F t t

@[simp]
theorem fix_0 (F : Operator a a) : fix F 0 = F 0 0 :=
  rfl

theorem strict_zpp_zero (S : Operator a b) (hstrict : Strict S) (hzpp : S 0 0 = 0) :
    ∀ s, S s 0 = 0 := by
  intro s
  calc
    S s 0 = S 0 0 := by
      apply strict_unique_zero
      assumption
    _ = 0 := by apply hzpp

omit [Zero a] [Zero b] in
theorem strict_agree_at_next (S : Operator a b) (hstrict : Strict S) :
    ∀ s s' n, agreeUpto n s s' → S s n.succ = S s' n.succ :=
  by
  unfold agreeUpto
  intro s s' n hagree
  apply hstrict
  intro i hlt
  apply hagree; omega

omit [Zero a] [Zero b] in
theorem agreeUpto_strict_extend (S : Operator a b) (hstrict : Strict S) (s s' : stream a) :
    ∀ n, (s =[ n ]= s') → S s =[n.succ]= S s' :=
  by
  intro n hagree
  intro t hle
  apply hstrict
  intro i hlt
  apply hagree; omega

/-
We don't actually use this characterization of strictness, but it might help
build intuition.
-/
omit [Zero a] [Zero b] in
theorem strict_as_agreeUpto (S : Operator a b) :
    Strict S ↔ (∀ s s', (S s =[ 0 ]= S s')) ∧ ∀ s s' n, (s =[ n ]= s') → S s =[n.succ]= S s' :=
  by
  unfold Strict
  constructor
  · intro hstrict
    constructor
    · intro s s'
      rw [agreeUpto_0]
      apply hstrict
      intro i hlt0
      exfalso
      apply Nat.not_lt_zero _ hlt0
    · intro s s' n hagree
      apply agreeUpto_strict_extend <;> assumption
  · intro h
    cases' h with h_zpp h_agree_extend
    intro s s' t hagree
    have h : t = 0 ∨ 0 < t := by omega
    cases h
    · subst t; apply h_zpp; omega
    · apply h_agree_extend _ _ (t - 1)
      intro i hle
      apply hagree; omega; omega

theorem delay_succ_upto (s1 s2 : stream a) (n : ℕ) : (s1 =[ n ]= s2) → delay s1 =[n.succ]= delay s2 :=
  by
  intro heqn
  unfold agreeUpto
  intro t
  intro hle
  unfold delay
  rw [heqn] ; omega

private theorem and_wlog2 {p1 p2 : Prop} (h2 : p2) (h21 : p2 → p1) : p1 ∧ p2 :=
  ⟨h21 h2, h2⟩

private theorem nth_fix_agree_aux (F : Operator a a) (hstrict : Strict F) (n : ℕ) :
    ((nth F n =[ n ]= fix F)) ∧ (fix F =[ n ]= F (fix F)) :=
  by
  induction' n with n n_ih
  · rw [agreeUpto_0, agreeUpto_0]
    constructor
    · rfl
    · unfold fix; simp [nth]
      apply strict_unique_zero; assumption
  conv =>
    lhs; lhs
    change F (nth F n)
  cases' n_ih with h_fix h_unfold
  have h : F (nth F n) =[n.succ]= F (fix F) :=
    by
    apply agreeUpto_strict_extend _ hstrict
    exact h_fix
  apply and_wlog2
  · apply agreeUpto_extend
    · exact h_unfold
    · simp [fix, nth]
      apply strict_agree_at_next _ hstrict
      exact h_fix
  · intro h2
    -- BUG: prove by reflexivity to instantiate the n argument to agree_upto
    -- (Lean seems to ignore the n in the first relation)
    calc
      F (nth F n) =[n.succ]= F (nth F n) := by apply agree_refl n.succ
      _ =[n.succ]= F (fix F) := by assumption
      _ =[n.succ]= fix F := by symm; assumption

-- The key characterization of fix F.
theorem fix_eq (F : Operator a a) (hstrict : Strict F) : fix F = F (fix F) :=
  by
  funext t
  have h := nth_fix_agree_aux _ hstrict t
  cases' h with _ h_unfold
  apply h_unfold; omega

-- We show two solutions α to α = F(α) are equal, from which obviously
-- they are all equal to fix F, which is one such solution from [fix_eq]
--
-- Users will typically want the special case of [fix_unique], which is written
-- in terms of our particular solution [fix].
omit [Zero a] in
private theorem fixpoints_unique (F : Operator a a) (hstrict : Strict F)
    (α β : stream a) :-- α and β are two possible solutions
        α =
        F α →
      β = F β → α = β :=
  by
  intro hα hβ
  rw [agree_everywhere_eq]; intro n
  induction' n with n
  · rw [hα]; rw [hβ]
    rw [agreeUpto_0]
    apply strict_unique_zero; assumption
  · rw [hα]; rw [hβ]
    apply agreeUpto_strict_extend; assumption
    assumption

theorem fix_unique (F : Operator a a) (hstrict : Strict F) (α : stream a) (h_fix : α = F α) :
    α = fix F := by
  apply fixpoints_unique _ hstrict α (fix F)
  · assumption
  · apply fix_eq; assumption

omit [Zero a] [Zero b] in
theorem loop1_body_strict (F : Operator b b) (hstrict : Strict F) (T : Operator2 a b b)
    (hcausal : Causal (uncurryOp T)) (s : stream a) : Strict fun α => T s (F α) :=
  by
  apply causal_strict_strict
  · apply hstrict
  · apply causal_uncurryOp_fixed; assumption

omit [Zero a] in
theorem loop1_unfold (F : Operator b b) (hstrict : Strict F) (T : Operator2 a b b)
    (hcausal : Causal (uncurryOp T)) (s : stream a) :
    (fix fun α => T s (F α)) = T s (F (fix fun α => T s (F α))) :=
  by
  apply fix_eq
  apply loop1_body_strict <;> assumption

omit [Zero a] in
theorem loop1_causal
  (T : Operator (a × b) b)  (hT : Causal T) :
    Causal fun s => fix fun x => T (sprod (s, z⁻¹ x)) := by
  intro s1 s2 n h; simp [fix]
  suffices ∀ t ≤ n,
      nth (fun x ↦ T (sprod (s1, z⁻¹ x))) n t = nth (fun x ↦ T (sprod (s2, z⁻¹ x))) n t by
    apply this; simp
  induction n
  · simp; apply hT
    intro x hx; simp; apply h; tauto
  · rename_i n ih; simp
    intros t ht; apply hT
    intro t2 ht2; simp; constructor
    · apply h; omega
    rcases t2 <;> simp
    rename_i t2; apply ih
    swap; omega
    intro x hx; apply h; omega

theorem loop1_timeInvariant
   (F : Operator b b)
   (fstrict : Strict F) (fti : TimeInvariant F)
   (T: Operator2 a b b)
   (tcausal : Causal (uncurryOp T)) (tti : TimeInvariant (uncurryOp T)) :
    TimeInvariant (fun s => fix fun α  => T s (F α)) := by
  intro s; simp
  have : ∀ α s, α = T s (F α) -> (z⁻¹ α) = T (z⁻¹ s) (F (z⁻¹ α)) := by
    intro α s h
    nth_rw 1 [h]; nth_rw 1 [uncurryOp_intro_sprod T]
    rw [<- tti]
    rw [delay_sprod, <- fti]
    rw [<- uncurryOp_intro_sprod]
  have eq := loop1_unfold F fstrict T tcausal s
  apply this at eq
  apply (fix_unique fun α => T (z⁻¹ s) (F α)) at eq; tauto
  apply loop1_body_strict <;> tauto

section fix2

def fix2 (F : Operator (stream a) (stream a)) : stream (stream a) := fun n t => nth F t n t

def AgreeNested (n t : ℕ) (s1 s2 : stream (stream a)) :=
  ∀ n' ≤ n, ∀ t' ≤ t, s1 n' t' = s2 n' t'

def CausalNested (Q : Operator (stream a) (stream b)) :=
  ∀ (s s': stream (stream a)),
    ∀ n t, AgreeNested n t s s' ->
    Q s n t = Q s' n t

-- The original definition is based on '<' on nested streams
-- This is an equivalent definition
def Strict2 (Q : Operator (stream a) (stream b)) :=
  ∀ (s s': stream (stream a)),
    ∀ n t, (∀ n' ≤ n, ∀ t' < t, s n' t' = s' n' t') ->
    Q s n t = Q s' n t

omit [Zero a] [Zero b] in
theorem casualNested_is_causal (Q : Operator (stream a) (stream b)) :
    CausalNested Q → Causal Q := by
  unfold CausalNested Causal; intro hc
  intro s1 s2 n h
  funext t; apply hc
  intros n1 hn1 t1 ht1
  specialize h n1 hn1
  rw [h]

omit [Zero a] [Zero b] in
theorem strict2_is_causalNested (Q : Operator (stream a) (stream b)) :
    Strict2 Q → CausalNested Q := by
  unfold Strict2 CausalNested; intro hstrict
  intros _ _ _ _ heq
  apply hstrict; intros;
  apply heq  <;> omega

omit [Zero a] [Zero b] in
theorem strict2_agree_0 (F : Operator (stream a) (stream b)) (hstrict : Strict2 F) :
    ∀ s s' n, F s n 0 = F s' n 0 := by
  intros; apply hstrict
  intros _ _ t' _
  have hcontra : ¬t' < 0 := by omega
  contradiction

omit [Zero b] in
theorem strict2_eq_0 (F : Operator (stream a) (stream b)) (hstrict : Strict2 F) :
    ∀ s n, F s n 0 = F 0 n 0 := by intros; apply strict2_agree_0 _ hstrict

def agreeUpto2 (t : ℕ) (s1 s2 : stream (stream a)) :=
  ∀ n, ∀ t' ≤ t, s1 n t' = s2 n t'
local notation:35 s1 " =[[" t "]]= " s2 => agreeUpto2 t s1 s2

omit [Zero a] in
theorem agreeUpto2_symm (t : ℕ) (s1 s2 : stream (stream a)) : (s1 =[[ t ]]= s2) → (s2 =[[ t ]]= s1) :=
  by
  unfold agreeUpto2; intros
  aesop

omit [Zero a] in
theorem agreeUpto2_trans (t : ℕ) (s1 s2 s3 : stream (stream a)) :
    (s1 =[[ t ]]= s2) → (s2 =[[ t ]]= s3) → (s1 =[[ t ]]= s3) :=
  by
  unfold agreeUpto2; intros _ _ n t' _
  trans s2 n t' <;> aesop

omit [Zero a] in
theorem agreeUpto2_0 (s1 s2 : stream (stream a)) : (s1 =[[ 0 ]]= s2) ↔ ∀ n, s1 n 0 = s2 n 0 :=
  by
  unfold agreeUpto2
  constructor <;> introv h <;> aesop


omit [Zero a] in
theorem agreeUpto2_extend (t : ℕ) (s s' : stream (stream a)) :
    (s =[[ t ]]= s') → (∀ n, s n t.succ = s' n t.succ) → s =[[t.succ]]= s' :=
  by
  intro hagree heqn
  unfold agreeUpto2; intros n t' _
  have ht' : t' ≤ t ∨ t' = t.succ := by omega
  cases ht' <;> aesop

omit [Zero a] [Zero b] in
theorem agreeUpto2_strict_extend (S : Operator (stream a) (stream b)) (hstrict : Strict2 S)
    (s s' : stream (stream a)) : ∀ t, (s =[[t]]= s') → S s =[[t.succ]]= S s' :=
  by
  introv hagree
  unfold agreeUpto2; intros
  apply hstrict
  intro n' _ t'' _
  have h1 : t'' ≤ t := by omega
  apply hagree; tauto

omit [Zero a] [Zero b] in
theorem strict_agree2_at_next (S : Operator (stream a) (stream b)) (hstrict : Strict2 S) :
    ∀ s s' t, (s =[[ t ]]= s') → ∀ n, S s n t.succ = S s' n t.succ :=
  by
  unfold agreeUpto2
  intro s s' t hagree n
  apply hstrict
  intros; apply hagree; omega

private theorem nth_fix2_agree_aux (F : Operator (stream a) (stream a)) (hstrict : Strict2 F)
    (t : ℕ) : ((nth F t =[[ t ]]= fix2 F)) ∧ (fix2 F =[[ t ]]= F (fix2 F))  :=
  by
  induction' t with t ih
  · rw [agreeUpto2_0, agreeUpto2_0]
    constructor
    · intros; unfold fix2; rfl
    · intros; unfold fix2; simp
      apply strict2_agree_0 _ hstrict
  conv =>
    lhs; lhs
    change F (nth F t)
  cases' ih with h_fix h_unfold
  have h : F (nth F t) =[[t.succ]]= F (fix2 F) := by apply agreeUpto2_strict_extend <;> assumption
  apply and_wlog2
  · apply agreeUpto2_extend
    · exact h_unfold
    · intro n
      simp [fix2, nth]
      apply strict_agree2_at_next _ hstrict
      exact h_fix
  · intro h2
    apply agreeUpto2_trans; assumption
    apply agreeUpto2_symm; assumption

theorem fix2_eq (F : Operator (stream a) (stream a)) (hstrict : Strict2 F) :
    fix2 F = F (fix2 F) := by
  funext n t
  have h := nth_fix2_agree_aux _ hstrict t
  cases' h with _ h_unfold
  apply h_unfold; omega

omit [Zero a] in
theorem agree2_everywhere_eq (s1 s2 : stream (stream a)) : (∀ t, (s1 =[[ t ]]= s2)) → s1 = s2 :=
  by
  intro heq
  funext n t
  apply heq t; omega

omit [Zero a] in
private theorem fixpoints2_unique (F : Operator (stream a) (stream a)) (hstrict : Strict2 F)
    (α β : stream (stream a)) :-- α and β are two possible solutions
        α =
        F α →
      β = F β → α = β :=
  by
  intro hα hβ
  apply agree2_everywhere_eq; intro n
  induction' n with n
  · rw [hα]; rw [hβ]
    intro n t' hle
    have ht : t' = 0 := by omega
    subst ht
    apply strict2_agree_0; assumption
  · rw [hα]; rw [hβ]
    apply agreeUpto2_strict_extend; assumption
    assumption

theorem fix2_unique (F : Operator (stream a) (stream a)) (hstrict : Strict2 F)
    (α : stream (stream a)) (h_fix : α = F α) : α = fix2 F :=
  by
  apply fixpoints2_unique _ hstrict α (fix2 F)
  · assumption
  · apply fix2_eq; assumption

theorem lifting_delay_strict2 : Strict2 ↑↑(@delay a _) :=
  by
  unfold Strict2; introv heq
  unfold delay; simp
  split_ifs <;> try rfl
  apply heq <;> omega

omit [Zero a] [Zero b] in
@[simp]
theorem causalNested_const (c : stream (stream b)) :
    CausalNested fun _ : stream (stream a) => c := by unfold CausalNested; intros; rfl

omit [Zero a] in
theorem causalNested_id : CausalNested fun x : stream (stream a) => x := by
  unfold CausalNested;
  intros _ _ _ _ heq; apply heq <;> omega

omit [Zero a] [Zero b] [Zero c] in
theorem causalNested_comp (Q1 : Operator (stream b) (stream c))
    (Q2 : Operator (stream a) (stream b)) :
    CausalNested Q1 → CausalNested Q2 → CausalNested fun s => Q1 (Q2 s) :=
  by
  intro h1 h2
  unfold CausalNested; intros _ _ _ _ heq
  apply h1; unfold AgreeNested; intros
  apply h2; unfold AgreeNested; intros
  apply heq <;> omega

omit [Zero a] [Zero b] in
@[simp]
theorem causalNested_lifting (Q : Operator a b) : Causal Q → CausalNested (↑↑Q) :=
  by
  intro h
  unfold CausalNested; intros _ _ _ _ heq; simp
  rw [h]
  intro t' hle
  apply heq <;> omega

omit [Zero a] in
theorem causalNested_loop
  (T : Operator (stream (a × b)) (stream b)) (hT : CausalNested T) :
    CausalNested fun s => fix fun x => T (sprod2 (s, z⁻¹ x))  := by
  intro s1 s2 n t h; simp [fix]
  suffices ∀ n' ≤ n,
      nth (fun x ↦ T (sprod2 (s1, z⁻¹ x))) n n' t = nth (fun x ↦ T (sprod2 (s2, z⁻¹ x))) n n' t by
    apply this; simp
  revert t; induction n <;> intro t h n' hn'
  · apply hT; simp
    intro n2 hn2 t2 ht2; simp; apply h <;> omega
  · rename_i n ih
    simp; apply hT
    intros n2 hn2 t2 ht2; simp
    constructor
    · apply h <;> omega
    · rcases n2 <;> simp
      apply ih <;> try omega
      intro _ _ _ _; apply h <;> omega

omit [Zero a] [Zero b] in
theorem causalNested_strict2_strict2
  (T : Operator (stream (a × b)) (stream b)) (hT : CausalNested T)
  (F: Operator (stream b) (stream b)) (hF: Strict2 F) (s: stream (stream a)):
    Strict2 fun x => T (sprod2 (s, F x)) := by
  intro s1 s2 n t h; simp
  apply hT; intro n1 hn1 t1 ht1; simp
  apply hF; intros; apply h <;> omega

omit [Zero a] in
theorem causalNested_loop_lifted
   (T : Operator (stream (a × b)) (stream b)) (hT : CausalNested T):
    CausalNested fun s => fix2 (fun x => T (sprod2 (s, ↑↑z⁻¹ x))) := by
  intro s1 s2 n t h; simp [fix2]
  suffices ∀ t' ≤ t,
      nth (fun x ↦ T (sprod2 (s1, ↑↑z⁻¹ x))) t n t' = nth (fun x ↦ T (sprod2 (s2, ↑↑z⁻¹ x))) t n t' by
    apply this; simp
  revert n; induction t <;> intro n h t' ht'
  · apply hT; unfold AgreeNested; simp
    intro n2 hn2 t2 ht2; apply h <;> omega
  · rename_i t ih
    simp; apply hT
    intros n2 hn2 t2 ht2; simp
    constructor
    · apply h <;> omega
    · rcases t2 <;> simp
      apply ih <;> try omega
      unfold AgreeNested
      intros; apply h <;> omega

-- Copyright 2022-2023 VMware, Inc.
import DBSP.StreamTheory.Operators
import DBSP.StreamTheory.Linear
import DBSP.StreamTheory.StreamElim
import DBSP.StreamTheory.Incremental

-- SPDX-License-Identifier: BSD-2-Clause
namespace ckt

section Ckts

variable (Func : ∀ (a b : Type) [AddCommGroup a] [AddCommGroup b], Type)

variable  (Func_denote : ∀ {a b : Type} [AddCommGroup a] [AddCommGroup b], Func a b → a → b)

inductive Ckt : ∀ (a b : Type) [AddCommGroup a] [AddCommGroup b], Type 1
  | delay {a : Type} [AddCommGroup a] : Ckt a a
  | derivative {a : Type} [AddCommGroup a] : Ckt a a
  | integral {a : Type} [AddCommGroup a] : Ckt a a
  | incremental {a b : Type} [AddCommGroup a] [AddCommGroup b] (f : Ckt a b) : Ckt a b
  |
  lifting {a b : Type} [AddCommGroup a] [AddCommGroup b] (f : Func a b) :
    Ckt a b-- | Ckt_lift {a b: Type} [add_comm_group a] [add_comm_group b]
--   (f: Ckt a b) : Ckt (stream a) (stream b)

  |
  seq {a b c : Type} [AddCommGroup a] [AddCommGroup b] [AddCommGroup c] (f1 : Ckt a b)
    (f2 : Ckt b c) : Ckt a c
  |
  par {a₁ b₁ a₂ b₂ : Type} [AddCommGroup a₁] [AddCommGroup a₂] [AddCommGroup b₁] [AddCommGroup b₂]
    (f1 : Ckt a₁ b₁) (f2 : Ckt a₂ b₂) : Ckt (a₁ × a₂) (b₁ × b₂)
  | feedback {a b : Type} [AddCommGroup a] [AddCommGroup b] (F : Ckt (a × b) b) : Ckt a b

-- | intro {a: Type} [add_comm_group a]
--   : Ckt a (stream a)
-- | elim {a: Type} [add_comm_group a]
--   : Ckt (stream a) a
local notation "Ckt" => Ckt Func
local notation f1 " ~~> " f2:25 => Ckt f1 f2

variable {a b c d : Type} [AddCommGroup a] [AddCommGroup b] [AddCommGroup c] [AddCommGroup d]

def denote {a b: Type} [AddCommGroup a] [AddCommGroup b] (c : Ckt a b) : stream a → stream b :=
  match c with
  | Ckt.delay => delay
  | Ckt.derivative => D
  | Ckt.integral => I
  | Ckt.incremental f => incremental (denote f)
  | Ckt.lifting f => ↑↑(Func_denote f)
  | Ckt.seq f1 f2 => denote f2 ∘ denote f1
  | Ckt.par f1 f2 => uncurryOp fun x1 x2 =>
      sprod (denote f1 x1, denote f2 x2)
  | Ckt.feedback F => fun s => fix fun α => denote F (sprod (s, z⁻¹ α))

local notation "denote" => denote Func Func_denote

def Equiv (f1 f2 : Ckt a b) :=
  denote f1 = denote f2

local infixl:50 " === " => Equiv Func Func_denote

@[refl]
theorem equiv_refl (f : Ckt a b) : f === f := by simp [Equiv]

@[symm]
theorem equiv_symm ( f1 f2 : Ckt a b ) : f1 === f2 → f2 === f1 := by
  simp [Equiv]; cc

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Mathlib.Tactic.CC._root_.Mathlib.Tactic.cc'
@[trans]
  theorem equiv_trans
    ( f1 f2 f3 : Ckt a b ) : f1 === f2 → f2 === f3 → f1 === f3
    := by unfold Equiv ; cc

@[simp]
theorem denote_seq (f1 : Ckt a b) (f2 : Ckt b c) :
    denote (Ckt.seq f1 f2) = fun x => denote f2 (denote f1 x) :=
  rfl

@[simp]
theorem denote_par (f1 : Ckt a b) (f2 : Ckt c d) :
    denote (Ckt.par f1 f2) = uncurryOp fun x1 x2 => sprod (denote f1 x1, denote f2 x2) :=
  rfl

@[simp]
theorem denote_delay : denote Ckt.delay = @delay a _ :=
  rfl

@[simp]
theorem denote_derivative : denote Ckt.derivative = @D a _ :=
  rfl

@[simp]
theorem denote_incremental (f : Ckt a b) : denote (Ckt.incremental f) = denote f^Δ :=
  rfl

@[simp]
theorem denote_integral : denote Ckt.integral = @I a _ :=
  rfl

@[simp]
theorem denote_lifting (f : Func a b) : denote (Ckt.lifting f) = ↑↑(Func_denote f) :=
  rfl

-- @[simp]
-- lemma denote_Ckt_lift (f: Ckt a b) :
--   denote (Ckt.Ckt_lift f) = ↑↑(denote f) := rfl.
@[simp]
theorem denote_feedback (F : Ckt (a × b) b) :
    denote (Ckt.feedback F) = fun s => fix fun α => denote F (sprod (s, z⁻¹ α)) :=
  rfl

-- @[simp]
-- lemma denote_intro :
--   denote (@Ckt.intro a _) = ↑↑δ0 := rfl.
--
-- @[simp]
-- lemma stream_elim_intro :
--   denote (@Ckt.elim a _) = ↑↑∫ := rfl.
local notation:55 x " >>> " y:55 => Ckt.seq x y

-- These definitions rely on being able to lift a few fixed functions; they
-- still make sense, but with relatively complicated assumptions that these
-- functions are available in [Func] with the appropriate meaning according to
-- [Func_denote].
/-
def lifting2 (f: a → b → c) : Ckt (a × b) c :=
  Ckt.lifting (λ xy, f xy.1 xy.2).

def derivative : Ckt a a :=
  Ckt.lifting (λ a, (a, a)) >>> Ckt.par (Ckt.lifting id) Ckt.delay >>>
  Ckt.lifting2 (λ x y, x - y).

theorem derivative_denote :
  @derivative a _ === Ckt.derivative :=
begin
  unfold derivative,
  funext s, simp,
  unfold lifting2, simp,
  funext t, simp,
  refl,
end

def integral : Ckt a a :=
  Ckt.feedback (Ckt.lifting2 (λ x y, x + y)).

theorem integral_denote :
  @integral a _ === Ckt.integral :=
begin
  unfold integral,
  funext s, simp,
  unfold lifting2, simp,
  unfold I feedback, simp,
  refl,
end
-/
def Ckt_causal (f : Ckt a b) : Causal (denote f) :=
  by
  induction f <;> try simp
  · apply delay_causal
  · apply causal_incremental; assumption
  · apply causal_comp_causal <;> assumption
  · rw [causal2]
    introv heq1 heq2
    simp
    rename_i f_ih_f1 f_ih_f2
    constructor
    · apply f_ih_f1; assumption
    · apply f_ih_f2; assumption
  · rename_i f_a f_b _ _ f_F f_ih
    apply
      loop1_causal delay _ fun (s : stream f_a) (α : stream f_b) =>
        denote f_F (sprod (s, α))
    rw [causal2]
    introv heq1 heq2
    apply f_ih
    intro m hle; simp
    constructor;
    · apply heq1; omega
    · apply heq2; omega
    apply delay_strict

-- def isStrict (f : Ckt a b) : {b : Bool | b → Strict (denote f)} :=
--   by
--   induction f <;> simp
--   · use True; simp; apply delay_strict
--   ·-- derivative
--     use False
--   ·-- integral
--     use False
--   · -- incremental
--     cases' f_ih with b hstrict; simp at *
--     use b; intro hb
--     unfold incremental
--     apply causal_strict_strict; swap; simp
--     apply strict_causal_strict; simp
--     tauto
--   ·-- lifting
--     use False
--   · -- seq (composition)
--     cases' f_ih_f1 with b1 hstrict1
--     cases' f_ih_f2 with b2 hstrict2; simp at *
--     use b1 || b2; simp
--     intro h; cases h <;> skip
--     apply causal_strict_strict; tauto; apply Ckt_causal
--     apply strict_causal_strict; apply Ckt_causal; tauto
--   · -- par
--     cases' f_ih_f1 with b1 hstrict1; cases' f_ih_f2 with b2 hstrict2
--     use b1 && b2; simp at *; intro h1 h2
--     intro s1 s2 n heq
--     unfold uncurryOp sprod; simp
--     constructor
--     · apply hstrict1 h1; intros; simp; rw [HEq]; omega
--     · apply hstrict2 h2; intros; simp; rw [HEq]; omega
--   · use False

/-
def incrementalize (f: Ckt a b) : Ckt a b :=
  Ckt.integral >>> f >>> Ckt.derivative.

theorem incrementalize_ok (f: Ckt a b) :
 denote (incrementalize f) = (denote f)^Δ :=
begin
  unfold incrementalize, simp,
  funext s, rw incremental_unfold,
end
-/
theorem seq_assoc (f1 : Ckt a b) (f2 : Ckt b c) (f3 : Ckt c d) :
    (f1 >>> f2) >>> f3 === f1 >>> f2 >>> f3 := by unfold Equiv; simp

-- section RecursiveOpt

-- variable
--   (opt :
--     ∀ {a b : Type} [inst1 : AddCommGroup a] [inst2 : AddCommGroup b],
--       (@Ckt a b inst1 inst2) → Option (@Ckt a b inst1 inst2))

-- def recursiveOpt : Ckt a b → Ckt a b := by
--   intro f; induction f
--   · apply (opt <| Ckt.delay).getD Ckt.delay
--   · apply (opt <| Ckt.derivative).getD Ckt.derivative
--   · apply (opt <| Ckt.integral).getD Ckt.integral
--   · apply (opt <| Ckt.incremental f_f).getD (Ckt.incremental f_ih)
--   · skip; apply (opt <| Ckt.lifting f_f).getD (Ckt.lifting f_f)
--   · skip; apply (opt <| Ckt.seq f_f1 f_f2).getD (Ckt.seq f_ih_f1 f_ih_f2)
--   · skip; apply (opt <| Ckt.par f_f1 f_f2).getD (Ckt.par f_ih_f1 f_ih_f2)
--   · skip; apply (opt <| Ckt.feedback f_F).getD (Ckt.feedback f_ih)

-- -- { apply (opt $ Ckt.intro).get_or_else Ckt.intro, },
-- -- { apply (opt $ Ckt.elim).get_or_else Ckt.elim, },
-- @[simp]
-- theorem recursiveOpt_seq (f1 : Ckt a b) (f2 : Ckt b c) :
--     recursive_opt (@opt) (Ckt.seq f1 f2) =
--       (opt <| Ckt.seq f1 f2).getD (Ckt.seq (recursive_opt (@opt) f1) (recursive_opt (@opt) f2)) :=
--   rfl

-- @[simp]
-- theorem recursiveOpt_par (f1 : Ckt a b) (f2 : Ckt c d) :
--     recursive_opt (@opt) (Ckt.par f1 f2) =
--       (opt <| Ckt.par f1 f2).getD (Ckt.par (recursive_opt (@opt) f1) (recursive_opt (@opt) f2)) :=
--   rfl

-- @[simp]
-- theorem recursiveOpt_feedback (f : Ckt (a × b) b) :
--     recursive_opt (@opt) (Ckt.feedback f) =
--       (opt <| Ckt.feedback f).getD (Ckt.feedback (recursive_opt (@opt) f)) :=
--   rfl

-- @[simp]
-- theorem recursiveOpt_incremental (f : Ckt a b) :
--     recursive_opt (@opt) (Ckt.incremental f) =
--       (opt <| Ckt.incremental f).getD (Ckt.incremental (recursive_opt (@opt) f)) :=
--   rfl

-- variable
--   (h_opt :
--     ∀ {a b : Type} [inst1 : AddCommGroup a] [inst2 : AddCommGroup b]
--       (f1 f2 : @Ckt.Ckt a b inst1 inst2),
--       @opt a b inst1 inst2 f1 = some f2 → @Ckt.Equiv a b inst1 inst2 f1 f2)

-- theorem opt_or_else_ok (f1 f2 : Ckt a b) : f2 === f1 → (opt f1).getD f2 === f1 :=
--   by
--   intro heq
--   destruct opt f1 <;> introv hopt <;> rw [hopt] <;> simp
--   assumption
--   symm; apply h_opt; assumption

-- theorem recursiveOpt_ok : ∀ f : Ckt a b, recursive_opt (@opt) f === f :=
--   by
--   intro f; induction f
--   · apply opt_or_else_ok _ @Func_denote _ @h_opt; rfl
--   · apply opt_or_else_ok _ @Func_denote _ @h_opt; rfl
--   · apply opt_or_else_ok _ @Func_denote _ @h_opt; rfl
--   · simp; apply opt_or_else_ok _ @Func_denote _ @h_opt
--     unfold Equiv at f_ih ⊢
--     simp; dsimp; rw [f_ih]
--   · apply opt_or_else_ok _ @Func_denote _ @h_opt; rfl
--   · simp; apply opt_or_else_ok _ @Func_denote _ @h_opt
--     unfold Equiv at f_ih_f1 f_ih_f2 ⊢
--     simp; dsimp; rw [f_ih_f2, f_ih_f1]
--   · simp; apply opt_or_else_ok _ @Func_denote _ @h_opt
--     unfold Equiv at f_ih_f1 f_ih_f2 ⊢
--     simp; dsimp; rw [f_ih_f1, f_ih_f2]
--   · simp; apply opt_or_else_ok _ @Func_denote _ @h_opt
--     unfold Equiv at f_ih ⊢
--     simp; dsimp; rw [f_ih]

-- end RecursiveOpt

section Incrementalize

variable
  (is_linear :
    ∀ {a b : Type} [i1 : AddCommGroup a] [i2 : AddCommGroup b] (f : @Func a b i1 i2), Bool)

-- returns an optimized version of c^Δ
def incrementalize {a b: Type} [AddCommGroup a] [AddCommGroup b] (c : Ckt a b) : Ckt a b :=
  match c with
  | Ckt.delay => Ckt.delay
  | Ckt.derivative => Ckt.derivative
  | Ckt.integral => Ckt.integral
  | Ckt.incremental f => Ckt.incremental (incrementalize f)
  | Ckt.lifting f =>
      if is_linear f then Ckt.lifting f else Ckt.incremental (Ckt.lifting f)
  | Ckt.seq f1 f2 => Ckt.seq (incrementalize f1) (incrementalize f2)
  | Ckt.par f1 f2 => Ckt.par (incrementalize f1) (incrementalize f2)
  | Ckt.feedback f =>
      Ckt.feedback (incrementalize f)

local notation "incrementalize" => incrementalize Func is_linear

@[simp]
theorem incrementalize_incremental (c : Ckt a b) :
    incrementalize (Ckt.incremental c) = Ckt.incremental (incrementalize c) :=
  rfl

@[simp]
theorem incrementalize_lifting (f : Func a b) :
    incrementalize (Ckt.lifting f) =
      if is_linear f then Ckt.lifting f else Ckt.incremental (Ckt.lifting f) :=
  rfl

@[simp]
theorem incrementalize_seq (f1 : Ckt a b) (f2 : Ckt b c) :
    incrementalize (f1 >>> f2) = incrementalize f1 >>> incrementalize f2 :=
  rfl

@[simp]
theorem incrementalize_par (f1 : Ckt a b) (f2 : Ckt c d) :
    incrementalize (Ckt.par f1 f2) = Ckt.par (incrementalize f1) (incrementalize f2) :=
  rfl

@[simp]
theorem incrementalize_feedback (f : Ckt (a × b) b) :
    incrementalize (Ckt.feedback f) = Ckt.feedback (incrementalize f) :=
  rfl

theorem incrementalize_ok
  (is_linear_ok :
    ∀ {a b : Type} [i1 : AddCommGroup a] [i2 : AddCommGroup b] (f : @Func a b i1 i2),
      @is_linear _ _ i1 i2 f →
        ∀ x y : a, Func_denote f (x + y) = Func_denote f x + Func_denote f y)
  (f : Ckt a b) : denote (incrementalize f) = denote f^Δ := by
  induction f <;> try simp; try tauto
  · split_ifs
    · simp; rw [lti_incremental]
      apply lifting_lti
      intros; apply is_linear_ok; assumption
    · simp
  · rename_i f1 f2 f_ih1 f_ih2
    rw [f_ih1, f_ih2]
    funext s
    rw [incremental_comp (denote f2) (denote f1)]
  · funext s
    rename_i f1_ih f2_ih
    rw [f1_ih, f2_ih]
    unfold uncurryOp
    unfold incremental
    rw [derivative_sprod]
    simp
    rw [integral_fst_comm, integral_snd_comm]
  · rename_i f f_ih
    rw [cycle_incremental fun s α => denote f (sprod (s, α))]
    · rw [f_ih]
      funext s
      apply congr; simp
      funext α
      rw [incremental_sprod]
    · rw [causal2]; introv heq1 heq2
      apply Ckt_causal
      intro t hle; simp
      rw [heq1, heq2] <;> tauto

end Incrementalize

end Ckts

end ckt

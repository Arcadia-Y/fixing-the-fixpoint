-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import Mathlib

/-!
# Streams

Definition of streams and some basic properties. We don't use mathlib streams
because we hardly need any definitions from it.

A stream over a type `a` is a `ℕ → a`.

Defines `agreeUpto n s s'`, usually written with the notation `s =[n]= s'`, which
says that `s` and `s'` agree on all indices in `0..n` (inclusive).
-/

universe u

/-- A stream is an infinite sequence of elements from `a`.

The indices usually use the metavariable `t`, meant to represent (a discrete
notion of) time.
-/
def stream (a: Type u) : Type u := ℕ → a

variable {a : Type u}

/-- `s₁ =[n]= s₂` says that streams `s₁` and `s₂` are equal up to (and including) time `n`. -/
def agreeUpto (n: ℕ) (s₁ s₂: stream a) := ∀ t ≤ n, s₁ t = s₂ t

notation:35 s " =[" n "]= " s' => agreeUpto n s s'

instance stream_po [PartialOrder a] : PartialOrder (stream a) :=
  Pi.partialOrder

lemma stream_le_ext [PartialOrder a] (s1 s2: stream a) :
  s1 ≤ s2 ↔ (∀ t, s1 t ≤ s2 t) := Iff.rfl

instance stream_zero [Zero a] : Zero (stream a) := ⟨fun _ => 0⟩

@[simp]
lemma stream_zero_apply [Zero a] (n: ℕ) : (0 : stream a) n = 0 := rfl

@[refl]
lemma agree_refl (n: ℕ) (s: stream a) : s =[ n ]= s :=
  fun _ _ => rfl

@[symm]
lemma agree_symm {n: ℕ} {s1 s2: stream a} : (s1 =[n]= s2) → s2 =[n]= s1 := by
  unfold agreeUpto
  intro h t h_le
  exact (h t h_le).symm

@[trans]
lemma agree_trans {n: ℕ} {s1 s2 s3: stream a} : (s1 =[n]= s2) → (s2 =[n]= s3) → s1 =[n]= s3 := by
  unfold agreeUpto
  intro h12 h23 t h_le
  rw [h12 t h_le, h23 t h_le]

instance {n : ℕ} : Trans (@agreeUpto a n) (@agreeUpto a n) (@agreeUpto a n) where
  trans := agree_trans

theorem agree_everywhere_eq (s s': stream a) :
  s = s' ↔ (∀ n, s =[n]= s') := by
  constructor
  · intro h; subst h; intro n; exact agree_refl n s
  · intro h
    funext n
    exact h n n (by omega)

lemma agreeUpto_weaken {s s': stream a} {n n': ℕ} :
  (s =[n]= s') → n' ≤ n → s =[n']= s' := by
  intro h_agree h_le t h_t_le
  exact h_agree t (by linarith)

lemma agreeUpto_weaken1 {s s': stream a} {n: ℕ} :
  (s =[n + 1]= s') → s =[n]= s' := by
  intro h
  apply agreeUpto_weaken h (by omega)

lemma agreeUpto_0 (s s': stream a) :
  (s =[0]= s') ↔ s 0 = s' 0 := by
  unfold agreeUpto
  constructor
  · intro h
    exact h 0 (by omega)
  · intro h t h_le
    rw [Nat.le_zero.mp h_le]
    exact h

lemma agreeUpto_extend (n: Nat) (s s': stream a) :
  (s =[n]= s') → s (n + 1) = s' (n + 1) → (s =[n+1]= s') := by
  intro h_agree h_eq i h_le
  rcases Nat.le_or_eq_of_le_succ h_le with h_lt_or_eq
  cases h_lt_or_eq
  · apply h_agree; assumption
  · subst i; assumption

-- We don't use this theory because everything is based on [agreeUpto], but
-- formalize a little bit from the paper.
namespace cutting

variable [Zero a]

/-- Construct a stream that matches `s` up to time `t` and is 0 afterward. -/
def cut (s: stream a) (t: ℕ) : stream a :=
  fun i => if i < t then s i else 0

lemma cut_at_0 (s: stream a) : cut s 0 = 0 := by
  funext n
  unfold stream at *
  simp [cut]

lemma cut_0 : cut (0 : stream a) = 0 := by
  ext n; funext m
  unfold cut; split_ifs <;> rfl

theorem cut_cut (s: stream a) (t1 t2: ℕ) :
  cut (cut s t1) t2 = cut s (min t1 t2) := by
  funext i; simp [cut]
  split_ifs <;> try { simp }
  tauto
  { exfalso; linarith }
  { exfalso; linarith }

theorem cut_comm (s: stream a) (t1 t2: ℕ) :
  cut (cut s t1) t2 = cut (cut s t2) t1 := by
  rw [cut_cut, cut_cut, min_comm]

theorem cut_idem (s: stream a) (t: ℕ) :
  cut (cut s t) t = cut s t := by
  rw [cut_cut, min_self]

/-- Relate `agreeUpto` to equality on `cut`. -/
theorem agreeUpto_cut (s1 s2: stream a) (n: ℕ) :
  (s1 =[n]= s2) ↔ cut s1 (n + 1) = cut s2 (n + 1) := by
  constructor
  · intro heq
    funext t; simp [cut]
    split_ifs <;> try rfl
    apply heq; omega
  · intro heq
    intro t hle; simp [cut] at heq
    have h := congr_fun heq t; simp at h
    unfold cut at *
    split_ifs at *
    · assumption
    · exfalso; omega

lemma cut_agree_succ (s1 s2: stream a) (t: ℕ) :
  cut s1 t = cut s2 t → s1 t = s2 t → cut s1 (t + 1) = cut s2 (t + 1) := by
  cases t
  · intro _hcut heq
    funext n
    unfold cut; split_ifs; swap; rfl
    have heq : n = 0 := by omega
    subst n; assumption
  repeat' rw [← agreeUpto_cut]
  apply agreeUpto_extend

theorem agree_with_cut (s: stream a) (n: ℕ) :
  s =[n]= cut s (n + 1) := by
  rw [agreeUpto_cut, cut_idem]

end cutting

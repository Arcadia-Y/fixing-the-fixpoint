-- Counterexample: FirstZero is NOT a sound fixpoint detector for the
-- delta-of-deltas approach.
import DBSP.ZsetCkt.GraphExample

namespace FirstZeroCounterexample
open CktBasic Datalog GraphExample

-- We reuse the relation `R` and circuit `c0` from GraphExample.
-- The counterexample uses two specific graphs G0 and G1.

-- G0: 1 → 2 → 3 → 4  (a 3-edge path)
def G0 : Finset (ℕ × ℕ) := {(1,2), (2,3), (3,4)}

-- G1: 1 → 5 → 3, 2 → 6 → 4  (two parallel 2-hop paths)
def G1 : Finset (ℕ × ℕ) := {(1,5), (5,3), (2,6), (6,4)}

-- Transitive closure iterates for G0 and G1
def S0 : ℕ → Finset (ℕ × ℕ)
  | 0 => {(1,2), (2,3), (3,4)}
  | 1 => {(1,2), (2,3), (3,4), (1,3), (2,4)}
  | _ => {(1,2), (2,3), (3,4), (1,3), (2,4), (1,4)}

def S1 : ℕ → Finset (ℕ × ℕ)
  | 0 => {(1,5), (5,3), (2,6), (6,4)}
  | _ => {(1,5), (5,3), (2,6), (6,4), (1,3), (2,4)}

-- Helper: D at successor index
private lemma D_succ {A: Type} [AddCommGroup A] (s: stream A) (n: ℕ) :
    D s (n + 1) = s (n + 1) - s n := by
  simp [D, delay]

-- Helper: R applied to fromSet inputs produces a fromSet output.
-- Reduces R(fromSet E, fromSet S) to fromSet of a computed Finset.
open Zset in
private lemma R_fromSet_eq (E S S' : Finset (ℕ × ℕ))
    (h : E ∪ Finset.image (fun (x : (ℕ × ℕ) × (ℕ × ℕ)) => (x.1.1, x.2.2))
           ((E ×ˢ S).filter (fun t => t.1.2 = t.2.1)) = S') :
    R (Zset.fromSet E, Zset.fromSet S) = Zset.fromSet S' := by
  subst h
  rw [← isSet_support_fromSet]
  have hbE := fromSet_isBag E
  have hbS := fromSet_isBag S
  have hbJ : IsBag (equiJoin Prod.snd Prod.fst (Zset.fromSet E) (Zset.fromSet S)) :=
    equiJoin_pos Prod.snd Prod.fst _ _ hbE hbS
  have hbM : IsBag (Zset.map (fun (x : (ℕ × ℕ) × (ℕ × ℕ)) => (x.1.1, x.2.2))
      (equiJoin Prod.snd Prod.fst (Zset.fromSet E) (Zset.fromSet S))) :=
    map_pos _ _ hbJ
  refine ⟨by simp only [R]; exact distinct_isSet _, ?_⟩
  simp only [R]
  rw [isBag_distinct_support _ (add_pos _ _ hbE hbM)]
  rw [isBag_add_support _ _ hbE hbM]
  rw [isBag_map_support _ _ hbJ]
  rw [equiJoin_support]
  simp

-- R step lemmas
open Zset in
private lemma R_G0_S0_0 :
    R (Zset.fromSet G0, Zset.fromSet (S0 0)) = Zset.fromSet (S0 1) := by
  simp only [S0, G0]; exact R_fromSet_eq _ _ _ (by decide)

open Zset in
private lemma R_G0_S0_1 :
    R (Zset.fromSet G0, Zset.fromSet (S0 1)) = Zset.fromSet (S0 2) := by
  simp only [S0, G0]; exact R_fromSet_eq _ _ _ (by decide)

open Zset in
private lemma R_G0_S0_ge2 (j : ℕ) :
    R (Zset.fromSet G0, Zset.fromSet (S0 (j + 2))) = Zset.fromSet (S0 (j + 3)) := by
  simp only [S0, G0]; exact R_fromSet_eq _ _ _ (by decide)

open Zset in
private lemma R_G1_S1_0 :
    R (Zset.fromSet G1, Zset.fromSet (S1 0)) = Zset.fromSet (S1 1) := by
  simp only [S1, G1]; exact R_fromSet_eq _ _ _ (by decide)

open Zset in
private lemma R_G1_S1_ge1 (j : ℕ) :
    R (Zset.fromSet G1, Zset.fromSet (S1 (j + 1))) = Zset.fromSet (S1 (j + 2)) := by
  simp only [S1, G1]; exact R_fromSet_eq _ _ _ (by decide)

-- The function iterates match our concrete definitions
private lemma fs_G0 (j : ℕ) :
    funcIterStream (fun r => R (Zset.fromSet G0, r)) (Zset.fromSet G0) j =
    Zset.fromSet (S0 j) := by
  induction j with
  | zero => simp [S0, G0]
  | succ j ih =>
    simp only [funcIterStream_apply, Function.iterate_succ_apply']
    rw [show (fun r => R (Zset.fromSet G0, r))^[j] (Zset.fromSet G0) =
        funcIterStream (fun r => R (Zset.fromSet G0, r)) (Zset.fromSet G0) j from rfl, ih]
    rcases j with _ | j
    · exact R_G0_S0_0
    rcases j with _ | j
    · exact R_G0_S0_1
    · exact R_G0_S0_ge2 j

private lemma fs_G1 (j : ℕ) :
    funcIterStream (fun r => R (Zset.fromSet G1, r)) (Zset.fromSet G1) j =
    Zset.fromSet (S1 j) := by
  induction j with
  | zero => simp [S1, G1]
  | succ j ih =>
    simp only [funcIterStream_apply, Function.iterate_succ_apply']
    rw [show (fun r => R (Zset.fromSet G1, r))^[j] (Zset.fromSet G1) =
        funcIterStream (fun r => R (Zset.fromSet G1, r)) (Zset.fromSet G1) j from rfl, ih]
    rcases j with _ | j
    · exact R_G1_S1_0
    · exact R_G1_S1_ge1 j

-- The input stream for the counterexample
def is_ce : stream (Z[ℕ × ℕ]) :=
  fun n => if n = 0 then Zset.fromSet G0 else Zset.fromSet G1

-- The double-differentiated stream
noncomputable def dd : stream (stream (Z[ℕ × ℕ])) :=
  D (fun i => D (fun j => funcIterStream (fun r => R (is_ce i, r)) (is_ce i) j))

-- Compute inner D for G0
private lemma innerD_G0 (n : ℕ) :
    D (funcIterStream (fun r => R (Zset.fromSet G0, r)) (Zset.fromSet G0)) (n + 1) =
    Zset.fromSet (S0 (n + 1)) - Zset.fromSet (S0 n) := by
  rw [D_succ, fs_G0, fs_G0]

-- Compute inner D for G1
private lemma innerD_G1 (n : ℕ) :
    D (funcIterStream (fun r => R (Zset.fromSet G1, r)) (Zset.fromSet G1)) (n + 1) =
    Zset.fromSet (S1 (n + 1)) - Zset.fromSet (S1 n) := by
  rw [D_succ, fs_G1, fs_G1]

-- Helper: fromSet subtraction for subsets
private lemma fromSet_sub_subset (A B : Finset (ℕ × ℕ)) (h : B ⊆ A) :
    Zset.fromSet A - Zset.fromSet B = Zset.fromSet (A \ B) := by
  ext x
  simp only [Zset.sub_apply, Zset.fromSet_apply, Finset.mem_sdiff]
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> simp [hA, hB]
  exact absurd (h hB) hA

-- dd at (1, 1) involves inner D at index 1 for both G0 and G1
-- DS0 1 = S0(1) - S0(0) = {(1,3),(2,4)} as Zset
-- DS1 1 = S1(1) - S1(0) = {(1,3),(2,4)} as Zset
-- Outer D: DS1 1 - DS0 1 = 0

theorem dd_1_1_eq_zero : dd 1 1 = 0 := by
  show D (fun i => D (fun j => funcIterStream (fun r => R (is_ce i, r)) (is_ce i) j)) 1 1 = 0
  rw [D_succ]
  show D (fun j => funcIterStream (fun r => R (is_ce 1, r)) (is_ce 1) j) 1 -
       D (fun j => funcIterStream (fun r => R (is_ce 0, r)) (is_ce 0) j) 1 = 0
  have h0 : is_ce 0 = Zset.fromSet G0 := by simp [is_ce]
  have h1 : is_ce 1 = Zset.fromSet G1 := by simp [is_ce]
  rw [h1, h0]
  rw [innerD_G1, innerD_G0]
  simp only [S0, S1]
  -- Both inner D's evaluate to fromSet{(1,3),(2,4)}, so outer D is 0
  rw [fromSet_sub_subset _ _ (by decide), fromSet_sub_subset _ _ (by decide),
      show ({(1,5),(5,3),(2,6),(6,4),(1,3),(2,4)} : Finset _) \
           {(1,5),(5,3),(2,6),(6,4)} =
           ({(1,2),(2,3),(3,4),(1,3),(2,4)} : Finset _) \
           {(1,2),(2,3),(3,4)} from by decide]
  exact sub_self _

-- dd at (1, 2) involves inner D at index 2 for both G0 and G1
-- DS0 2 = S0(2) - S0(1) contains {(1,4)}
-- DS1 2 = S1(2) - S1(1) = S1(1) - S1(1) = 0
-- Outer D: 0 - {(1,4)} = -{(1,4)} ≠ 0

theorem dd_1_2_ne_zero : dd 1 2 ≠ 0 := by
  show D (fun i => D (fun j => funcIterStream (fun r => R (is_ce i, r)) (is_ce i) j)) 1 2 ≠ 0
  rw [D_succ]
  show D (fun j => funcIterStream (fun r => R (is_ce 1, r)) (is_ce 1) j) 2 -
       D (fun j => funcIterStream (fun r => R (is_ce 0, r)) (is_ce 0) j) 2 ≠ 0
  have h0 : is_ce 0 = Zset.fromSet G0 := by simp [is_ce]
  have h1 : is_ce 1 = Zset.fromSet G1 := by simp [is_ce]
  rw [h1, h0]
  rw [innerD_G1, innerD_G0]
  simp only [S0, S1]
  -- S1(2) = S1(1), so first difference is 0. S0(1) ⊂ S0(2), difference is {(1,4)}.
  rw [sub_self, zero_sub]
  rw [fromSet_sub_subset _ _ (by decide)]
  -- Goal: -Zset.fromSet ({...} \ {...}) ≠ 0, i.e. -Zset.fromSet {(1,4)} ≠ 0
  intro h
  have h14 := DFunLike.congr_fun (neg_eq_zero.mp h) (1, 4)
  simp [Zset.fromSet_apply] at h14

end FirstZeroCounterexample

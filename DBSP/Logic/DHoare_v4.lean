import DBSP.Circuits.Circuits_v2
import DBSP.StreamTheory.Linear
import Mathlib.Algebra.Group.Defs
import DBSP.ResourceAnalysis.Dominate_v3
open CktBasic

-- Lemmas about `stream Prop` and `Operator A Prop`
section SProp

def true_until (n: ℕ) (P: stream Prop) :=
  ∀ m ≤ n, P m

lemma true_until_mono {P: stream Prop} {n m: ℕ}
  (ht: true_until m P) (h: n ≤ m):
    true_until n P := by
  intro k hk; apply ht; omega

lemma true_until_forall {P: stream Prop}:
  (∀ n, P n) <-> (∀ n, true_until n P) := by
  constructor <;> simp [true_until] <;>
  intros <;> tauto

variable {A: Type} [Zero A] {I: Operator A Prop} {n: ℕ}

lemma zero_0_to_delay_0
  (h0: I 0 0) (hc: Causal I) (s: stream A):
    I (z⁻¹ s) 0 := by
  suffices I 0 0 = I (z⁻¹ s) 0 by
    rw [<- this]; tauto
  apply hc
  intro t ht; have: t = 0 := by omega
  rw [this]; simp

@[simp]
def omit0 (I: Operator A Prop) :=
  fun s i => I (z⁻¹ s) (i+1)

lemma causal_omit0 (hc: Causal I):
    Causal (omit0 I) := by
  intro s1 s2 t h; simp only [omit0]
  apply hc; intro i hi
  rcases i; simp
  simp; apply h; omega

lemma true_until_omit0_delay
  (h0: I 0 0) (hc: Causal I) x:
    true_until n (omit0 I x) <-> true_until (n+1) (I (z⁻¹ x)) := by
  constructor
  · intro h m hm
    rcases m
    · apply zero_0_to_delay_0 <;> tauto
    · apply h; omega
  · intro h m hm; simp
    apply h; omega

@[simp]
def later (P: Operator A Prop) :=
  fun s n =>
    if n = 0 then s 0 = 0
     else P (drop 1 s) (n-1)

lemma later_delay (P: Operator A Prop) (s: stream A) (n: ℕ):
    P s n <-> later P (z⁻¹ s) (n+1) := by simp

lemma later_delay_true_until (P: Operator A Prop) (s: stream A) (n: ℕ):
    true_until n (P s) <-> true_until (n+1) (later P (z⁻¹ s)) := by
  simp [true_until]; constructor
  · intro hp m hm hm0
    apply hp; omega
  · intro h m hm
    have : m = m + 1 - 1 := by omega
    rw [this]; apply h <;> omega

lemma later_delay_forall (P: Operator A Prop) (s: stream A):
    (∀ n, P s n) <-> (∀ n, later P (z⁻¹ s) (n+1)) := by simp

lemma later_delay_true_until_forall (P: Operator A Prop) (s: stream A):
    (∀ n, true_until n (P s)) <-> (∀ n, true_until n (later P (z⁻¹ s))) := by
  constructor
  · intro h n; cases n; simp [true_until]
    rw [<- later_delay_true_until]; tauto
  · intro h n
    rw [later_delay_true_until]; tauto

end SProp

-- Lemmas about transpose
section Transpose
variable {A: Type}

@[simp]
def transpose (s: stream (stream A)): stream (stream A) :=
  fun n m => s m n
notation "TP" => transpose

@[simp]
lemma transpose_apply (s: stream (stream A)) (n m: ℕ):
  TP s n m = s m n := by rfl

variable [Zero A]

theorem TP_delay (s: stream (stream A)):
    TP (↑↑z⁻¹ s) = z⁻¹ (TP s) := by
  funext n m; simp [transpose, delay]
  split_ifs <;> simp

@[simp]
def omit0TP (I: Operator (stream A) Prop) (s: stream (stream A)) :=
  omit0 I (TP s)

end Transpose

section DHoare
-- definition of DHoare
variable {n: ℕ} {A B C: VType} {ns: Bool} {c: Ckt ns A B} {x: SOVType ns A}
  {r r1 r2: SONat ns} {Q: Operator (OVType ns B) Prop}

structure DHoare (n: ℕ) (c: Ckt ns A B) (x: SOVType ns A)
    (Q: Operator (OVType ns B) Prop) (k: ℕ) (r: SONat ns) where
  post: true_until n (Q (denote c x))
  bound: (cost_f c x) <[k, n] r

variable {k k1 k2: ℕ}

theorem DHoare_conseq
  (Q': Operator (OVType ns B) Prop)
  (h: DHoare n c x Q' k r)
  (hy: ∀ y i, Q' y i -> Q y i):
    DHoare n c x Q k r := by
  constructor
  case bound => exact h.bound
  case post =>
    intro m hm
    apply hy; apply h.post; tauto

theorem DHoare_scale_k (k': ℕ)
  (h: DHoare n c x Q k r) (hk: k ≤ k'):
    DHoare n c x Q k' r := by
  constructor
  case post => exact h.post
  case bound =>
    apply Dom_scale_k
    apply h.bound
    tauto

theorem DHoare_weaken (r': SONat ns)
  (h: DHoare n c x Q k1 r) (hr: r <[k2, n] r') :
    DHoare n c x Q (k2 * k1) r' := by
  constructor
  case post => exact h.post
  case bound => apply Dom_trans h.bound hr

theorem DHoare_seq {c1: Ckt ns A B} {c2: Ckt ns B C}
  {Q1: Operator (OVType ns B) Prop} {Q2: Operator (OVType ns C) Prop}
  (h1: DHoare n c1 x Q1 k1 r1) (h2: ∀ y, true_until n (Q1 y) -> DHoare n c2 y Q2 k2 r2):
    DHoare n (c1 >>c c2) x Q2 (max k1 k2) (r1 + r2) := by
  specialize h2 (denote c1 x) (h1.post)
  constructor
  case post => exact h2.post
  case bound =>
    simp [cost_f]
    apply Dom_add_Dom
    exact h1.bound; exact h2.bound

theorem DHoare_seq_ncausal {c1: Ckt ns A B} {c2: Ckt ns B C}
  {Q1: (SOVType ns B) -> Prop} {Q2: Operator (OVType ns C) Prop}
  (h1: DHoare n c1 x (fun y _ => Q1 y) k1 r1) (h2: ∀ y, Q1 y -> DHoare n c2 y Q2 k2 r2):
    DHoare n (c1 >>c c2) x Q2 (max k1 k2) (r1 + r2) := by
  apply DHoare_seq h1
  intro y hy
  apply h2; apply (hy 0); simp

theorem DHoare_seq_ncausal_tight {c1: Ckt ns A B} {c2: Ckt ns B C}
  {Q1: (SOVType ns B) -> Prop} {Q2: Operator (OVType ns C) Prop} (k3: ℕ) (r3: SONat ns)
  {h1: DHoare n c1 x (fun y _ => Q1 y) k1 r1} {h2: ∀ y, Q1 y -> DHoare n c2 y Q2 k2 r2}
  (hdom: ∀ x1 x2, (x1 <[k1, n] r1) -> (x2 <[k2, n] r2) -> x1 + x2 <[k3, n] r3):
    DHoare n (c1 >>c c2) x Q2 k3 r3 := by
  specialize h2 (denote c1 x) (h1.post 0 (by simp))
  constructor
  case post => exact h2.post
  case bound =>
    simp [cost_f]
    apply hdom
    apply h1.bound; apply h2.bound

theorem DHoare_par {c1: Ckt ns A B} {c2: Ckt ns A C}
  {Q1: Operator (OVType ns B) Prop} {Q2: Operator (OVType ns C) Prop}
  (h1: DHoare n c1 x Q1 k1 r1) (h2: DHoare n c2 x Q2 k2 r2):
    DHoare n (c1 &&c c2) x
      (fun y n => ∃ y1 y2, y = sprodO ns (y1, y2) ∧ Q1 y1 n ∧ Q2 y2 n)
      (max k1 k2) (r1 + r2) := by
  constructor
  case post =>
    simp [denote]; intro t ht
    use (denote c1 x), (denote c2 x)
    constructor; simp
    constructor
    apply h1.post; tauto
    apply h2.post; tauto
  case bound =>
    simp [cost_f]
    apply Dom_add_Dom
    exact h1.bound; exact h2.bound

theorem DHoare_par_ncausal {c1: Ckt ns A B} {c2: Ckt ns A C}
  {Q1: (SOVType ns B) -> Prop} {Q2: (SOVType ns C) -> Prop}
  (h1: DHoare n c1 x (fun y _ => Q1 y) k1 r1) (h2: DHoare n c2 x (fun y _ => Q2 y) k2 r2):
    DHoare n (c1 &&c c2) x
      (fun y _ => ∃ y1 y2, y = sprodO ns (y1, y2) ∧ Q1 y1 ∧ Q2 y2)
      (max k1 k2) (r1 + r2) := by
  apply DHoare_par h1 h2

theorem DHoare_par_ncausal_tight {c1: Ckt ns A B} {c2: Ckt ns A C}
  {Q1: (SOVType ns B) -> Prop} {Q2: (SOVType ns C) -> Prop} (k3: ℕ) (r3: SONat ns)
  (h1: DHoare n c1 x (fun y _ => Q1 y) k1 r1) (h2: DHoare n c2 x (fun y _ => Q2 y) k2 r2)
  (hdom: ∀ x1 x2, (x1 <[k1, n] r1) -> (x2 <[k2, n] r2) -> x1 + x2 <[k3, n] r3):
    DHoare n (c1 &&c c2) x
      (fun y _ => ∃ y1 y2, y = sprodO ns (y1, y2) ∧ Q1 y1 ∧ Q2 y2)
      k3 r3 := by
  constructor
  case post =>
    simp [denote]; intro t ht
    use (denote c1 x), (denote c2 x)
    constructor; simp
    constructor
    apply h1.post; tauto
    apply h2.post; tauto
  case bound =>
    simp [cost_f]
    apply hdom
    exact h1.bound; exact h2.bound

theorem DHoare_loop_later {c: Ckt ns (A ×ᵥ B) B}
  {x: SOVType ns A} {r: SONat ns}
  (I: Operator (OVType ns B) Prop) (s: SONat ns)
  (ih: ∀ y n, true_until n (later I y) -> DHoare n c (sprodO ns (x, y)) I k1 r)
  (hs: ∀ y, true_until n (I y) -> liftO ns VType_space y <[k2, n] s) :
    DHoare n (cloop c) x I (max k1 k2) (r + s) := by
  have h_tuI : ∀ n, true_until n (I (denote (cloop c) x)) := by
    clear hs; intro n; induction n
    · specialize ih (z⁻¹ (denote (cloop c) x)) 0 (by simp [true_until])
      rw [loop_unfold]
      apply ih.post
    · rename_i n hn
      rw [later_delay_true_until] at hn
      apply ih at hn
      rw [loop_unfold]
      apply hn.post
  constructor
  case post =>
    tauto
  case bound =>
    simp [cost_f]; apply Dom_add_Dom
    · rw [later_delay_true_until_forall] at h_tuI
      specialize ih _ n (by apply h_tuI)
      apply ih.bound
    · apply hs
      tauto

theorem DHoare_loop {c: Ckt ns (A ×ᵥ B) B}
  {x: SOVType ns A} {r: SONat ns}
  (I: Operator (OVType ns B) Prop)
  (hIc: Causal I)
  (s: SONat ns) (h0: I 0 0)
  (ih: ∀ y n, true_until n (I (z⁻¹ y)) -> DHoare n c (sprodO ns (x, z⁻¹ y)) (omit0 I) k1 r)
  (hs: ∀ y, true_until n (omit0 I y) -> liftO ns VType_space y <[k2, n] s) :
    DHoare n (cloop c) x (omit0 I) (max k1 k2) (r + s) := by
  have h_tuI : ∀ n, true_until n (I (z⁻¹ (denote (cloop c) x))) := by
    clear hs; intro n; induction n
    · simp [true_until]
      apply zero_0_to_delay_0 <;> tauto
    · rename_i n hn
      apply ih at hn
      rw [loop_unfold, <- true_until_omit0_delay] <;> try tauto
      apply hn.post
  constructor
  case post =>
    rw [true_until_omit0_delay] <;> tauto
  case bound =>
    simp [cost_f]; apply Dom_add_Dom
    · specialize ih _ n (by apply h_tuI)
      apply ih.bound
    · apply hs
      rw [true_until_omit0_delay] <;> tauto

theorem DHoare_loop_lifted {c: Ckt 1 (A ×ᵥ B) B}
  {x: stream (stream (VType_interp A))} {r: stream (stream ℕ)}
  (I: Operator (stream ( VType_interp B)) Prop)
  (hIc: Causal I) (h0: I 0 0)
  (s: stream (stream ℕ))
  (ih: ∀ y n, true_until n (I (TP (↑↑z⁻¹ y))) -> DHoare n c (sprod2 (x, ↑↑z⁻¹ y)) (omit0TP I) k1 r)
  (hs: ∀ y, true_until n (omit0TP I y) -> ↑↑↑↑VType_space y <[k2, n] s) :
    DHoare n (cloop2 c) x (omit0TP I) (max k1 k2) (r + s) := by
  have h_tuI : ∀ n, true_until n (I (TP (↑↑z⁻¹ (denote (cloop2 c) x)))) := by
    clear hs; intro n; induction n
    · simp [true_until]
      rw [TP_delay]
      apply zero_0_to_delay_0 <;> tauto
    · rename_i n hn
      apply ih at hn
      rw [TP_delay]
      rw [loop_lifted_unfold, <- true_until_omit0_delay] <;> try tauto
      apply hn.post
  constructor
  case post =>
    simp; rw [true_until_omit0_delay, <- TP_delay] <;> tauto
  case bound =>
    simp [cost_f]; apply Dom_add_Dom
    · specialize ih _ n (by apply h_tuI)
      apply ih.bound
    · apply hs; simp
      rw [true_until_omit0_delay, <- TP_delay] <;> tauto

theorem DHoare_lifting {c: Ckt false A B} {x: stream (stream (VType_interp A))}
  {Q: Operator (VType_interp B) Prop} {r: stream (stream ℕ)}
  (h: ∀ i ≤ n, ∀ m, DHoare m c (x i) Q k (r i)):
    DHoare n (c↑ c) x (fun y i => ∀ t, Q (y i) t) k r := by
  constructor
  case post =>
    intro i hi t; simp [denote]
    specialize h i hi t
    apply h.post; simp
  case bound =>
    intro i hi t; simp [cost_f]
    specialize h i hi t
    apply h.bound; simp

lemma sumVals_N_weaken {s : stream ℕ}
  (n m : ℕ) (h: m ≤ n):
    sumVals s m ≤  sumVals s n := by
  have: n = m + (n-m) := by omega
  rw [this, sumVals_split]; simp

theorem DHoare_bracket {c: Ckt 1 A B}
  {x: stream (VType_interp A)} {r: stream (stream ℕ)}
  (Q: Operator (stream (VType_interp B)) Prop) (b: stream ℕ)
  (h: DHoare n c (↑↑δ0 x) Q k r)
  (hb: ∀ n y, true_until n (Q y) -> ZeroAfter (y n) (b n)) :
    ∃ m,
      DHoare n (cbracket c) x
        (fun y i => (Q m) i ∧ y i = sumVals (m i) (b i))
        k (fun i => sumVals (r i) (b i + 1)) := by
  have Qm := h.post
  set m := denote c (↑↑δ0 x); use m
  have hzm: ∀ t ≤ n, ZeroAfter (m t) (b t) := by
    intro t ht
    apply hb; apply true_until_mono <;> tauto
  constructor
  case post =>
    simp [denote]; intro t ht
    constructor; apply Qm; tauto
    rw [streamElim_zeroAfter]; apply hzm; tauto
  case bound =>
    simp [cost_f]; intro t ht; simp
    specialize hzm t ht
    cases Classical.propDecidable _ <;>
    rename_i hex <;> simp [hex]
    have hr := h.bound; clear h
    have hcm := Classical.choose_spec hex
    set cm := Classical.choose hex
    rw [add_comm, <- sumVals_succ]
    rw [add_comm (r t (b t)), <- sumVals_succ]
    apply le_trans
    · apply sumVals_N_weaken (b t + 1); simp
      apply Minimal_ZeroAfter (hn:= hzm); tauto
    specialize hr t ht
    apply MonoDom_sumVals
    swap; apply le_refl
    intro _ _; apply hr

theorem DHoare_delay:
    DHoare n (@Ckt.delay ns A) x (fun y _ => y = z⁻¹ x) 1 (liftO ns VType_space x) := by
  constructor
  case post =>
    intro _ _; simp [denote]
  case bound =>
    intro _ _; simp [cost_f]

theorem DHoare_id:
    DHoare n (@Ckt.id ns A) x (fun y _ => y = x) 0 0 := by
  constructor
  case post =>
    intro _ _; simp [denote]
  case bound =>
    intro _ _; simp [cost_f]; rcases ns <;> simp

theorem DHoare_fst {x: SOVType ns (A×ᵥB)}:
    DHoare n (@Ckt.fst ns A B) x (fun y _ => y = liftO ns Prod.fst x) 0 0 := by
  constructor
  case post =>
    intro _ _; simp [denote]
  case bound =>
    intro _ _; simp [cost_f]; rcases ns <;> simp

theorem DHoare_snd {x: SOVType ns (A×ᵥB)}:
    DHoare n (@Ckt.snd ns A B) x (fun y _ => y = liftO ns Prod.snd x) 0 0 := by
  constructor
  case post =>
    intro _ _; simp [denote]
  case bound =>
    intro _ _; simp [cost_f]; rcases ns <;> simp

-- cost bound from h1
theorem DHoare_conj {k1 k2: ℕ}
  {Q1: Operator (OVType ns B) Prop} {Q2: Operator (OVType ns B) Prop}
  (h1: DHoare n c x Q1 k1 r1) (h2: DHoare n c x Q2 k2 r2):
    DHoare n c x (fun y i => Q1 y i ∧ Q2 y i) k1 r1 := by
  constructor
  case post =>
    intro m hm
    have h1p := h1.post m hm
    have h2p := h2.post m hm
    tauto
  case bound =>
    apply h1.bound

theorem DHoare_conj_ncausal {k1 k2: ℕ}
  {Q1: (SOVType ns B) -> Prop} {Q2: (SOVType ns B) -> Prop}
  (h1: DHoare n c x (fun y _ => Q1 y) k1 r1) (h2: DHoare n c x (fun y _ => Q2 y) k2 r2):
    DHoare n c x (fun y _ => Q1 y ∧ Q2 y) k1 r1 := by
  apply DHoare_conseq
  apply DHoare_conj h1 h2
  tauto

end DHoare

syntax "Dweaken": tactic
syntax "wapply" term: tactic
syntax "le_refine" term: tactic
syntax "par_intro": tactic
syntax "seq_intro": tactic
syntax "cons_apply" term: tactic
-- apply consequence rule and use the raw value to reason
syntax "cons_value" term: tactic

macro_rules
  | `(tactic| Dweaken) => `(tactic| apply DHoare_scale_k; apply DHoare_weaken)
  | `(tactic| wapply $h: term) => `(tactic| Dweaken; apply $h)
  | `(tactic| le_refine $e: term) => `(tactic| refine le_trans ?_ (le_rfl (a := $e)); try omega)
  | `(tactic| seq_intro) => `(tactic| intro y hy; try simp at hy; try subst y)
  | `(tactic| par_intro) => `(tactic| rintro y ⟨y1, y2, eqy, hy1, hy2⟩; try simp at eqy; try subst eqy)
  | `(tactic| cons_apply $h: term) => `(tactic| apply DHoare_conseq; apply $h)
  | `(tactic| cons_value $h: term) => `(tactic| apply DHoare_conseq; apply $h; intro y i hy; (try simp at hy); try subst y)

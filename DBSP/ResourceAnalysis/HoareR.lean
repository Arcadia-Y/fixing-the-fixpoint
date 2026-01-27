import DBSP.Circuits.Circuits_v3
import DBSP.Logic.SProp
import DBSP.Logic.Sequiv
import DBSP.Logic.Hoare
import DBSP.ResourceAnalysis.Dominate_v3
open CktBasic

section HoareR
variable {A B C: VType} {ns: Bool} {c: Ckt ns A B}
  {r r1 r2: SOType ns ℕ} {x: SOVType ns A} {Q: SPred (OVType ns B)} {n: ℕ}

def some_bound {ns: Bool} (r: SOType ns ℕ) : SOType ns ℕ∞ :=
  liftO ns Nat.cast r

@[simp]
theorem some_bound_linear:
    some_bound (r1 + r2) = some_bound r1 + some_bound r2 := by
  rcases ns <;> simp [some_bound, liftO, add_smul]
  · funext n; simp
  · funext m n; simp

@[simp]
theorem some_bound_smul (k: ℕ):
    some_bound (k • r) = k • some_bound r := by
  induction k
  · rcases ns <;> simp [some_bound]
    funext n; simp
    funext m n; simp
  · simp [add_smul]
    rename_i n ih; simp [ih]

theorem some_bound_le (h: r1 ≤ r2):
    some_bound r1 ≤ some_bound r2 := by
  rcases ns <;> simp [some_bound, liftO]
  · intro n; apply Nat.cast_le.mpr; apply h
  · intro m n; apply Nat.cast_le.mpr; apply h

theorem some_bound_Dom {k} (h: r1 <[k, n] r2):
    some_bound r1 <[k, n] some_bound r2 := by
  rcases ns <;> simp [some_bound, liftO]
  · intro m hm; apply Nat.cast_le.mpr; apply h m hm
  · intro m hm n; apply Nat.cast_le.mpr; apply h m hm

-- Hoare logic with resource bound
structure HoareR (c: Ckt ns A B) (x: SOVType ns A)
    (Q: SPred (OVType ns B))
    (k: ℕ) (r: SOType ns ℕ) (n: ℕ) where
  post: Hoare c x Q n
  cost: cost_f c x <[k, n] some_bound r

variable {k k1 k2: ℕ}

theorem HoareR_conseq_strong
  (Q': SPred (OVType ns B))
  (hy: ∀ y n, true_until n (Q' y) -> true_until n (Q y))
  {n: ℕ} (h: HoareR c x Q' k r n):
    HoareR c x Q k r n := by
  constructor
  case post =>
    apply Hoare_conseq_strong
    apply h.post; apply hy
  case cost => apply h.cost

theorem HoareR_conseq
  (Q': SPred (OVType ns B))
  {n: ℕ} (h: HoareR c x Q' k r n)
  (hy: ∀ y i, Q' y i -> Q y i):
    HoareR c x Q k r n := by
  constructor
  case post =>
    apply Hoare_conseq
    apply h.post; apply hy
  case cost => apply h.cost

theorem HoareR_release_k
  (h: HoareR c x Q k r n):
    HoareR c x Q 1 (k • r) n := by
  constructor
  case post => apply h.post
  case cost =>
    simp; apply Dom_release_k; apply h.cost

theorem HoareR_absorb_k
  (h: HoareR c x Q 1 (k • r) n):
    HoareR c x Q k r n := by
  constructor
  case post => apply h.post
  case cost =>
    apply Dom_absorb_k; rw [<- some_bound_smul]; apply h.cost

theorem HoareR_scale_k (k': ℕ)
  (h: HoareR c x Q k r n) (hk: k ≤ k'):
    HoareR c x Q k' r n := by
  constructor
  case post => apply h.post
  case cost =>
    simp; apply Dom_scale_k; apply h.cost; tauto

theorem HoareR_weaken (r': SOType ns ℕ)
  (h: HoareR c x Q k1 r n) (hr: r <[k2, n] r'):
    HoareR c x Q (k2 * k1) r' n := by
  constructor
  case post => apply h.post
  case cost =>
    apply Dom_trans; apply h.cost
    apply some_bound_Dom; apply hr

theorem HoareR_weaken_tight (k2: ℕ) (r2: SOType ns ℕ)
  (h: HoareR c x Q k1 r n) (hr: k1 • r ≤ k2 • r2):
    HoareR c x Q k2 r2 n := by
  constructor
  case post => apply h.post
  case cost =>
    apply Dom_absorb_k; apply Dom_scale_k; apply Dom_trans
    have hc := h.cost
    apply Dom_release_k at hc; apply hc
    simp_rw [<- some_bound_smul]; apply some_bound_Dom
    apply le_Dom; apply hr; simp

theorem HoareR_weaken_1 (r': SOType ns ℕ)
  (h: HoareR c x Q 1 r n) (hr: r ≤ r'):
    HoareR c x Q 1 r' n := by
  apply HoareR_weaken_tight (h:=h)
  simp; apply hr

theorem HoareR_seq_tight {c1: Ckt ns A B} {c2: Ckt ns B C}
  {Q1: SPred (OVType ns B)} {Q2: SPred (OVType ns C)}
  (h1: HoareR c1 x Q1 k1 r1 n) (h2: ∀ y, true_until n (Q1 y) -> HoareR c2 y Q2 k2 r2 n):
    HoareR (c1 >>c c2) x Q2 1 (k1 • r1 + k2 • r2) n := by
  constructor
  case post =>
    apply Hoare_seq; apply h1.post
    intro y hy; apply (h2 y hy).post
  case cost =>
    simp [cost_f]; intro m hm
    have hc1 := h1.cost m hm
    have hc2 := (h2 (denote c1 x) h1.post).cost m hm
    simp at hc1 hc2; simp
    apply add_le_add <;> tauto

theorem HoareR_seq {c1: Ckt ns A B} {c2: Ckt ns B C}
  {Q1: SPred (OVType ns B)} {Q2: SPred (OVType ns C)}
  (h1: HoareR c1 x Q1 k1 r1 n) (h2: ∀ y, true_until n (Q1 y) -> HoareR c2 y Q2 k2 r2 n):
    HoareR (c1 >>c c2) x Q2 (max k1 k2) (r1 + r2) n := by
  apply HoareR_scale_k; apply HoareR_weaken_tight
  apply HoareR_seq_tight h1 h2
  swap; rfl
  simp; apply add_le_add <;> gcongr <;> simp

theorem HoareR_seq_ncausal {c1: Ckt ns A B} {c2: Ckt ns B C}
  {Q1: (SOVType ns B) -> Prop} {Q2: SPred (OVType ns C)}
  (h1: HoareR c1 x (fun y _ => Q1 y) k1 r1 n) (h2: ∀ y, Q1 y -> HoareR c2 y Q2 k2 r2 n):
    HoareR (c1 >>c c2) x Q2 (max k1 k2) (r1 + r2) n := by
  apply HoareR_seq; apply h1
  intro y hy
  apply h2; apply (hy 0); simp

theorem Hoare_par {c1: Ckt ns A B} {c2: Ckt ns A C}
  {Q1: SPred (OVType ns B)} {Q2: SPred (OVType ns C)}
  (h1: Hoare c1 x Q1 n) (h2: Hoare c2 x Q2 n):
    Hoare (c1 &&c c2) x
      (fun y i => ∃ y1 y2, y = sprodO ns (y1, y2) ∧ Q1 y1 i ∧ Q2 y2 i) n := by
  simp [Hoare, denote]; intro t ht
  use (denote c1 x), (denote c2 x)
  constructor; simp
  constructor
  apply h1; tauto
  apply h2; tauto

theorem Hoare_par_ncausal {c1: Ckt ns A B} {c2: Ckt ns A C}
  {Q1: (SOVType ns B) -> Prop} {Q2: (SOVType ns C) -> Prop}
  (h1: Hoare c1 x (fun y _ => Q1 y) n) (h2: Hoare c2 x (fun y _ => Q2 y) n):
    Hoare (c1 &&c c2) x
      (fun y _ => ∃ y1 y2, y = sprodO ns (y1, y2) ∧ Q1 y1 ∧ Q2 y2) n := by
  apply Hoare_par h1 h2

theorem Hoare_loop {c: Ckt ns (A ×ᵥ B) B}
  {x: SOVType ns A}
  (I: SPred (OVType ns B))
  (ih: ∀ y n, true_until n (later I y) -> Hoare c (sprodO ns (x, y)) I n) {n: ℕ}:
    Hoare (cloop c) x I n := by
  unfold Hoare at *; induction n
  · specialize ih (z⁻¹ (denote (cloop c) x)) 0 (by simp [true_until])
    rw [loop_unfold]
    apply ih
  · rename_i n hn
    rw [later_delay_true_until] at hn
    apply ih at hn
    rw [loop_unfold]
    apply hn

theorem Hoare_lifted_loop {c: Ckt true (A ×ᵥ B) B}
  {x: stream (stream (VType_interp A))}
  (I: SPred (stream (VType_interp B)))
  (ih: ∀ y n, true_until n (later I (TP y)) -> Hoare c (sprod2 (x, y)) (TP_SPred I) n) {n: ℕ}:
    Hoare (cloop2 c) x (TP_SPred I) n := by
  unfold Hoare at *; induction n
  · specialize ih (↑↑z⁻¹ (denote (cloop2 c) x)) 0 (by
      rw [TP_delay]; simp [true_until]
    )
    rw [lifted_loop_unfold]
    apply ih
  · rename_i n hn
    simp at hn
    rw [later_delay_true_until] at hn
    rw [<- TP_delay] at hn
    apply ih at hn
    rw [lifted_loop_unfold]
    apply hn

lemma sumVals_N_weaken {s : stream ℕ}
  (n m : ℕ) (h: m ≤ n):
    sumVals s m ≤  sumVals s n := by
  have: n = m + (n-m) := by omega
  rw [this, sumVals_split]; simp

theorem Hoare_bracket {c: Ckt 1 A B} {fc}
  {x: stream (VType_interp A)}
  (Q: SPred (stream (VType_interp B))) (b: stream ℕ) {n: ℕ}
  (h: Hoare c (↑↑δ0 x) Q n)
  (hb: ∀ n y, true_until n (Q y) -> ZeroAfter (y n) (b n)) :
    Hoare (cbracket c fc) x
      (fun y i => ∃ m, (Q m) i ∧ y i = sumVals (m i) (b i)) n := by
  set m := denote c (↑↑δ0 x)
  have hzm: ∀ t ≤ n, ZeroAfter (m t) (b t) := by
    intro t ht
    apply hb; apply true_until_mono <;> tauto
  simp [Hoare, denote]; intro t ht
  use m; constructor; apply h; tauto
  rw [streamElim_zeroAfter]; apply hzm; tauto

theorem Hoare_bracket_ncausal {c: Ckt 1 A B} {fc}
  {x: stream (VType_interp A)}
  (Q: SPred (stream (VType_interp B))) (b: stream ℕ)
  (h: ∀ n, Hoare c (↑↑δ0 x) Q n)
  (hb: ∀ n y, true_until n (Q y) -> ZeroAfter (y n) (b n)) {n: ℕ} :
    Hoare (cbracket c fc) x
      (fun y _ => ∃ m, ∀ i, (Q m) i ∧ y i = sumVals (m i) (b i)) n := by
  set m := denote c (↑↑δ0 x)
  have hzm: ∀ t, ZeroAfter (m t) (b t) := by
    intro t; apply hb; apply true_until_mono <;> tauto
  simp [Hoare, denote]; intro t ht
  use m; intro i; constructor; apply h; tauto
  rw [streamElim_zeroAfter]; apply hzm

theorem Hoare_delay:
    Hoare (@Ckt.delay ns A) x (fun y _ => y = z⁻¹ x) n:= by
  intro _ _; simp [Hoare, denote]

theorem Hoare_id:
    Hoare (@Ckt.id ns A) x (fun y _ => y = x) n := by
  intro _ _; simp [Hoare, denote]

theorem Hoare_fst {x: SOVType ns (A×ᵥB)}:
    Hoare (@Ckt.fst ns A B) x (fun y _ => y = liftO ns Prod.fst x) n := by
  intro _ _; simp [Hoare, denote]

theorem Hoare_snd {x: SOVType ns (A×ᵥB)}:
    Hoare (@Ckt.snd ns A B) x (fun y _ => y = liftO ns Prod.snd x) n := by
  intro _ _; simp [Hoare, denote]

theorem Hoare_conj
  {Q1: SPred (OVType ns B)} {Q2: SPred (OVType ns B)}
  (h1: Hoare c x Q1 n) (h2: Hoare c x Q2 n):
    Hoare c x (fun y i => Q1 y i ∧ Q2 y i) n := by tauto

theorem Hoare_conj_ncausal
  {Q1: (SOVType ns B) -> Prop} {Q2: (SOVType ns B) -> Prop}
  (h1: Hoare c x (fun y _ => Q1 y) n) (h2: Hoare c x (fun y _ => Q2 y) n):
    Hoare c x (fun y _ => Q1 y ∧ Q2 y) n := by
  apply Hoare_conseq
  apply Hoare_conj; apply h1; apply h2
  simp

end HoareR

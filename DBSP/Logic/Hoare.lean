import DBSP.Circuits.Circuits_v3
import DBSP.StreamTheory.Linear
import DBSP.Logic.SProp
import DBSP.Logic.Sequiv
open CktBasic

section Transpose
variable {A: Type}

@[simp]
def transpose (s: stream (stream A)): stream (stream A) :=
  fun n m => s m n
notation "TP" => transpose

@[simp]
lemma TP_apply (s: stream (stream A)) (n m: ℕ):
  TP s n m = s m n := by rfl

variable [Zero A]

theorem TP_delay (s: stream (stream A)):
    TP (↑↑z⁻¹ s) = z⁻¹ (TP s) := by
  funext n m; simp [transpose, delay]
  split_ifs <;> simp

@[simp]
def TP_SPred (P: SPred (stream A)) :=
  fun s => P (TP s)

end Transpose

section Hoare
variable {A B C: VType} {ns: Bool} {c: Ckt ns A B}
  {x: SOVType ns A} {P: SPred (OVType ns A)} {Q: SPred (OVType ns B)}

-- Shallow-embedded Hoare triple for Ckts
def Hoare (P: SPred (OVType ns A))
    (c: Ckt ns A B) (Q: SPred (OVType ns B)):=
  ∀ x n, TrueUntil n (P x) -> TrueUntil n (Q (denote c x))

theorem Hoare_conseq_strong
  (Q': SPred (OVType ns B))
  {n: ℕ} (h: Hoare c x Q' n)
  (hy: ∀ y n, TrueUntil n (Q' y) -> TrueUntil n (Q y)):
    Hoare c x Q n := by
  tauto

theorem Hoare_conseq
  (Q': SPred (OVType ns B))
  {n: ℕ} (h: Hoare c x Q' n)
  (hy: ∀ y i, Q' y i -> Q y i):
    Hoare c x Q n := by
  tauto

theorem Hoare_Sequiv_cong {c1 c2: Ckt ns A B}
  (h: c1 ≃ c2) {n: ℕ}:
    Hoare c1 x Q n <-> Hoare c2 x Q n := by
  simp [Hoare]; rw [h]

theorem Hoare_SequivOn_cong {c1 c2: Ckt ns A B}
  (P: SPred (OVType ns A)) (he: c1 ≃[P] c2)
  (hp: ∀ n, (P x) n) {n: ℕ}:
    Hoare c1 x Q n <-> Hoare c2 x Q n := by
  simp [Hoare]; specialize he x
  have : denote c1 x = denote c2 x := by
    rw [agree_everywhere_eq]
    intro n; apply he
    rw [TrueUntil_forall] at hp; tauto
  rw [this]

theorem Hoare_SequivOn_cong_causal {c1 c2: Ckt ns A B}
  (P: SPred (OVType ns A)) (he: c1 ≃[P] c2)
  (hc: Causal Q)
  {n: ℕ} (hp: TrueUntil n (P x)):
    Hoare c1 x Q n <-> Hoare c2 x Q n := by
  simp [Hoare]; specialize he x
  constructor <;> intro h m hm <;>
  specialize he m (by apply TrueUntil_mono <;> tauto)
  · apply hc at he; rw [<- he]; tauto
  · apply hc at he; rw [he]; tauto

theorem Hoare_seq {c1: Ckt ns A B} {c2: Ckt ns B C}
  {Q1: SPred (OVType ns B)} {Q2: SPred (OVType ns C)}
  (h1: Hoare c1 x Q1 n) (h2: ∀ y, TrueUntil n (Q1 y) -> Hoare c2 y Q2 n):
    Hoare (c1 >>c c2) x Q2 n := by
  tauto

theorem Hoare_seq_ncausal {c1: Ckt ns A B} {c2: Ckt ns B C}
  {Q1: (SOVType ns B) -> Prop} {Q2: SPred (OVType ns C)}
  (h1: Hoare c1 x (fun y _ => Q1 y) n) (h2: ∀ y, Q1 y -> Hoare c2 y Q2 n):
    Hoare (c1 >>c c2) x Q2 n := by
  apply Hoare_seq; apply h1
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
  (ih: ∀ y n, TrueUntil n (later I y) -> Hoare c (sprodO ns (x, y)) I n) {n: ℕ}:
    Hoare (cloop c) x I n := by
  unfold Hoare at *; induction n
  · specialize ih (z⁻¹ (denote (cloop c) x)) 0 (by simp [TrueUntil])
    rw [loop_unfold]
    apply ih
  · rename_i n hn
    rw [later_delay_TrueUntil] at hn
    apply ih at hn
    rw [loop_unfold]
    apply hn

theorem Hoare_lifted_loop {c: Ckt true (A ×ᵥ B) B}
  {x: stream (stream (VType_interp A))}
  (I: SPred (stream (VType_interp B)))
  (ih: ∀ y n, TrueUntil n (later I (TP y)) -> Hoare c (sprod2 (x, y)) (TP_SPred I) n) {n: ℕ}:
    Hoare (cloop2 c) x (TP_SPred I) n := by
  unfold Hoare at *; induction n
  · specialize ih (↑↑z⁻¹ (denote (cloop2 c) x)) 0 (by
      rw [TP_delay]; simp [TrueUntil]
    )
    rw [lifted_loop_unfold]
    apply ih
  · rename_i n hn
    simp at hn
    rw [later_delay_TrueUntil] at hn
    rw [<- TP_delay] at hn
    apply ih at hn
    rw [lifted_loop_unfold]
    apply hn

theorem Hoare_bracket {c: Ckt 1 A B} {fc}
  {x: stream (VType_interp A)}
  (Q: SPred (stream (VType_interp B))) (b: stream ℕ) {n: ℕ}
  (h: Hoare c (↑↑δ0 x) Q n)
  (hb: ∀ n y, TrueUntil n (Q y) -> ZeroAfter (y n) (b n)) :
    Hoare (cbracket c fc) x
      (fun y i => ∃ m, (Q m) i ∧ y i = sumVals (m i) (b i)) n := by
  set m := denote c (↑↑δ0 x)
  have hzm: ∀ t ≤ n, ZeroAfter (m t) (b t) := by
    intro t ht
    apply hb; apply TrueUntil_mono <;> tauto
  simp [Hoare, denote]; intro t ht
  use m; constructor; apply h; tauto
  rw [streamElim_zeroAfter]; apply hzm; tauto

theorem Hoare_bracket_ncausal {c: Ckt 1 A B} {fc}
  {x: stream (VType_interp A)}
  (Q: SPred (stream (VType_interp B))) (b: stream ℕ)
  (h: ∀ n, Hoare c (↑↑δ0 x) Q n)
  (hb: ∀ n y, TrueUntil n (Q y) -> ZeroAfter (y n) (b n)) {n: ℕ} :
    Hoare (cbracket c fc) x
      (fun y _ => ∃ m, ∀ i, (Q m) i ∧ y i = sumVals (m i) (b i)) n := by
  set m := denote c (↑↑δ0 x)
  have hzm: ∀ t, ZeroAfter (m t) (b t) := by
    intro t; apply hb; apply TrueUntil_mono <;> tauto
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

end Hoare

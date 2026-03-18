-- Propositions of ExtFP and IntFP
import DBSP.Circuits.CktProp
import DBSP.Circuits.LiftedScalar
import DBSP.Convergence.Spec
open CktBasic

-- Fixpoint proposition
-- for the outer iteration, i.e. the **1st** time dimension
section FPProp1
variable {ns: Bool} {A B C: VType}

-- FixAfter1 Props
lemma FixAfter1_mono {T: Type} {s: stream T} {n1 n2: ℕ}
  (h: FixAfter1 s n1)(hn: n1 ≤ n2):
     FixAfter1 s n2 := by
  intro m hm
  have := h _ hn
  specialize h m (by omega)
  rw [this, h]

lemma FixAfter1_iff_forall {T: Type} {s: stream T} {n: ℕ}:
    FixAfter1 s n <-> ∀ m ≥ n, FixAfter1 s m := by
  constructor <;> intro h
  · intro m hm; apply FixAfter1_mono <;> tauto
  · apply h; omega

lemma FixAfter1_extend {T: Type} {s: stream T} {n: ℕ}:
     (FixAfter1 s (n+1) ∧ s n = s (n+1)) <->
     FixAfter1 s n := by
  constructor
  · rintro ⟨h ,hn⟩
    intro m hm
    by_cases heq: (m = n)
    · subst heq; tauto
    · specialize h m (by omega)
      rw [hn]; tauto
  · intro h
    have hn : s (n+1) = s n := by
      apply h; omega
    symm; constructor; tauto
    intro m hm; rw [hn]
    apply h; omega

lemma FixAfter1_sprod {A B: Type} {s1: stream A} {s2: stream B}
  {p: ℕ}:
    FixAfter1 (sprod (s1, s2)) p <->
    FixAfter1 s1 p ∧ FixAfter1 s2 p := by
  simp [FixAfter1]; constructor <;> intros; swap; tauto
  rename_i h; constructor <;> intros m hm <;> specialize h m hm <;> tauto

lemma FixAfter1_sprod2 {A B: Type} {s1: stream (stream A)} {s2: stream (stream B)} {n: ℕ}:
    FixAfter1 (sprod2 (s1, s2)) n  <->
    FixAfter1 (s1) n ∧ FixAfter1 (s2) n := by
  simp [FixAfter1]; constructor <;> intro h
  · constructor <;>
    intro m hm <;> specialize h m hm <;>
    funext i <;>
    have := congr h (Eq.refl i) <;>
    simp at this <;> tauto
  · intro m hm; funext i; simp
    rcases h with ⟨h1, h2⟩
    specialize h1 m hm; specialize h2 m hm; tauto

lemma FixAfter1_sprodO {A B: Type} {ns: Bool}
  {s1: SOType ns A} {s2: SOType ns B} {n: ℕ}:
    FixAfter1 (sprodO ns (s1, s2)) n <->
    FixAfter1 s1 n ∧ FixAfter1 s2 n := by
  rcases ns <;> simp [sprodO]
  apply FixAfter1_sprod
  apply FixAfter1_sprod2

lemma FixAfter1_delay_0 {T: Type} [Zero T] {s: stream T}:
    FixAfter1 (z⁻¹ s) 0 <-> s = 0 := by
  simp [FixAfter1, delay]; constructor
  · intro h; funext m; specialize h (m+1) (by omega)
    simp at h; rw [h]; rfl
  · intro h; rw [h]; simp [FixAfter1]

lemma FixAfter1_delay_succ {T: Type} [Zero T] {s: stream T} {n: ℕ}:
    FixAfter1 (z⁻¹ s) (n+1) <-> FixAfter1 s n := by
  simp [FixAfter1]; constructor
  · intro h m hm
    specialize h (m+1) (by omega)
    simp at h; tauto
  · intro h m hm
    specialize h (m-1) (by omega)
    simp [delay]
    rcases m; omega
    simp at h ⊢; tauto

lemma FixAfter1_lifting {A B: Type} {s: stream A} {n: ℕ}
  {f: A -> B} (hx: FixAfter1 s n):
    FixAfter1 (↑↑f s) n := by
  simp [FixAfter1, lifting] at hx ⊢
  intros; congr 1; apply hx; tauto

lemma FixAfter1_liftO {A B: Type} {ns: Bool} {s: SOType ns A} {n: ℕ}
  {f: A -> B} (hx: FixAfter1 s n):
    FixAfter1 (liftO ns f s) n := by
  simp [liftO] at hx ⊢
  rcases ns <;> simp <;> apply FixAfter1_lifting <;> tauto

lemma ZeroAfter_impl_FixAfter1 {A: Type} [AddCommGroup A] {s: stream A} {n: ℕ}
  (hz: ZeroAfter s n):
    FixAfter1 s n := by
  simp [FixAfter1]; intro m hm
  rw [hz, hz] <;> omega

lemma ZeroAfterVec_impl_FixAfter2Vec {A: Type} [AddCommGroup A] {s: stream (stream A)} {b: stream ℕ}
  (hz: ZeroAfterVec s b):
    FixAfter2Vec s b := by
  intro m; simp [FixAfter2]
  apply ZeroAfter_impl_FixAfter1
  tauto

lemma ZeroAfter_succ_D_FixAfter1
  {A: Type} [AddCommGroup A] {s: stream A} {n: ℕ}:
    ZeroAfter (D s) (n+1) <-> FixAfter1 s n := by
  constructor
  · intro hz
    simp [FixAfter1]; intro m hm
    set k := m-n
    have : m = n + k := by omega
    rw [this]; clear this
    induction' k with k sk
    · simp
    · specialize hz (n+k+1) (by omega)
      simp [D] at hz
      rw [sk] at hz
      rw [<- add_assoc]
      rw [sub_eq_zero] at hz
      simp [hz]
  · intro h m hm
    simp [D, delay]
    split_ifs
    · omega
    · rw [sub_eq_zero]
      rw [h m (by omega)]
      rw [h (m-1) (by omega)]

lemma ZeroAfter_D_FixAfter1_delay
  {A: Type} [AddCommGroup A] {s: stream A} {n: ℕ}:
    ZeroAfter (D s) n <-> FixAfter1 (z⁻¹ s) n := by
  cases n
  case zero =>
    rw [FixAfter1_delay_0]
    constructor
    · intro h
      funext m
      induction m with
      | zero =>
        specialize h 0 (by omega)
        simp [D, delay] at h
        exact h
      | succ m ih =>
        specialize h (m+1) (by omega)
        simp [D, delay] at h
        rw [sub_eq_zero] at h
        rw [h]; exact ih
    · intro h; rw [h]
      intro m hm
      simp [D, delay]
  case succ n =>
    rw [ZeroAfter_succ_D_FixAfter1]
    rw [FixAfter1_delay_succ]

lemma ZeroAfter_succ_I_FixAfter1
  {A: Type} [AddCommGroup A] {s: stream A} {n: ℕ}:
    ZeroAfter s (n+1) <-> FixAfter1 (I s) n := by
  constructor
  · intro hz; intro m hm
    rw [integral_sumVals, integral_sumVals]
    symm
    apply sumVals_eq_helper
    · exact hz
    · omega
  · intro h m hm
    rw [<- integral_derivative s]
    simp [D, delay]
    split_ifs
    · omega
    · rw [sub_eq_zero]
      rw [h m (by omega)]
      rw [h (m-1) (by omega)]

lemma ZeroAfter_seq_D (c: Ckt A B ns) x n
  (hz: ZeroAfter (denote (c >>c cD) x) (n+1)):
    FixAfter1 (denote c x) n := by
  simp [denote] at hz
  rw [<- ZeroAfter_succ_D_FixAfter1]
  rcases ns <;> assumption

lemma FixAfter1_sub {A: Type} [AddCommGroup A]
  {s1 s2: stream A} {m n: ℕ}
  (h1: FixAfter1 s1 m) (h2: FixAfter1 s2 n):
    FixAfter1 (s1 - s2) (max m n) := by
  intro k hk
  simp
  have h1k := h1 k (by omega)
  have h2k := h2 k (by omega)
  have h1m := h1 (max m n) (by omega)
  have h2m := h2 (max m n) (by omega)
  rw [h1k, h2k, h1m, h2m]

@[simp]
lemma FixAfter1_const {A: Type} {a: A} {n: ℕ}:
    FixAfter1 (fun _ => a) n := by
  intro m hm
  simp

-- ExtFP1 Props

theorem delta_ExtFP1_impl_ZeroAfter {c: Ckt A B 0}
  {x: VType_interp A} {n: ℕ}
  (h: ExtFP1 c (δ0 x) n)
  (hz: denote c (δ0 x) n = 0):
    ZeroAfter (denote c (δ0 x)) n := by
  intro m hm
  rw [h.2 m hm, hz]

theorem delta_ZeroAfter_impl_ExtFP1 {c: Ckt A B 0}
  {x: VType_interp A} {n: ℕ}
  (hz: ZeroAfter (denote c (δ0 x)) n):
    ExtFP1 c (δ0 x) (n+1) := by
  constructor
  · apply FixAfter1_mono (n1 := 1)
    apply ZeroAfter_impl_FixAfter1
    apply δ0_ZeroAfter
    omega
  · apply ZeroAfter_impl_FixAfter1
    apply ZeroAfter_ge <;> tauto

lemma ExtFP1_mono {ns: Bool} (c: Ckt A B ns) (x: SOVType ns A) (n1 n2: ℕ)
  (h: ExtFP1 c x n1) (hn: n1 ≤ n2):
    ExtFP1 c x n2 := by
  simp [ExtFP1] at *
  rcases h with ⟨h1, h2⟩
  constructor <;> apply FixAfter1_mono <;> try assumption

lemma lifted_Ckt_ExtFP1 {A B: VType} {ns: Bool} (c: Ckt A B ns)
  (x: SOVType ns A) (hc: lifted_Ckt c):
    ExtFP1 c x = FixAfter1 x := by
  funext n; simp [ExtFP1]; intro h
  rcases hc with ⟨f, hc⟩; rw [hc]
  apply FixAfter1_lifting h

lemma ExtFP1_loop (c: Ckt (A ×ᵥ B) B ns) x n
  (h: ExtFP1 (cloop c) x n):
    ExtFP1 c (sprodO ns (x, z⁻¹ (denote (cloop c) x))) (n+1) := by
  simp [ExtFP1] at h ⊢
  rw [<- loop_unfold]
  constructor; swap
  · apply FixAfter1_mono; tauto; simp
  · rw [FixAfter1_sprodO]
    constructor
    apply FixAfter1_mono; tauto; simp
    rw [FixAfter1_delay_succ]; tauto

lemma ExtFP1_par (c1: Ckt A B ns) (c2: Ckt A C ns) x n
  (h: ExtFP1 (c1 &&c c2) x n):
    ExtFP1 c1 x n ∧ ExtFP1 c2 x n := by
  simp [ExtFP1] at h ⊢
  rcases h with ⟨h1, h2⟩
  simp [denote] at h2
  rw [FixAfter1_sprodO] at h2
  tauto

lemma ExtFP1_I_seq (c: Ckt A B 0) x n
  (h: ExtFP1 (cI >>c c) (δ0 x) n):
    ExtFP1 cI (δ0 x) n ∧ ExtFP1 c (denote cI (δ0 x)) n := by
  simp [ExtFP1] at h ⊢
  rcases h with ⟨h1, h2⟩
  simp [denote] at *
  have hz : ZeroAfter (δ0 x) (n+1) := by
    apply ZeroAfter_ge (δ0_ZeroAfter x)
    omega
  have hfix : FixAfter1 (I (δ0 x)) n := by
    rw [<- ZeroAfter_succ_I_FixAfter1]
    exact hz
  constructor
  · constructor <;> assumption
  · constructor <;> assumption

-- IntFP1 Props

lemma IntFP1_mono {ns: Bool} (c: Ckt A B ns) (x: SOVType ns A) (n1 n2: ℕ)
  (h: IntFP1 c x n1) (hn: n1 ≤ n2):
    IntFP1 c x n2 := by
  revert x; induction c <;> intro x
  case seq c1 c2 ih1 ih2 =>
    intro h; simp [IntFP1] at h
    rcases h with ⟨h1, h2⟩
    constructor
    · apply ih1; exact h1
    · apply ih2; exact h2
  case par c1 c2 ih1 ih2 =>
    intro h; simp [IntFP1] at h
    rcases h with ⟨h1, h2⟩
    constructor
    · apply ih1; exact h1
    · apply ih2; exact h2
  case loop c ih =>
    intro h; simp [IntFP1] at h
    apply ih; exact h
  case lifted_loop c ih =>
    intro h; simp [IntFP1] at h
    apply ih; exact h
  case bracket c ih =>
    intro h; simp [IntFP1] at h
    apply ih; exact h
  all_goals
    intro h
    apply ExtFP1_mono _ _ _ _ h hn

-- The Internal Fixpoint implies the External Fixpoint
theorem IntFP1_impl_ExtFP1 {ns: Bool} (c: Ckt A B ns) (x: SOVType ns A) (n: ℕ):
    IntFP1 c x n -> ExtFP1 c x n := by
  revert x; induction c <;> intro x <;> simp [IntFP1]
  case seq c1 c2 ih1 ih2 =>
    intro h1 h2
    specialize ih1 x h1; specialize ih2 (denote c1 x) h2
    rename Bool => ns; rcases ns <;> simp [ExtFP1] at ih1 ih2 ⊢ <;>
    simp [denote] <;> tauto
  case par c1 c2 ih1 ih2 =>
    intro h1 h2
    specialize ih1 x h1; specialize ih2 x h2
    simp [ExtFP1] at *; constructor; tauto
    simp [denote]; rw [FixAfter1_sprodO]; tauto
  case loop c ih =>
    intro h; apply ih at h; clear ih
    simp [ExtFP1] at *
    rw [FixAfter1_sprodO] at h
    rw [loop_unfold]
    tauto
  case lifted_loop c ih =>
    intro h; apply ih at h; clear ih
    simp [ExtFP1] at *
    rw [FixAfter1_sprod2] at h
    rw [lifted_loop_unfold]
    tauto
  case bracket c ih =>
    intro h
    apply ih at h; clear ih
    simp [ExtFP1, denote] at *
    rcases h with ⟨h1, h2⟩
    constructor
    · intro i hi
      specialize h1 i hi
      have := congr h1 (Eq.refl 0)
      simp at this; tauto
    · intro i hi
      simp [lifting]
      specialize h2 i hi
      rw [h2]

theorem delta_IntFP1_ZeroAfter {c: Ckt A B 0}
  {x: VType_interp A} {n: ℕ}
  (h: IntFP1 c (δ0 x) n)
  (hz: denote c (δ0 x) n = 0):
     ZeroAfter (denote c (δ0 x)) n := by
  apply delta_ExtFP1_impl_ZeroAfter (IntFP1_impl_ExtFP1 c (δ0 x) n h) hz

lemma I_IntFP1_delta (x: OVType 0 A):
    IntFP1 cI (δ0 x) 1 := by
  simp [cI] at ⊢
  have hz := δ0_ZeroAfter x
  have hf := hz
  rw [ZeroAfter_succ_I_FixAfter1, <- cI_denote] at hf
  constructor
  · simp [sprodO]
    rw [FixAfter1_sprod]
    constructor; tauto
    rw [FixAfter1_delay_succ]; tauto
  · simp [sprodO]
    nth_rewrite 1 [denote]; simp [liftO]
    intro m hm; simp
    rcases m; omega
    simp; apply hf; simp

lemma I_IntFP1 (x: SOVType ns A) n
  (h: FixAfter1 (I x) n):
    IntFP1 cI x (n+1) := by
  simp [cI, IntFP1]
  rw [<- cI]; simp [denote]
  have hz: ZeroAfter x (n+1) := by
    rcases ns <;>
    rw [ZeroAfter_succ_I_FixAfter1] <;>
    tauto
  rw [lifted_Ckt_ExtFP1 (hc:=by simp)]
  rw [FixAfter1_sprodO]
  constructor
  · apply ZeroAfter_impl_FixAfter1
    rcases ns <;> tauto
  · rw [FixAfter1_delay_succ]
    rcases ns <;> tauto

lemma D_IntFP1 (x: SOVType ns A) n (h: ZeroAfter (D x) n):
    IntFP1 cD x n := by
  simp [cD]
  have hfz : FixAfter1 (z⁻¹ x) n := by
    rcases ns <;>
    rw [ZeroAfter_D_FixAfter1_delay] at h <;>
    assumption
  have h := hfz
  rw [<- FixAfter1_extend] at h
  rw [FixAfter1_delay_succ] at h
  constructor
  · constructor <;> constructor <;> try tauto
    simp [denote, liftO_id]; tauto
  constructor
  · simp [denote]
    rw [FixAfter1_sprodO]
    simp [liftO_id]; tauto
  · simp [denote, liftO_id]
    apply FixAfter1_liftO
    rw [FixAfter1_sprodO]
    tauto

end FPProp1

-- Fixpoint proposition
-- for the inner iteration, i.e. the **2nd** time dimension
section FPProp2
variable {A B C: VType}

-- FixAfter2 Props

lemma FixAfter2_mono {T: Type} {s: stream (stream T)} {m: ℕ} {n1 n2: ℕ}
  (h: FixAfter2 s m n1)(hn: n1 ≤ n2):
     FixAfter2 s m n2 := by
  simp [FixAfter2] at h ⊢
  apply FixAfter1_mono <;> assumption

lemma FixAfter2_sprod2 {A B: Type} {s1: stream (stream A)} {s2: stream (stream B)}
  {m n1 n2: ℕ} (h1: FixAfter2 s1 m n1) (h2: FixAfter2 s2 m n2) (hn: n1 ≤ n2):
    FixAfter2 (sprod2 (s1, s2)) m n2 := by
  intro i hi
  simp [FixAfter2, sprod2, sprod]
  constructor
  · simp [h1 i (by omega), h1 n2 (by omega)]
  · simp [h2 i (by omega), h2 n2 (by omega)]

lemma FixAfter2_sprod2_iff {A B: Type} {s1: stream (stream A)} {s2: stream (stream B)}
  {m n: ℕ}:
    FixAfter2 (sprod2 (s1, s2)) m n  <->
    FixAfter2 (s1) m n ∧ FixAfter2 (s2) m n := by
  simp [FixAfter2, FixAfter1]; constructor <;> intros; swap; tauto
  rename_i h; constructor <;> intros m hm <;> specialize h m hm <;> tauto

lemma FixAfter2_lifted_scalar {A B: Type} {s: stream (stream A)} {m n: ℕ}
  {f: A -> B} (hx: FixAfter2 s m n):
    FixAfter2 (liftO 1 f s) m n := by
  simp [FixAfter2, liftO] at hx ⊢
  intro i hi; simp
  apply congr; simp
  apply hx; tauto

-- The nested fixedpoint is causal
-- in a stronger sense that it only depends on row `m` of the input
theorem FixAfter2_causal {T: Type} {m: ℕ}
  (s1 s2: stream (stream T))
  (heq: s1 m = s2 m):
    FixAfter2 s1 m = FixAfter2 s2 m := by
  funext n; simp [FixAfter2]; rw [heq]

-- FixAfter2Vec Props
lemma FixAfter2Vec_mono {A: Type} {s: stream (stream A)} {b1 b2: stream ℕ}
  (h: FixAfter2Vec s b1) (hb: b1 ≤ b2):
    FixAfter2Vec s b2 := by
  intro i
  apply FixAfter2_mono <;> tauto

lemma FixAfter2Vec_sprod2 {A B: Type}
  {s1: stream (stream A)} {s2: stream (stream B)} {b: stream ℕ}:
    FixAfter2Vec (sprod2 (s1, s2)) b <->
    FixAfter2Vec s1 b ∧ FixAfter2Vec s2 b := by
  constructor
  · intro h; constructor <;> intro i <;>
    specialize h i <;>
    rw [FixAfter2_sprod2_iff] at h <;> tauto
  · rintro ⟨h1, h2⟩
    intro i; rw [FixAfter2_sprod2_iff]; tauto

lemma FixAfter2Vec_delay {A: Type} [Zero A]
  {x: stream (stream A)} {b: stream ℕ}:
    FixAfter2Vec x b <->
    FixAfter2Vec (z⁻¹ x) (z⁻¹ b) := by
  constructor <;> intro h i
  · rcases i with _ | i
    · simp [FixAfter2, FixAfter1]
    · simp [FixAfter2]; apply h
  · specialize h (i+1)
    simp [FixAfter2] at h ⊢
    tauto

lemma FixAfter2Vec_lifting {A B: Type} {s: stream (stream A)} {b: stream ℕ}
  {f: A -> B} (hx: FixAfter2Vec s b):
    FixAfter2Vec (↑↑↑↑f s) b := by
  intro i
  apply FixAfter2_lifted_scalar
  apply hx

lemma FixAfter2Vec_sub {A: Type} [AddCommGroup A]
  {s1 s2: stream (stream A)} {b1 b2: stream ℕ}
  (h1: FixAfter2Vec s1 b1) (h2: FixAfter2Vec s2 b2):
    FixAfter2Vec (s1 - s2) (fun i => max (b1 i) (b2 i)) := by
  intro i
  simp [FixAfter2]
  apply FixAfter1_sub <;> tauto

lemma FixAfter2Vec_D {A: Type} [AddCommGroup A]
  {s: stream (stream A)} {b: stream ℕ}
  (h: FixAfter2Vec s b):
    FixAfter2Vec (D s) (fun i => max (b i) (z⁻¹ b i)) := by
  unfold D
  apply FixAfter2Vec_sub; assumption
  rw [<- FixAfter2Vec_delay]; assumption

lemma ZeroAfterVec_delay {A: Type} [Zero A]
  {x: stream (stream A)} {b: stream ℕ}:
    ZeroAfterVec x b <->
    ZeroAfterVec (z⁻¹ x) (z⁻¹ b) := by
  constructor <;> intro h i
  · simp [delay]
    intro m hm
    rcases i with _ | i
    · simp
    · have := h i
      simp at hm
      apply this
      omega
  · specialize h (i+1)
    simp [delay] at h
    intro m hm
    apply h
    omega

lemma ZeroAfterVec_sub {A: Type} [AddCommGroup A]
  {s1 s2: stream (stream A)} {b1 b2: stream ℕ}
  (h1: ZeroAfterVec s1 b1) (h2: ZeroAfterVec s2 b2):
    ZeroAfterVec (s1 - s2) (fun i => max (b1 i) (b2 i)) := by
  intro i
  have h1' : ZeroAfter (s1 i) (max (b1 i) (b2 i)) := ZeroAfter_ge (h1 i) _ (le_max_left _ _)
  have h2' : ZeroAfter (s2 i) (max (b1 i) (b2 i)) := ZeroAfter_ge (h2 i) _ (le_max_right _ _)
  simp
  have := sub_zeroAfter h1' h2'
  simp [ge_iff_le] at this
  exact this

lemma ZeroAfter_add {A: Type} [AddCommGroup A]
  {s1 s2: stream A} {b1 b2: ℕ}
  (h1: ZeroAfter s1 b1) (h2: ZeroAfter s2 b2):
    ZeroAfter (s1 + s2) (max b1 b2) := by
  have h1' : ZeroAfter s1 (max b1 b2) := ZeroAfter_ge h1 _ (le_max_left _ _)
  have h2' : ZeroAfter s2 (max b1 b2) := ZeroAfter_ge h2 _ (le_max_right _ _)
  intro m hm; simp
  have: s1 m = 0 := by apply h1'; omega
  simp [this]
  apply h2'; omega

lemma ZeroAfterVec_add {A: Type} [AddCommGroup A]
  {s1 s2: stream (stream A)} {b1 b2: stream ℕ}
  (h1: ZeroAfterVec s1 b1) (h2: ZeroAfterVec s2 b2):
    ZeroAfterVec (s1 + s2) (fun i => max (b1 i) (b2 i)) := by
  intro i
  simp; apply ZeroAfter_add <;> tauto

lemma ZeroAfterVec_D {A: Type} [AddCommGroup A]
  {s: stream (stream A)} {b: stream ℕ}
  (h: ZeroAfterVec s b):
    ZeroAfterVec (D s) (fun i => max (b i) (z⁻¹ b i)) := by
  unfold D
  apply ZeroAfterVec_sub; assumption
  rw [← ZeroAfterVec_delay]; assumption

lemma ZeroAfterVec_I {A: Type} [AddCommGroup A]
  {s: stream (stream A)} {b: stream ℕ}
  (h: ZeroAfterVec s b):
    ZeroAfterVec (I s) (I b) := by
  intro i; induction i <;> simp
  · apply h
  apply ZeroAfter_ge
  apply ZeroAfter_add <;> tauto
  simp

lemma ZeroAfterVec_mono {A: Type} [AddCommGroup A]
  {s: stream (stream A)} {b1 b2: stream ℕ}
  (h: ZeroAfterVec s b1) (hb: ∀ i, b1 i ≤ b2 i):
    ZeroAfterVec s b2 := by
  intro i
  have h1 : ZeroAfter (s i) (b1 i) := h i
  apply ZeroAfter_ge h1 _ (hb i)

-- ExtFP2 Props

lemma ExtFP2_mono {c: Ckt A B 1} {x: SOVType 1 A}
  {m n1 n2: ℕ} (h: ExtFP2 c x m n1) (hn: n1 ≤ n2):
    ExtFP2 c x m n2 := by
  simp [ExtFP2] at *
  rcases h with ⟨h1, h2⟩
  constructor <;> apply FixAfter1_mono <;> try assumption

lemma DenoteLiftedScalar_ExtFP2 {A B: VType} (c: Ckt A B 1)
  (x: SOVType 1 A) {f} (hc: DenoteLiftedScalar c f):
    ExtFP2 c x = FixAfter2 x := by
  funext m n; simp [ExtFP2]; intro h
  rw [hc]
  apply FixAfter2_lifted_scalar h

lemma LiftedScalar_ExtFP2 {A B: VType} (c: Ckt A B 1)
  (x: SOVType 1 A) (hc: LiftedScalar c):
    ExtFP2 c x = FixAfter2 x := by
  apply LiftedScalar_Denote at hc
  rcases hc with ⟨f, hf⟩
  apply DenoteLiftedScalar_ExtFP2; tauto

-- The nested External Fixpoint is causal
theorem ExtFP2_causal (c: Ckt A B 1):
    Causal (ExtFP2 c) := by
  intro x1 x2 m hca; funext n
  simp [ExtFP2, FixAfter2]
  have : x1 m = x2 m := by
    apply hca; rfl
  rw [this]
  have : denote c x1 m = denote c x2 m := by
    have := ckt_causalO c
    apply causalO_is_causal at this
    apply this; tauto
  rw [this]

theorem delta_ExtFP2_impl_ZeroAfter {c: Ckt A B 1}
  {x: SOVType 0 A} {m n: ℕ}
  (h: ExtFP2 c (↑↑δ0 x) m n)
  (hz: denote c (↑↑δ0 x) m n = 0):
    ZeroAfter (denote c (↑↑δ0 x) m) n := by
  intro k hk
  rw [h.2 k hk, hz]

theorem delta_ZeroAfter_impl_ExtFP2 {c: Ckt A B 1}
  {x: SOVType 0 A} {m n: ℕ}
  (hz: ZeroAfter (denote c (↑↑δ0 x) m) n):
    ExtFP2 c (↑↑δ0 x) m (n+1) := by
  constructor
  · simp [FixAfter2]
    apply FixAfter1_mono (n1 := 1)
    apply ZeroAfter_impl_FixAfter1
    apply δ0_ZeroAfter
    omega
  · simp [FixAfter2]
    apply ZeroAfter_impl_FixAfter1
    apply ZeroAfter_ge <;> tauto

-- ExtFP2Vec Props

lemma forall_and_iff {A: Type} {P Q: A -> Prop}: (∀ x, P x ∧ Q x) <-> (∀ x, P x) ∧ (∀ x, Q x) :=
  Iff.intro (fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩) (fun h x => ⟨h.1 x, h.2 x⟩)

lemma ExtFP2Vec_iff {c: Ckt A B 1} {x: SOVType 1 A} {b: stream ℕ}:
    ExtFP2Vec c x b <->
    FixAfter2Vec x b ∧ FixAfter2Vec (denote c x) b := by
  simp [ExtFP2Vec]; apply forall_and_iff

-- IntFP2 Props

lemma IntFP2_mono {c: Ckt A B 1} {x: SOVType 1 A}
  {m n1 n2: ℕ} (h: IntFP2 c x m n1) (hn: n1 ≤ n2):
    IntFP2 c x m n2 := by
  revert c; apply Ckt_generalize_ns_1
  intro ns c hns; revert x; induction c <;>
    (try subst hns) <;> (try tauto) <;>
    intro x
  case seq c1 c2 ih1 ih2 =>
    intro h; simp [IntFP2] at h
    rcases h with ⟨h1, h2⟩
    simp [IntFP2]; constructor <;> tauto
  case par c1 c2 ih1 ih2 =>
    intro h; simp [IntFP2] at h
    rcases h with ⟨h1, h2⟩
    simp [IntFP2]; constructor <;> tauto
  case lifting c =>
    intro h; simp [IntFP2] at ⊢ h
    apply IntFP1_mono _ _ _ _ h hn
  case loop c ih =>
    simp at ⊢ ih
    simp [IntFP2]; apply ih
  case lifted_loop c ih =>
    simp at ⊢ ih
    simp [IntFP2]; apply ih
  all_goals
    intro h; simp [IntFP2] at ⊢ h
    apply ExtFP2_mono <;> tauto

-- The nested Internal Fixpoint is causal
theorem IntFP2_causal (c: Ckt A B 1):
    Causal (IntFP2 c) := by
  intro x1 x2 m hca; funext n; revert c; apply Ckt_generalize_ns_1
  intro ns c hns; revert x1 x2; induction c <;>
    (try subst hns) <;> (try tauto) <;>
    intro x1 x2 hca <;> simp [IntFP2] <;>
    (try rw [ExtFP2_causal]; tauto)
  case seq c1 c2 ih1 ih2 =>
    simp at ih1 ih2
    specialize ih1 x1 x2 hca
    rw [<- ih1]; simp; intro h1
    apply ih2
    apply causal_respects_agreeUpto
    apply causalO_is_causal; apply ckt_causalO
    tauto
  case par c1 c2 ih1 ih2 =>
    simp at ih1 ih2
    specialize ih1 x1 x2 hca; specialize ih2 x1 x2 hca
    rw [ih1, ih2]
  case loop c ih =>
    simp at ih; apply ih
    intro j hj; funext k; simp
    constructor
    · specialize hca j hj; rw [hca]
    rcases j <;> simp
    apply congr _ (by simp)
    have := ckt_causalO (cloop c)
    apply causalO_is_causal at this
    apply this
    intro t ht; apply hca; omega
  case lifted_loop c ih =>
    simp at ih; apply ih
    intro j hj; funext k; simp
    constructor
    · specialize hca j hj; rw [hca]
    rcases k <;> simp
    apply congr _ (by simp)
    have := ckt_causalO (cloop2 c)
    apply causalO_is_causal at this
    apply this
    intro t ht; apply hca; omega
  case lifting c =>
    have : x1 m = x2 m := by
      apply hca; rfl
    rw [this]

-- The nested Internal Fixpoint implies the nested External Fixpoint
theorem IntFP2_impl_ExtFP2 (c: Ckt A B 1) (x: SOVType 1 A) (m n: ℕ):
    IntFP2 c x m n -> ExtFP2 c x m n := by
  revert c; apply Ckt_generalize_ns_1
  intro ns c hns; revert x m n; induction c <;>
    (try subst hns) <;> (try tauto) <;>
    intro x m n <;> simp [IntFP2]
  case seq c1 c2 ih1 ih2 =>
    intro h1 h2; simp at ih1 ih2
    apply ih1 at h1; apply ih2 at h2
    simp [ExtFP2] at h1 h2 ⊢
    simp [denote]; tauto
  case par c1 c2 ih1 ih2 =>
    intro h1 h2; simp at ih1 ih2
    apply ih1 at h1; apply ih2 at h2
    simp [ExtFP2] at h1 h2 ⊢
    simp [denote, sprodO]; rw [FixAfter2_sprod2_iff]; tauto
  case loop c ih =>
    intro h; simp at ih
    apply ih at h; clear ih
    simp [ExtFP2] at *
    rw [FixAfter2_sprod2_iff] at h
    rw [loop_unfold]
    tauto
  case lifted_loop c ih =>
    intro h; simp at ih
    apply ih at h; clear ih
    simp [ExtFP2] at *
    rw [FixAfter2_sprod2_iff] at h
    rw [lifted_loop_unfold]
    tauto
  case lifting c =>
    intro h; simp [ExtFP2] at *
    apply IntFP1_impl_ExtFP1 at h
    constructor; apply h.1
    simp [denote, FixAfter2]
    apply h.2

lemma I_IntFP2_delta (x: OVType 1 A) m:
    IntFP2 cI (↑↑δ0 x) m 1 := by
  simp [cI, IntFP2]
  rw [<- cI, cI_denote]
  rw [integral_lift_comm _ _ delta_linear]
  constructor
  · rw [FixAfter2_sprod2_iff]
    simp [FixAfter2]
    constructor; apply δ0_ZeroAfter
    rcases m; simp [FixAfter1]
    simp; apply δ0_ZeroAfter
  simp [denote, liftO]
  intro k hk; simp
  split_ifs; omega
  simp [delay]; split_ifs; simp
  apply δ0_ZeroAfter; omega

-- IntFP2Vec Props

theorem delta_IntFP2Vec_ZeroAfterVec {c: Ckt A B 1}
  {x: SOVType 0 A} {b: stream ℕ}
  (h: IntFP2Vec c (↑↑δ0 x) b)
  (hz: ∀ i, denote c (↑↑δ0 x) i (b i) = 0):
     ZeroAfterVec (denote c (↑↑δ0 x)) b := by
  intro i
  apply delta_ExtFP2_impl_ZeroAfter (IntFP2_impl_ExtFP2 c (↑↑δ0 x) i (b i) (h i)) (hz i)

lemma IntFP2Vec_impl_ExtFP2Vec {c: Ckt A B 1} {x: SOVType 1 A} {b: stream ℕ}:
    IntFP2Vec c x b -> ExtFP2Vec c x b := by
  simp [IntFP2Vec, ExtFP2Vec]
  intros; apply IntFP2_impl_ExtFP2; tauto

lemma IntFP2Vec_seq {c1: Ckt A B 1} {c2: Ckt B C 1}
  {x: SOVType 1 A} {b: stream ℕ}:
    IntFP2Vec (c1 >>c c2) x b <->
    IntFP2Vec c1 x b ∧ IntFP2Vec c2 (denote c1 x) b := by
  simp [IntFP2Vec, IntFP2]; aesop

lemma IntFP2Vec_par {c1: Ckt A B 1} {c2: Ckt A C 1}
  {x: SOVType 1 A} {b: stream ℕ}:
    IntFP2Vec (c1 &&c c2) x b <->
    IntFP2Vec c1 x b ∧ IntFP2Vec c2 x b := by
  simp [IntFP2Vec, IntFP2]; aesop

lemma IntFP2Vec_mono {c: Ckt A B 1} {x: SOVType 1 A} {b1 b2: stream ℕ}
  (h: b1 ≤ b2) (h1: IntFP2Vec c x b1):
    IntFP2Vec c x b2 := by
  intro i
  apply IntFP2_mono <;> tauto

lemma I_IntFP2Vec {x: SOVType 1 A} {b}
  (h: FixAfter2Vec x b):
    IntFP2Vec cI (D x) (fun i => max (b i) (z⁻¹ b i)) := by
  intro m; simp [cI, IntFP2]
  rw [<- cI]; simp [denote]
  rw [DenoteLiftedScalar_ExtFP2 (hc:=by constructor)]
  rw [FixAfter2_sprod2_iff]
  constructor
  · apply FixAfter2Vec_D; assumption
  · apply FixAfter2_mono
    apply FixAfter2Vec_delay.1; tauto; omega

lemma D_IntFP2Vec {x: SOVType 1 A}
  {b: stream ℕ} (hfa: FixAfter2Vec x b):
    IntFP2Vec cD x (fun i => max (b i) (z⁻¹ b i)) := by
  intro i
  simp [cD, IntFP2]
  constructor; constructor
  · rw [LiftedScalar_ExtFP2 (hc:= by constructor)]
    apply FixAfter2_mono; tauto; omega
  · constructor
    apply FixAfter2_mono; tauto; omega
    simp [denote]
    apply FixAfter2_mono
    apply FixAfter2Vec_delay.1; tauto; omega
  · rw [LiftedScalar_ExtFP2 (hc:= by constructor)]
    simp [denote, sprodO, liftO]
    rw [FixAfter2_sprod2_iff]
    constructor
    apply FixAfter2_mono; tauto; omega
    apply FixAfter2_mono
    apply FixAfter2Vec_delay.1; tauto; omega

end FPProp2

section IntConvProp
variable {A B C: VType} {ns: Bool}

@[simp]
lemma IntConv_cI {ns: Bool} {A: VType}{x: SOVType ns A}:
    IntConv cI x := by
  simp [cI, IntConv]

@[simp]
lemma ExtConv_cI {ns: Bool} {A: VType}{x: SOVType ns A}:
    ExtConv cI x := by
  simp [cI, ExtConv]

@[simp]
lemma IntConv_cD {ns: Bool} {A: VType}{x: SOVType ns A}:
    IntConv cD x := by
  simp [cD, IntConv]

@[simp]
lemma ExtConv_cD {ns: Bool} {A: VType}{x: SOVType ns A}:
    ExtConv cD x := by
  simp [cD, ExtConv]

lemma ExtConv_cΔ {c: Ckt A B ns}
  {x: SOVType ns A} (h: ExtConv c x):
    ExtConv (cΔ c) (D x) := by
  simp [cΔ, ExtConv]; tauto

lemma IntConv_cΔ {c: Ckt A B ns}
  {x: SOVType ns A} (h: IntConv c x):
    IntConv (cΔ c) (D x) := by
  simp [cΔ, IntConv]; tauto

lemma IntConv_bracket_alt {c: Ckt A B 1} {x: SOVType 0 A}
  (h: IntConv (cbracket c) x):
    IntConv c (↑↑δ0 x) ∧
    ∀ i, ∃ b, IntFP2 c (↑↑δ0 x) i b ∧ ZeroAfter (denote c (↑↑δ0 x) i) b := by
  simp [IntConv] at h
  rcases h with ⟨h1, ⟨b, ⟨h2, h3⟩⟩⟩
  simp [h1]
  intro i; use (b i)
  tauto

lemma IntConv_iff_IntConv' {c: Ckt A B ns} {x: SOVType ns A}:
    IntConv c x <-> IntConv' c x := by
  revert x
  induction c <;> intro x <;> simp [IntConv, IntConv']
  intro h; constructor <;> rintro ⟨b, h1, h2⟩ <;>
  use b <;> simp [h1] <;> apply IntFP2Vec_impl_ExtFP2Vec at h1
  · intro i; apply h2; simp
  · intro i j h
    rw [<- h2 i]
    specialize h1 i
    apply h1.2; omega

theorem IntConv_impl_ExtConv {c: Ckt A B ns}
  {x: SOVType ns A} (h: IntConv c x):
    ExtConv c x := by
  revert x
  induction c <;> intro x h <;> simp [IntConv, ExtConv] at h ⊢
  case seq c1 c2 ih1 ih2 =>
    rcases h with ⟨h1, h2⟩
    exact ⟨ih1 h1, ih2 h2⟩
  case par c1 c2 ih1 ih2 =>
    rcases h with ⟨h1, h2⟩
    exact ⟨ih1 h1, ih2 h2⟩
  case lifting c ih =>
    intro j
    exact ih (h j)
  case loop c ih =>
    exact ih h
  case lifted_loop c ih =>
    exact ih h
  case bracket c ih =>
    rcases h with ⟨h1, ⟨b, h2, h3⟩⟩
    exact ⟨ih h1, ⟨b, h3⟩⟩

end IntConvProp

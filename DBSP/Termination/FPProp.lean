-- Propositions of ExtFP and IntFP
import DBSP.Circuits.CktProp
import DBSP.Termination.Spec
open CktBasic

-- Fixpoint proposition
-- for the outer iteration, i.e. the **1st** time dimension
section FPProp1
variable {ns: Bool} {A B C: VType}

-- FixedAfter1 Props
lemma FixedAfter1_mono {T: Type} {s: stream T} {n1 n2: ℕ}
  (h: FixedAfter1 s n1)(hn: n1 ≤ n2):
     FixedAfter1 s n2 := by
  intro m hm
  have := h _ hn
  specialize h m (by omega)
  rw [this, h]

lemma FixedAfter1_iff_forall {T: Type} {s: stream T} {n: ℕ}:
    FixedAfter1 s n <-> ∀ m ≥ n, FixedAfter1 s m := by
  constructor <;> intro h
  · intro m hm; apply FixedAfter1_mono <;> tauto
  · apply h; omega

lemma FixedAfter1_extend {T: Type} {s: stream T} {n: ℕ}:
     (FixedAfter1 s (n+1) ∧ s n = s (n+1)) <->
     FixedAfter1 s n := by
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

lemma FixedAfter1_sprod {A B: Type} {s1: stream A} {s2: stream B}
  {p: ℕ}:
    FixedAfter1 (sprod (s1, s2)) p <->
    FixedAfter1 s1 p ∧ FixedAfter1 s2 p := by
  simp [FixedAfter1]; constructor <;> intros; swap; tauto
  rename_i h; constructor <;> intros m hm <;> specialize h m hm <;> tauto

lemma FixedAfter1_sprod2 {A B: Type} {s1: stream (stream A)} {s2: stream (stream B)} {n: ℕ}:
    FixedAfter1 (sprod2 (s1, s2)) n  <->
    FixedAfter1 (s1) n ∧ FixedAfter1 (s2) n := by
  simp [FixedAfter1]; constructor <;> intro h
  · constructor <;>
    intro m hm <;> specialize h m hm <;>
    funext i <;>
    have := congr h (Eq.refl i) <;>
    simp at this <;> tauto
  · intro m hm; funext i; simp
    rcases h with ⟨h1, h2⟩
    specialize h1 m hm; specialize h2 m hm; tauto

lemma FixedAfter1_sprodO {A B: Type} {ns: Bool}
  {s1: SOType ns A} {s2: SOType ns B} {n: ℕ}:
    FixedAfter1 (sprodO ns (s1, s2)) n <->
    FixedAfter1 s1 n ∧ FixedAfter1 s2 n := by
  rcases ns <;> simp [sprodO]
  apply FixedAfter1_sprod
  apply FixedAfter1_sprod2

lemma FixedAfter1_delay_0 {T: Type} [Zero T] {s: stream T}:
    FixedAfter1 (z⁻¹ s) 0 <-> s = 0 := by
  simp [FixedAfter1, delay]; constructor
  · intro h; funext m; specialize h (m+1) (by omega)
    simp at h; rw [h]; rfl
  · intro h; rw [h]; simp [FixedAfter1]

lemma FixedAfter1_delay_succ {T: Type} [Zero T] {s: stream T} {n: ℕ}:
    FixedAfter1 (z⁻¹ s) (n+1) <-> FixedAfter1 s n := by
  simp [FixedAfter1]; constructor
  · intro h m hm
    specialize h (m+1) (by omega)
    simp at h; tauto
  · intro h m hm
    specialize h (m-1) (by omega)
    simp [delay]
    rcases m; omega
    simp at h ⊢; tauto

lemma FixedAfter1_lifting {A B: Type} {s: stream A} {n: ℕ}
  {f: A -> B} (hx: FixedAfter1 s n):
    FixedAfter1 (↑↑f s) n := by
  simp [FixedAfter1, lifting] at hx ⊢
  intros; congr 1; apply hx; tauto

lemma FixedAfter1_liftO {A B: Type} {ns: Bool} {s: SOType ns A} {n: ℕ}
  {f: A -> B} (hx: FixedAfter1 s n):
    FixedAfter1 (liftO ns f s) n := by
  simp [liftO] at hx ⊢
  rcases ns <;> simp <;> apply FixedAfter1_lifting <;> tauto

lemma ZeroAfter_impl_FixedAfter1 {A: Type} [AddCommGroup A] {s: stream A} {n: ℕ}
  (hz: ZeroAfter s n):
    FixedAfter1 s n := by
  simp [FixedAfter1]; intro m hm
  rw [hz, hz] <;> omega

lemma ZeroAfter_succ_D_FixedAfter1
  {A: Type} [AddCommGroup A] {s: stream A} {n: ℕ}:
    ZeroAfter (D s) (n+1) <-> FixedAfter1 s n := by
  constructor
  · intro hz
    simp [FixedAfter1]; intro m hm
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

lemma ZeroAfter_D_FixedAfter1_delay
  {A: Type} [AddCommGroup A] {s: stream A} {n: ℕ}:
    ZeroAfter (D s) n <-> FixedAfter1 (z⁻¹ s) n := by
  cases n
  case zero =>
    rw [FixedAfter1_delay_0]
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
    rw [ZeroAfter_succ_D_FixedAfter1]
    rw [FixedAfter1_delay_succ]

lemma ZeroAfter_succ_I_FixedAfter1
  {A: Type} [AddCommGroup A] {s: stream A} {n: ℕ}:
    ZeroAfter s (n+1) <-> FixedAfter1 (I s) n := by
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
    FixedAfter1 (denote c x) n := by
  simp [denote] at hz
  rw [<- ZeroAfter_succ_D_FixedAfter1]
  rcases ns <;> assumption

-- ExtFP1 Props

lemma ExtFP1_mono {ns: Bool} (c: Ckt A B ns) (x: SOVType ns A) (n1 n2: ℕ)
  (h: ExtFP1 c x n1) (hn: n1 ≤ n2):
    ExtFP1 c x n2 := by
  simp [ExtFP1] at *
  rcases h with ⟨h1, h2⟩
  constructor <;> apply FixedAfter1_mono <;> try assumption

lemma lifted_Ckt_ExtFP1 {A B: VType} {ns: Bool} (c: Ckt A B ns)
  (x: SOVType ns A) (hc: lifted_Ckt c):
    ExtFP1 c x = FixedAfter1 x := by
  funext n; simp [ExtFP1]; intro h
  rcases hc with ⟨f, hc⟩; rw [hc]
  apply FixedAfter1_lifting h

lemma ExtFP1_loop (c: Ckt (A ×ᵥ B) B ns) x n
  (h: ExtFP1 (cloop c) x n):
    ExtFP1 c (sprodO ns (x, z⁻¹ (denote (cloop c) x))) (n+1) := by
  simp [ExtFP1] at h ⊢
  rw [<- loop_unfold]
  constructor; swap
  · apply FixedAfter1_mono; tauto; simp
  · rw [FixedAfter1_sprodO]
    constructor
    apply FixedAfter1_mono; tauto; simp
    rw [FixedAfter1_delay_succ]; tauto

lemma ExtFP1_par (c1: Ckt A B ns) (c2: Ckt A C ns) x n
  (h: ExtFP1 (c1 &&c c2) x n):
    ExtFP1 c1 x n ∧ ExtFP1 c2 x n := by
  simp [ExtFP1] at h ⊢
  rcases h with ⟨h1, h2⟩
  simp [denote] at h2
  rw [FixedAfter1_sprodO] at h2
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
  have hfix : FixedAfter1 (I (δ0 x)) n := by
    rw [<- ZeroAfter_succ_I_FixedAfter1]
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
  case loop_lifted c ih =>
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
    simp [denote]; rw [FixedAfter1_sprodO]; tauto
  case loop c ih =>
    intro h; apply ih at h; clear ih
    simp [ExtFP1] at *
    rw [FixedAfter1_sprodO] at h
    rw [loop_unfold]
    tauto
  case loop_lifted c ih =>
    intro h; apply ih at h; clear ih
    simp [ExtFP1] at *
    rw [FixedAfter1_sprod2] at h
    rw [loop_lifted_unfold]
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

lemma I_IntFP1 (x: OVType 0 A):
    IntFP1 cI (δ0 x) 1 := by
  simp [cI] at ⊢
  have hz := δ0_ZeroAfter x
  have hf := hz
  rw [ZeroAfter_succ_I_FixedAfter1, <- cI_denote] at hf
  constructor
  · simp [sprodO]
    rw [FixedAfter1_sprod]
    constructor; tauto
    rw [FixedAfter1_delay_succ]; tauto
  · simp [sprodO]
    nth_rewrite 1 [denote]; simp [liftO]
    intro m hm; simp
    rcases m; omega
    simp; apply hf; simp

lemma ZeroAfter_D_IntFP1 (x: SOVType ns A) n (h: ZeroAfter (D x) n):
    IntFP1 cD x n := by
  simp [cD]
  have hfz : FixedAfter1 (z⁻¹ x) n := by
    rcases ns <;>
    rw [ZeroAfter_D_FixedAfter1_delay] at h <;>
    assumption
  have h := hfz
  rw [<- FixedAfter1_extend] at h
  rw [FixedAfter1_delay_succ] at h
  constructor
  · constructor <;> constructor <;> try tauto
    simp [denote, liftO_id]; tauto
  constructor
  · simp [denote]
    rw [FixedAfter1_sprodO]
    simp [liftO_id]; tauto
  · simp [denote, liftO_id]
    apply FixedAfter1_liftO
    rw [FixedAfter1_sprodO]
    tauto

end FPProp1

-- Fixpoint proposition
-- for the inner iteration, i.e. the **2nd** time dimension
section FPProp2
variable {A B C: VType}

-- FixedAfter2 Props

lemma FixedAfter2_mono {A B: Type} {s1: stream (stream A)} {s2: stream (stream B)}
  {m n1 n2: ℕ} (h1: FixedAfter2 s1 m n1) (h2: FixedAfter2 s2 m n2) (hn: n1 ≤ n2):
    FixedAfter2 (sprod2 (s1, s2)) m n2 := by
  intro i hi
  simp [FixedAfter2, sprod2, sprod]
  constructor
  · simp [h1 i (by omega), h1 n2 (by omega)]
  · simp [h2 i (by omega), h2 n2 (by omega)]

lemma FixedAfter2_sprod2 {A B: Type} {s1: stream (stream A)} {s2: stream (stream B)}
  {m n: ℕ}:
    FixedAfter2 (sprod2 (s1, s2)) m n  <->
    FixedAfter2 (s1) m n ∧ FixedAfter2 (s2) m n := by
  simp [FixedAfter2, FixedAfter1]; constructor <;> intros; swap; tauto
  rename_i h; constructor <;> intros m hm <;> specialize h m hm <;> tauto

lemma FixedAfter2_lifted_scalar {A B: Type} {s: stream (stream A)} {m n: ℕ}
  {f: A -> B} (hx: FixedAfter2 s m n):
    FixedAfter2 (liftO 1 f s) m n := by
  simp [FixedAfter2, liftO] at hx ⊢
  intro i hi; simp
  apply congr; simp
  apply hx; tauto

-- The nested fixedpoint is causal
-- in a stronger sense that it only depends on row `m` of the input
theorem FixedAfter2_causal {T: Type} {m: ℕ}
  (s1 s2: stream (stream T))
  (heq: s1 m = s2 m):
    FixedAfter2 s1 m = FixedAfter2 s2 m := by
  funext n; simp [FixedAfter2]; rw [heq]

-- ExtFP2 Props

lemma ExtFP2_mono {c: Ckt A B 1} {x: SOVType 1 A}
  {m n1 n2: ℕ} (h: ExtFP2 c x m n1) (hn: n1 ≤ n2):
    ExtFP2 c x m n2 := by
  simp [ExtFP2] at *
  rcases h with ⟨h1, h2⟩
  constructor <;> apply FixedAfter1_mono <;> try assumption

lemma DenoteLiftedScalar_ExtFP2 {A B: VType} (c: Ckt A B 1)
  (x: SOVType 1 A) f (hc: DenoteLiftedScalar c f):
    ExtFP2 c x = FixedAfter2 x := by
  funext m n; simp [ExtFP2]; intro h
  rw [hc]
  apply FixedAfter2_lifted_scalar h

-- The nested External Fixpoint is causal
theorem ExtFP2_causal (c: Ckt A B 1):
    Causal (ExtFP2 c) := by
  intro x1 x2 m hca; funext n
  simp [ExtFP2, FixedAfter2]
  have : x1 m = x2 m := by
    apply hca; rfl
  rw [this]
  have : denote c x1 m = denote c x2 m := by
    have := ckt_causalO c
    apply causalO_is_causal at this
    apply this; tauto
  rw [this]

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
  case loop_lifted c ih =>
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
  case loop_lifted c ih =>
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
    simp [denote, sprodO]; rw [FixedAfter2_sprod2]; tauto
  case loop c ih =>
    intro h; simp at ih
    apply ih at h; clear ih
    simp [ExtFP2] at *
    rw [FixedAfter2_sprod2] at h
    rw [loop_unfold]
    tauto
  case loop_lifted c ih =>
    intro h; simp at ih
    apply ih at h; clear ih
    simp [ExtFP2] at *
    rw [FixedAfter2_sprod2] at h
    rw [loop_lifted_unfold]
    tauto
  case lifting c =>
    intro h; simp [ExtFP2] at *
    apply IntFP1_impl_ExtFP1 at h
    constructor; apply h.1
    simp [denote, FixedAfter2]
    apply h.2

lemma IntFP2_cI (x: OVType 1 A) m:
    IntFP2 cI (↑↑δ0 x) m 1 := by
  simp [cI, IntFP2]
  rw [<- cI, cI_denote]
  rw [integral_lift_comm _ _ delta_linear]
  constructor
  · rw [FixedAfter2_sprod2]
    simp [FixedAfter2]
    constructor; apply δ0_ZeroAfter
    rcases m; simp [FixedAfter1]
    simp; apply δ0_ZeroAfter
  simp [denote, liftO]
  intro k hk; simp
  split_ifs; omega
  simp [delay]; split_ifs; simp
  apply δ0_ZeroAfter; omega

end FPProp2

section TerminateProp
@[simp]
lemma TerminateRow_cI {ns: Bool} {A: VType}{x: SOVType ns A} n:
    TerminateRow cI x n := by
  simp [cI, TerminateRow]

@[simp]
lemma Terminate_cI {ns: Bool} {A: VType}{x: SOVType ns A}:
    Terminate cI x := by
  simp [cI, Terminate]

@[simp]
lemma TerminateRow_cD {ns: Bool} {A: VType}{x: SOVType ns A} n:
    TerminateRow cD x n := by
  simp [cD, TerminateRow]

@[simp]
lemma Terminate_cD {ns: Bool} {A: VType}{x: SOVType ns A}:
    Terminate cD x := by
  simp [cD, Terminate]

end TerminateProp

import DBSP.Circuits.Circuits_v6
import DBSP.Circuits.CktProp
open CktBasic

-- Fixpoint Specification
-- for the outer iteration, i.e. the **1st** time dimension
section FPSpec1
variable {A B C: VType}

def FixedAfter1 {T: Type} (s: stream T) (n: ℕ): Prop :=
  ∀ m ≥ n, s m = s n

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

-- For any circuit, the External Fixpoint is
--   an index `n` of the outer stream such that
--   after `n` both the input and output of the circuit become fixed.
-- For the nested circuit, `n` is a column index,
--   and "fixed" means that the same stream repeats after `n`,
--   not that a single value repeats after `n`.
def ExtFP1 {ns: Bool} (c: Ckt A B ns) (x: SOVType ns A) (n: ℕ): Prop :=
  FixedAfter1 x n ∧ FixedAfter1 (denote c x) n

lemma lifted_Ckt_ExtFP1 {A B: VType} {ns: Bool} (c: Ckt A B ns)
  (x: SOVType ns A) (hc: lifted_Ckt c):
    ExtFP1 c x = FixedAfter1 x := by
  funext n; simp [ExtFP1]; intro h
  rcases hc with ⟨f, hc⟩; rw [hc]
  apply FixedAfter1_lifting h

-- The Internal Fixpoint is an index `n` of the outer stream such that,
--   for any internal circuit,
--   both input and output become fixed after `n`.
-- For nested circuits, this means
--   for any internal circuit,
--   both input and output become a fixed stream after the outer iteration `n`.
def IntFP1 {A B: VType} {ns: Bool} (c: Ckt A B ns) (x: SOVType ns A) (n: ℕ): Prop :=
  match c with
  -- all primitive nodes and convenient constructs
  | Ckt.node1 f => ExtFP1 (Ckt.node1 f) x n
  | Ckt.node2 f => ExtFP1 (Ckt.node2 f) x n
  | Ckt.const k => ExtFP1 (Ckt.const k) x n
  | Ckt.id => ExtFP1 (Ckt.id) x n
  | Ckt.fst => ExtFP1 (Ckt.fst) x n
  | Ckt.snd => ExtFP1 (Ckt.snd) x n
  | Ckt.add => ExtFP1 (Ckt.add) x n
  | Ckt.sub => ExtFP1 (Ckt.sub) x n
  -- sequential and parallel compositions
  | Ckt.seq c1 c2 => IntFP1 c1 x n ∧ IntFP1 c2 (denote c1 x) n
  | Ckt.par c1 c2 => IntFP1 c1 x n ∧ IntFP1 c2 x n
  | Ckt.delay => ExtFP1 Ckt.delay x n
  -- For `c↑ c`, since the internal circuit doesn't have across-iteration states,
  -- thus the Internal Fixpoint is simply the External Fixpoint
  | Ckt.lifting c => ExtFP1 (Ckt.lifting c) x n
  | Ckt.loop c =>  IntFP1 c (sprodO ns (x, z⁻¹ (denote (Ckt.loop c) x))) n
  | Ckt.loop_lifted c => IntFP1 c (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.loop_lifted c) x))) n
  | Ckt.bracket c => IntFP1 c (↑↑δ0 x) n

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

end FPSpec1

-- Fixedpoint checking theory
-- for the inner iteration, i.e. the **2nd** time dimension
section FPSpec2
variable {A B C: VType}
-- FixedAfter2 is like FixedAfter1 but for a row of a nested stream
def FixedAfter2 {T: Type} (s: stream (stream T)) (m n: ℕ): Prop :=
  FixedAfter1 (s m) n

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

-- For nested circuits,
-- the nested External Fixpoint is a point `(m, n)`,
-- such that in row `m`, both the input and output become fixed after column `n`.
def ExtFP2 {A B: VType} (c: Ckt A B 1) (x: SOVType 1 A) (m: ℕ) (n: ℕ): Prop :=
  FixedAfter2 x m n ∧ FixedAfter2 (denote c x) m n

theorem lifted_scalar_Ckt_ExtFP2 {A B: VType} (c: Ckt A B 1)
  (x: SOVType 1 A) (hc: lifted_scalar_Ckt c):
    ExtFP2 c x = FixedAfter2 x := by
  funext m n; simp [ExtFP2]; intro h
  rcases hc with ⟨f, hc⟩; rw [hc]
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

-- For nested circuits,
-- the nested External Fixpoint is a point `(m, n)` such that,
-- in outer iteration `m`, for any internal circuit,
-- both the input and output become fixed after inner iteration `n`.
def IntFP2 {A B: VType} (c: Ckt A B 1) (x: SOVType 1 A) (m n: ℕ): Prop :=
  match c with
  | Ckt.node1 f => ExtFP2 (Ckt.node1 f) x m n
  | Ckt.node2 f => ExtFP2 (Ckt.node2 f) x m n
  | Ckt.const k => ExtFP2 (Ckt.const k) x m n
  | Ckt.id => ExtFP2 (Ckt.id) x m n
  | Ckt.fst => ExtFP2 (Ckt.fst) x m n
  | Ckt.snd => ExtFP2 (Ckt.snd) x m n
  | Ckt.add => ExtFP2 (Ckt.add) x m n
  | Ckt.sub => ExtFP2 (Ckt.sub) x m n
  | Ckt.seq c1 c2 => let o := denote c1 x
       IntFP2 c1 x m n ∧ IntFP2 c2 o m n
  | Ckt.par c1 c2 => IntFP2 c1 x m n ∧ IntFP2 c2 x m n
  | Ckt.delay => ExtFP2 Ckt.delay x m n
  -- This is where `IntFP2` depends on `IntFP1`
  -- For `c↑ c`, the nested Internal Fixpoint is `(m, n)` means that
  -- the Internal Fixpoint of `c` on input `x m` is `n`
  | Ckt.lifting c => IntFP1 c (x m) n
  | Ckt.loop c =>  IntFP2 c (sprod2 (x, z⁻¹ (denote (Ckt.loop c) x))) m n
  | Ckt.loop_lifted c => IntFP2 c (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.loop_lifted c) x))) m n

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

-- The vectorized version of IntFP2
def IntFP2V (c: Ckt A B 1) (x: SOVType 1 A) (b: stream ℕ): Prop :=
  ∀ i, IntFP2 c x i (b i)

-- `terminate c x` means that circuit `c` terminates on any finite segment of input `x`
--  you can also call it "streaming progress"
def terminate {ns: Bool} {A B: VType} (c: Ckt A B ns) (x: SOVType ns A): Prop :=
  match c with
  -- the core definition
  | Ckt.bracket c => terminate c (↑↑δ0 x) ∧ ∃ b, IntFP2V c (↑↑δ0 x) b
  -- other structural constructs
  | Ckt.seq c1 c2 => terminate c1 x ∧ terminate c2 (denote c1 x)
  | Ckt.par c1 c2 => terminate c1 x ∧ terminate c2 x
  | Ckt.lifting c => ∀ i, terminate c (x i)
  | Ckt.loop c =>  terminate c (sprodO ns (x, z⁻¹ (denote (Ckt.loop c) x)))
  | Ckt.loop_lifted c => terminate c (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.loop_lifted c) x)))
  -- all other primitive nodes are terminating
  | _ => true

end FPSpec2

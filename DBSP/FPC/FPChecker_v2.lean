import DBSP.Circuits.Circuits_v5
import DBSP.StreamTheory.Linear
import DBSP.Logic.SProp
open CktBasic

-- Fixedpoint checking theory
-- for the outer iteration, i.e. the **1st** time dimension
section FPChecker1
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

-- For any circuit, the external fixedpoint is
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

-- The internal fixedpoint is an index `n` of the outer stream such that,
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
  -- thus the internal fixedpoint is simply the external fixedpoint
  | Ckt.lifting c => ExtFP1 (Ckt.lifting c) x n
  | Ckt.loop c =>  IntFP1 c (sprodO ns (x, z⁻¹ (denote (Ckt.loop c) x))) n
  | Ckt.loop_lifted c => IntFP1 c (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.loop_lifted c) x))) n
  | Ckt.bracket c => IntFP1 c (↑↑δ0 x) n

-- The internal fixedpoint implies the external fixedpoint
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

-- `let_fixed1 s n` is the stream acquired by
--  letting `s` be fixed after `n`
def let_fixed1 {T: Type} (s: stream T) (n: ℕ) : stream T :=
    fun i => if i < n then s i else s n

lemma agree_let_fixed1 {T: Type} (s: stream T) (n: ℕ):
   (let_fixed1 s n) =[n]= s   := by
  intro i hi; simp [let_fixed1]; intro
  have : n = i := by omega
  simp [this]

lemma FixedAfter1_let_fixed1 {T: Type} (s: stream T) (n: ℕ):
    FixedAfter1 (let_fixed1 s n) n := by
  intro m hm; simp [let_fixed1]; omega

lemma let_fixed1_eq_iff {T: Type} (s: stream T) (n: ℕ):
    (let_fixed1 s n) = s <-> FixedAfter1 s n := by
  constructor
  · intro h; rw [<- h]; apply FixedAfter1_let_fixed1
  · intro h
    funext n; simp [let_fixed1]
    intro hn; rw [<- h]; omega

-- `let_fixed1` is idempotent
lemma let_fixed1_idem {T: Type} (s: stream T) (n: ℕ):
    let_fixed1 (let_fixed1 s n) n = let_fixed1 s n := by
  funext; simp [let_fixed1]; omega

-- `let_fixed1` is causal
lemma let_fixed1_causal {T: Type}:
    Causal (@let_fixed1 T) := by
  intro x1 x2 n h; funext i; simp [let_fixed1]
  split_ifs <;> apply h <;> omega

@[simp]
lemma let_fixed1_delay_0 {T: Type} [Zero T] (s: stream T):
    let_fixed1 (z⁻¹ s) 0 = 0 := by
  funext i; simp [let_fixed1, delay]

@[simp]
lemma let_fixed1_delay_succ {T: Type} [Zero T] (s: stream T) (n: ℕ):
    let_fixed1 (z⁻¹ s) (n+1) = z⁻¹ (let_fixed1 s n) := by
  funext i; simp [let_fixed1, delay]
  split_ifs with hi <;> (try simp) <;> omega

lemma let_fixed1_sprod2 {A B: Type}
  (s1: stream (stream A)) (s2: stream (stream B)) (n: ℕ):
    let_fixed1 (sprod2 (s1, s2)) n =
    sprod2 (let_fixed1 s1 n, let_fixed1 s2 n) := by
  funext i j; simp [let_fixed1, sprod2]
  split_ifs <;> simp

lemma let_fixed1_sprodO {A B: Type} {ns: Bool}
  (s1: SOType ns A) (s2: SOType ns B) (n: ℕ):
    let_fixed1 (sprodO ns (s1, s2)) n =
    sprodO ns (let_fixed1 s1 n, let_fixed1 s2 n) := by
  rcases ns <;> simp [sprodO]
  · funext i; simp [let_fixed1, sprod]
    split_ifs <;> simp
  · apply let_fixed1_sprod2

lemma let_fixed1_causal_f_agree {A B: Type}
  (f: Operator A B) (hc: Causal f) (s: stream A) (n: ℕ):
    f s =[n]= f (let_fixed1 s n) := by
  rw [causal_to_agree] at hc
  apply hc; symm; apply agree_let_fixed1

lemma let_fixed1_denote_agree {A B: VType} {ns: Bool}
  (c: Ckt A B ns) (x: SOVType ns A) (n: ℕ):
    denote c x =[n]= denote c (let_fixed1 x n) := by
  have hc := ckt_causal c
  apply let_fixed1_causal_f_agree; tauto

  -- A state fixedpoint is an index `n` such that:
  --  if after the outer iteration `n`, the input becomes fixed,
  --  then `n` will also be an internal fixedpoint.
  -- It's called the state fixedpoint because
  --   the state of the circuit after `n` is determined by the input up to `n`.
  def StFP1 {A B: VType} {ns: Bool} (c: Ckt A B ns) (x: SOVType ns A) (n: ℕ): Prop :=
    IntFP1 c (let_fixed1 x n) n

-- The internal fixedpoint is equivalent to
-- the state fixedpoint with the input being fixed after `n`
theorem IntFP1_StFP1 {A B: VType} {ns: Bool} (c: Ckt A B ns)
  (x: SOVType ns A):
    IntFP1 c x = SAnd (FixedAfter1 x) (StFP1 c x) := by
  funext n; simp
  simp [StFP1]; constructor
  · intro hi
    have he := IntFP1_impl_ExtFP1 c x n hi
    rcases he with ⟨h1, h2⟩
    constructor; tauto
    rw [<- let_fixed1_eq_iff] at h1
    rw [h1]; tauto
  · rintro ⟨h1, h2⟩
    rw [<- let_fixed1_eq_iff] at h1
    rw [<- h1]; tauto

theorem StFP1_IntFP1 {A B: VType} {ns: Bool} {c: Ckt A B ns}
  {x: SOVType ns A} {n: ℕ}
  (hf: FixedAfter1 x n) (hs: StFP1 c x n):
    IntFP1 c x n := by
  rw [IntFP1_StFP1]; simp; tauto

-- The state fixedpoint of a circuit on input `x`
-- is equivalent to that on input `let_fixed1 p x`
theorem StFP1_let_fixed1_eq {A B: VType} {ns: Bool} (c: Ckt A B ns)
  (x: SOVType ns A) (n: ℕ):
    StFP1 c (let_fixed1 x n) n <-> StFP1 c x n := by
  simp [StFP1]; rw [let_fixed1_idem]

theorem StFP1_causal {A B: VType} {ns: Bool} (c: Ckt A B ns):
    Causal (StFP1 c):= by
  intro x1 x2 i hca; simp [StFP1]
  have : let_fixed1 x1 i = let_fixed1 x2 i := by
    apply let_fixed1_causal
    intro j hj; apply hca; omega
  rw [this]

-- An equivalent definition of `StFP1`
theorem StFP1_iff {A B: VType} {ns: Bool}
  {c: Ckt A B ns} {x: SOVType ns A} {n: ℕ}:
    StFP1 c x n <->
    ∀ (y: SOVType ns A), (y =[n]= x) -> FixedAfter1 y n -> IntFP1 c y n := by
  constructor
  · intro h y hag hf
    rw [IntFP1_StFP1]; simp
    constructor; tauto
    rw [StFP1_causal] <;> tauto
  · intro h
    simp [StFP1]
    apply h; apply agree_let_fixed1
    apply FixedAfter1_let_fixed1

-- A high-level specification of the outer-iteration fixedpoint checker
-- the idea is to check the state fixedpoint `StFP1` at runtime.
-- For nested-circuits, this is run at the end of each outer iteration.
noncomputable def FPChecker1 {A B: VType} {ns: Bool} (c: Ckt A B ns) (x: SOVType ns A): stream Prop :=
  match c with
  -- all primitive nodes and convenient constructs
  | Ckt.node1 f => STrue
  | Ckt.node2 f => STrue
  | Ckt.const k => STrue
  | Ckt.id => STrue
  | Ckt.fst => STrue
  | Ckt.snd => STrue
  | Ckt.add => STrue
  | Ckt.sub => STrue
  -- sequential and parallel compositions
  | Ckt.seq c1 c2 => SAnd (FPChecker1 c1 x) (FPChecker1 c2 (denote c1 x))
  | Ckt.par c1 c2 => SAnd (FPChecker1 c1 x) (FPChecker1 c2 x)
  -- checks whether the input is equal to the stored state (the last input)
  -- for non-nested delay, it's a single value
  -- for nested delay, it's a list
  | Ckt.delay => fun n => x n = (z⁻¹ x) n
  -- For `c↑ c`, returns true since it has no states across outer iterations
  | Ckt.lifting c => STrue
  -- The checking for loop is similar to that of delay, but more complicated
  -- it checks the internal circuit
  -- and also whether the output is equal to the stored state (i.e. the delayed output)
  | Ckt.loop c =>
    fun n => let o := denote (Ckt.loop c) x
      FPChecker1 c (sprodO ns (x, z⁻¹ o)) n ∧ o n = (z⁻¹ o) n
  -- The lifted_loop itself has no states across outer iterations
  -- but the internal circuit may have states across outer iterations
  -- so we need to check the internal circuit
  | Ckt.loop_lifted c => fun n => let o := denote (Ckt.loop_lifted c) x
      FPChecker1 c (sprod2 (x, ↑↑z⁻¹ o)) n
  -- We need to check the internal circuit
  -- for the same reason as loop_lifted
  | Ckt.bracket c => fun n => FPChecker1 c (↑↑δ0 x) n

lemma ExtFP1_lifted_Ckt_let_fixed1 {A B: VType} {ns: Bool}
  (c: Ckt A B ns) (x: SOVType ns A) (n: ℕ) (hc: lifted_Ckt c):
    ExtFP1 c (let_fixed1 x n) n := by
  have h1 := FixedAfter1_let_fixed1 x n
  have h2 := lifted_Ckt_ExtFP1 c (let_fixed1 x n) hc
  rw [h2]; tauto

lemma loop_FixedAfter1_ind {A B: VType} {ns: Bool}
  (c: Ckt (A ×ᵥB) B ns) (x: SOVType ns A) (n: ℕ)
  (hf: FixedAfter1 (denote c (sprodO ns (x, let_fixed1 (z⁻¹ (denote (cloop c) x)) n))) n)
  (heq: denote (cloop c) x n = z⁻¹ (denote (cloop c) x) n):
    FixedAfter1 (z⁻¹ (denote (cloop c) x)) n := by
  suffices: z⁻¹ (denote (cloop c) x) = let_fixed1 (z⁻¹ (denote (cloop c) x)) n
  · rw [this]; apply FixedAfter1_let_fixed1
  rw [agree_everywhere_eq]
  intro m; induction' m with m ih
  · intro i hi
    have : i = 0 := by omega
    subst this; simp [let_fixed1]
    intro hn; subst hn; simp
  by_cases hm: (m ≤ n)
  · apply agreeUpto_extend; tauto
    simp [let_fixed1]
    intros; rw [<- heq]
    by_cases h:(m = n)
    subst h; tauto
    have : n = m + 1 := by omega
    subst this; simp at heq; tauto
  apply agreeUpto_extend; tauto
  simp [let_fixed1]; intros
  specialize hf m (by omega)
  rw [loop_unfold]
  calc
    _ = denote c (sprodO ns (x, let_fixed1 (z⁻¹ (denote (cloop c) x)) n)) m := by
      apply ckt_causal
      rw [sprodO_causal]
      tauto
    _ = _ := hf
    _ = denote c (sprodO ns (x, z⁻¹ (denote (cloop c) x))) n:= by
      apply ckt_causal
      rw [sprodO_causal]
      constructor; rfl
      apply agree_let_fixed1
    _ = _ := by
      rw [<- loop_unfold]; tauto

lemma loop_FPChecker1_correct {A B: VType} {ns: Bool}
  (c: Ckt (A ×ᵥB) B ns) (x: SOVType ns A) (n: ℕ):
    StFP1 c (sprodO ns (x, z⁻¹ (denote (cloop c) x))) n ∧
    denote (cloop c) x n = z⁻¹ (denote (cloop c) x) n <->
    IntFP1 c (sprodO ns (let_fixed1 x n, z⁻¹ (denote (cloop c) (let_fixed1 x n)))) n := by
  rw [StFP1, let_fixed1_sprodO]
  nth_rw 2 [let_fixed1_causal]
  case a =>
    apply causal_respects_agreeUpto; apply delay_causal
    apply causal_respects_agreeUpto; apply ckt_causal
    symm; apply agree_let_fixed1
  constructor; swap
  -- This direction is easier
  · intro hi
    have he := IntFP1_impl_ExtFP1 _ _ _ hi
    rcases he with ⟨he, _⟩
    rw [FixedAfter1_sprodO] at he
    rcases he with ⟨_, he⟩
    constructor
    · rw [<- let_fixed1_eq_iff] at he
      rw [he]; tauto
    specialize he (n+1) (by omega)
    simp at he
    rw [ckt_causal]; rw [he]
    rcases n <;> simp
    rw [ckt_causal]
    apply agreeUpto_weaken; apply agree_let_fixed1
    omega; symm; apply agree_let_fixed1
  -- This direction is harder
  rintro ⟨hi, heq⟩
  suffices hf:
    FixedAfter1 (z⁻¹ (denote (cloop c) (let_fixed1 x n))) n
  · rw [<- let_fixed1_eq_iff] at hf
    rw [<- hf]; tauto
  apply IntFP1_impl_ExtFP1 at hi
  rcases hi with ⟨_, hf⟩
  have heq := by calc
    denote (cloop c) (let_fixed1 x n) n = denote (cloop c) x n := by
      apply ckt_causal; apply agree_let_fixed1
    _ = _ := heq
    _ = z⁻¹ (denote (cloop c) (let_fixed1 x n)) n := by
      rcases n <;> simp
      apply ckt_causal
      apply agreeUpto_weaken
      symm; apply agree_let_fixed1; omega
  set y := let_fixed1 x n
  apply loop_FixedAfter1_ind <;> tauto

-- The proof is similar to `loop_FixedAfter1_ind`
-- but needs induction on both two dimensions
lemma loop_lifted_FixedAfter1_ind {A B: VType}
  (c: Ckt (A ×ᵥB) B 1) (x: SOVType 1 A) (n: ℕ)
  (hf: FixedAfter1 (denote c (sprod2 (x, let_fixed1 (↑↑z⁻¹ (denote (cloop2 c) x)) n))) n):
    FixedAfter1 (↑↑z⁻¹ (denote (cloop2 c) x)) n := by
  suffices: ↑↑z⁻¹ (denote (cloop2 c) x) = let_fixed1 (↑↑z⁻¹ (denote (cloop2 c) x)) n
  · rw [this]; apply FixedAfter1_let_fixed1
  rw [agree_everywhere_eq]
  intro m; induction' m with m ih
  · intro i hi
    have : i = 0 := by omega
    subst this; simp [let_fixed1]
    intro hn; subst hn; simp
  apply agreeUpto_extend; tauto
  by_cases hm: (m + 1 < n)
  · simp [let_fixed1]
    intros; omega
  simp [let_fixed1, -lifting_eq]; intros
  by_cases hm: (m + 1 = n)
  · subst hm; simp
  specialize hf (m+1) (by omega)
  rw [agree_everywhere_eq]
  intro k; induction' k with k ihk
  · intro i hi
    have : i = 0 := by omega
    subst this; simp
  apply agreeUpto_extend; tauto
  simp
  rw [loop_lifted_unfold]
  have hca2 := ckt_causalO c; simp [CausalO] at hca2
  calc
    _ = denote c (sprod2 (x, let_fixed1 (↑↑z⁻¹ (denote (cloop2 c) x)) n)) (m+1) k := by
      apply hca2
      intro a ha b hb
      by_cases (a ≤ m)
      · specialize ih a (by omega)
        simp at ih ⊢
        rw [ih]
      have : a = m + 1 := by omega
      subst a
      specialize ihk b (by omega)
      simp at ihk ⊢
      simp [let_fixed1, *]
    _ = _ := by rw [hf]
    _ = _ := by
      apply congr; swap; simp
      apply ckt_causal
      rw [sprod2_causal]
      constructor; rfl
      apply agree_let_fixed1

-- This proof is similar to `loop_FPChecker1_correct`, but simpler
lemma loop_lifted_FPChecker1_correct {A B: VType} (c: Ckt (A ×ᵥB) B 1)
  (x: SOVType 1 A) (n: ℕ):
    IntFP1 c (sprod2 (let_fixed1 x n, let_fixed1 (↑↑z⁻¹ (denote (cloop2 c) x)) n)) n <->
    IntFP1 c (sprod2 (let_fixed1 x n, ↑↑z⁻¹ (denote (cloop2 c) (let_fixed1 x n)))) n := by
  nth_rw 2 [let_fixed1_causal]
  case a =>
    apply causal_respects_agreeUpto; apply lifting_causal
    apply causal_respects_agreeUpto; apply ckt_causal
    symm; apply agree_let_fixed1
  constructor; swap
  -- This direction is easier
  · intro hi
    have he := IntFP1_impl_ExtFP1 _ _ _ hi
    rcases he with ⟨he, _⟩
    rw [FixedAfter1_sprod2] at he
    rcases he with ⟨_, he⟩
    rw [<- let_fixed1_eq_iff] at he
    rw [he]; tauto
  -- This direction is harder
  intro hi
  suffices hf:
    FixedAfter1 (↑↑z⁻¹ (denote (cloop2 c) (let_fixed1 x n))) n
  · rw [<- let_fixed1_eq_iff] at hf
    rw [<- hf]; tauto
  apply IntFP1_impl_ExtFP1 at hi
  rcases hi with ⟨_, hf⟩
  apply loop_lifted_FixedAfter1_ind; tauto

-- The corrrectness of `FPChecker1`
-- It is sound and complete w.r.t. `StFP1`
theorem FPChecker1_correct {A B: VType} {ns: Bool} (c: Ckt A B ns)
  (x: SOVType ns A):
    FPChecker1 c x = StFP1 c x := by
  funext n; simp; revert x; induction c <;>
  intro x <;> simp [FPChecker1, StFP1, IntFP1] <;>
  -- base cases are trivial since they are lifted functions
  (try  apply ExtFP1_lifted_Ckt_let_fixed1) <;>
  (try unfold lifted_Ckt; simp [lifted_Ckt, denote, liftO]) <;>
  (try tauto) <;>
  (try rename Bool => ns; rcases ns <;> simp <;> tauto)
  case seq c1 c2 ih1 ih2 =>
    simp at ih1 ih2
    rw [ih1, ih2]
    simp [StFP1]
    intro h
    apply IntFP1_impl_ExtFP1 at h
    rw [iff_eq_eq]; apply congr
    apply congr; rfl; swap; rfl
    funext i; simp [let_fixed1]
    split_ifs
    apply ckt_causal
    apply agreeUpto_weaken
    symm; apply agree_let_fixed1; omega
    rw [ckt_causal]
    case neg.a =>
      symm; apply agree_let_fixed1
    symm; apply h.2; omega
  case par c1 c2 ih1 ih2 =>
    simp at ih1 ih2
    rw [ih1, ih2]
    simp [StFP1]
  case delay =>
    simp [ExtFP1]
    have hf := FixedAfter1_let_fixed1 x n
    simp [hf, denote]
    rw [<- FixedAfter1_extend]
    rw [FixedAfter1_delay_succ]; simp [hf]
    rcases n <;> simp [let_fixed1] <;> tauto
  case loop ns _ _ c ih =>
    rw [ih]; apply loop_FPChecker1_correct
  case loop_lifted c ih =>
    rw [ih, StFP1]
    rw [let_fixed1_sprod2]
    apply loop_lifted_FPChecker1_correct
  case bracket c ih =>
    rw [ih, StFP1]
    rw [iff_eq_eq]; congr
    funext i j
    by_cases hi:(i < n)
    · simp [hi, let_fixed1]
    by_cases hj:(j = 0)
    · simp [hj, hi, let_fixed1]
    simp [hi, hj, let_fixed1]

end FPChecker1


-- Fixedpoint checking theory
-- for the inner iteration, i.e. the **2nd** time dimension
section FPChecker2
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
-- the nested external fixedpoint is a point `(m, n)`,
-- such that in row `m`, both the input and output become fixed after column `n`.
def ExtFP2 {A B: VType} (c: Ckt A B 1) (x: SOVType 1 A) (m: ℕ) (n: ℕ): Prop :=
  FixedAfter2 x m n ∧ FixedAfter2 (denote c x) m n

theorem lifted_scalar_Ckt_ExtFP2 {A B: VType} (c: Ckt A B 1)
  (x: SOVType 1 A) (hc: lifted_scalar_Ckt c):
    ExtFP2 c x = FixedAfter2 x := by
  funext m n; simp [ExtFP2]; intro h
  rcases hc with ⟨f, hc⟩; rw [hc]
  apply FixedAfter2_lifted_scalar h

-- The nested external fixedpoint is causal
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
-- the nested external fixedpoint is a point `(m, n)` such that,
-- in outer iteration `m`, for any internal circuit,
-- both the input and output become fixed after inner iteration `n`.
def IntFP2 {A B: VType} (c: Ckt A B 1) (x: SOVType 1 A) (m n: ℕ): Prop :=
  match c with
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
  -- For `c↑ c`, the nested internal fixedpoint is `(m, n)` means that
  -- the internal fixedpoint of `c` on input `x m` is `n`
  | Ckt.lifting c => IntFP1 c (x m) n
  | Ckt.loop c =>  IntFP2 c (sprod2 (x, z⁻¹ (denote (Ckt.loop c) x))) m n
  | Ckt.loop_lifted c => IntFP2 c (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.loop_lifted c) x))) m n

-- The nested internal fixedpoint is causal
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

-- The nested internal fixedpoint implies the nested external fixedpoint
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

-- Total order on time points
-- essentially dictionary order on (m, n)
def le_time (p1 p2: ℕ × ℕ) : Prop :=
  p1.1 < p2.1 ∨ (p1.1 = p2.1 ∧ p1.2 ≤ p2.2)
notation:40  p1 " ≤ₜ " p2 => le_time p1 p2

@[refl]
lemma le_time_refl (p: ℕ × ℕ):
    p ≤ₜ p := by
  simp [le_time]

@[trans]
lemma le_time_trans {p1 p2 p3: ℕ × ℕ}
  (h1: p1 ≤ₜ p2) (h2: p2 ≤ₜ p3):
    p1 ≤ₜ p3 := by
  simp [le_time] at h1 h2 ⊢
  rcases h1 with (h1 | ⟨h1, h1'⟩)
  · rcases h2 with (h2 | ⟨h2, h2'⟩)
    · left; omega
    · left; omega
  · rcases h2 with (h2 | ⟨h2, h2'⟩)
    · left; omega
    · right; constructor <;> omega

-- For nested streams `s1` and `s2`,
-- `agreeT s1 s2 m n` means that
--  `s1` and `s2` are equal up to the moment (position) `(m, n)`
def agreeT {T: Type} (m n: ℕ)(s1 s2: SOType 1 T) : Prop :=
  ∀ m' n', ((m', n') ≤ₜ (m, n)) -> s1 m' n' = s2 m' n'

notation:35 s1 " ={ " m ", " n " }= " s2 => agreeT m n s1 s2

-- `agreeT` is an equivalence relation
@[refl]
lemma agreeT_refl {T: Type}
  (m n: ℕ) (s: SOType 1 T) :
    s ={m, n}= s := by
  intro _ _ _; rfl

@[symm]
lemma agreeT_symm {T: Type}
  {m n: ℕ} {s1 s2: SOType 1 T} :
    (s1 ={m, n}= s2) -> s2 ={m, n}= s1 := by
  intro h; simp [agreeT] at h ⊢
  intro _ _ _; symm; tauto

@[trans]
lemma agreeT_trans {T: Type}
  {m n: ℕ} {s1 s2 s3: SOType 1 T} :
    (s1 ={m, n}= s2) -> (s2 ={m, n}= s3) -> (s1 ={m, n}= s3) := by
  intros h1 h2; simp [agreeT] at h1 h2 ⊢
  intro i j h
  rw [h1, h2] <;> tauto

lemma agreeT_imply_AgreeNested {T: Type}
  {m n m' n': ℕ} {s1 s2: stream (stream T)}
  (hs: s1 ={m, n}= s2) (hmn: (m' ,n') ≤ₜ (m, n)):
   AgreeNested m' n' s1 s2 := by
  intro i hi j hj
  apply hs; trans; swap; tauto
  simp [le_time]; omega

lemma delay_agreeT_0  {T: Type} [Zero T]
  {n: ℕ} {s1 s2: SOType 1 T}:
    ((z⁻¹ s1) ={0, n}= (z⁻¹ s2)) := by
  intro i j h
  simp [le_time] at h
  rcases h with ⟨hi, _⟩; subst hi
  simp

lemma delay_agreeT_succ  {T: Type} [Zero T]
  {m n: ℕ} {s1 s2: SOType 1 T}:
    ((z⁻¹ s1) ={m+1, n}= (z⁻¹ s2)) <-> s1 ={m, n}= s2 := by
  constructor <;> intro h i j ht
  · specialize h (i+1) j; simp at h
    apply h; revert ht; simp [le_time]
  · rcases i with _ | i; simp
    simp; apply h
    revert ht; simp [le_time]

lemma agree_to_agreeT {T: Type}
  {m n: ℕ} {s1 s2: SOType 1 T}
  (h: s1 =[m]= s2):
    s1 ={m, n}= s2 := by
  intro i j hle
  rw [h]; simp [le_time] at hle; omega

lemma agreeT_0_iff {T: Type}
   {n: ℕ} {s1 s2: SOType 1 T}:
    (s1 ={0, n}= s2) <-> s1 0 =[n]= s2 0 := by
  constructor
  · intro h i hi; apply h; simp [le_time]; omega
  · intro h i j ht
    simp [le_time] at ht
    rcases ht with ⟨hi, _⟩; subst hi
    apply h; tauto

lemma agreeT_succ_iff {T: Type}
  {m n: ℕ} {s1 s2: SOType 1 T}:
  (s1 ={m+1, n}= s2) <-> (s1 =[m]= s2) ∧ s1 (m+1) =[n]= s2 (m+1) := by
  constructor
  · intro h; constructor
    · intro i hi; funext j; apply h; simp [le_time]; omega
    · intro i hi; apply h; simp [le_time]; omega
  · rintro ⟨h1, h2⟩ i j ht
    simp [le_time] at ht
    cases' ht with ht ht
    · rw [h1]; omega
    · rcases ht with ⟨hi, ht⟩
      subst hi; apply h2
      tauto

lemma agreeT_sprod2 {A B: Type} [Zero A] [Zero B]
  {m n: ℕ} {s1 s2: stream (stream A)} {t1 t2: stream (stream B)}:
    ((sprod2 (s1, t1)) ={m, n}= (sprod2 (s2, t2))) <->
    (s1 ={m, n}= s2) ∧ (t1 ={m, n}= t2) := by
  constructor
  · intro h; constructor <;> intro i j hle
    · specialize h i j hle; simp [sprod2] at h; tauto
    · specialize h i j hle; simp [sprod2] at h; tauto
  · rintro ⟨h1, h2⟩ i j hle
    simp [sprod2]
    constructor
    · apply h1; tauto
    · apply h2; tauto

-- The concept of "causal" w.r.t. time, i.e. `le_time`
def CausalT {A B: Type} (f: Operator (stream A) (stream B)) : Prop :=
  ∀ (s1 s2: SOType 1 A) (m n: ℕ),
    (s1 ={m, n}= s2) -> f s1 m n = f s2 m n

theorem causalT_agreeT {A B: Type}
  (f: Operator (stream A) (stream B)) (hc: CausalT f)
  {s1 s2: SOType 1 A} {m n: ℕ}
  (h: s1 ={m, n}= s2):
    f s1 ={m, n}= f s2 := by
  intro i j hle
  apply hc
  intro a b hab; apply h
  trans <;> tauto

theorem causalNested_to_causalT {A B: Type}
  (f: Operator (stream A) (stream B)) (hc: CausalNested f):
    CausalT f := by
  intro s1 s2 m n h
  apply hc; apply agreeT_imply_AgreeNested; tauto; rfl

lemma strict_to_causalT {A B: Type}
  (f: Operator (stream A) (stream B)) (hs: Strict f):
    CausalT f := by
  intro s1 s2 m n h
  rw [hs]
  intro i hi; funext j
  apply h; simp [le_time]; omega

theorem ckt_causalT {A B: VType} (c: Ckt A B 1):
    CausalT (denote c) := by
  apply causalNested_to_causalT
  have := ckt_causalO c
  apply this

lemma delay_causalT {T: Type} [Zero T]:
    CausalT (z⁻¹ : Operator (stream T) (stream T)) := by
  apply strict_to_causalT
  apply delay_strict

lemma lifting_causalT {A B: Type}
  (f: Operator A B) (hf: Causal f):
    CausalT (↑↑ f) := by
  intro s1 s2 m n h
  simp; rw [hf]
  rcases m
  rw [agreeT_0_iff] at h; tauto
  rw [agreeT_succ_iff] at h; tauto

-- For nested streams `s`,
-- `let_fixed2 s m n` is the nested stream acquired by
--  letting the row `m` of `s` be fixed after column `n`
def let_fixed2 {T: Type} (s: stream (stream T)) (m n: ℕ) :
    stream (stream T) :=
 fun i j =>
    if i != m then s i j
    else if j < n then s m j
    else s m n

lemma agreeT_let_fixed2 {T: Type}
  (s: stream (stream T)) (m n: ℕ):
    s ={m, n}= let_fixed2 s m n  := by
  simp [agreeT]
  intro i j h
  simp [let_fixed2]
  intro hi; subst hi
  simp [h]; intro hn
  cases h; omega
  have : j = n := by omega
  simp [this]

-- `let_fixed2` is causal in some sense
theorem let_fixed2_causal {T: Type}
  (s1 s2: stream (stream T)) (m n: ℕ)
  (hca: s1 ={m, n}= s2):
    let_fixed2 s1 m n =[m]= let_fixed2 s2 m n := by
  intro i hi; funext j; simp [let_fixed2]
  split_ifs with hi' <;> apply hca <;> simp [le_time] <;> omega

lemma FixedAfter2_let_fixed2 {T: Type}
  (s: stream (stream T)) (m n: ℕ):
    FixedAfter2 (let_fixed2 s m n) m n := by
  simp [FixedAfter2]; intro i hi
  simp [let_fixed2]; intros; omega

lemma let_fixed2_eq_iff {T: Type}
  (s: stream (stream T)) (m n: ℕ):
    (let_fixed2 s m n) = s <-> FixedAfter2 s m n := by
  constructor
  · intro h; rw [<- h]; apply FixedAfter2_let_fixed2
  · intro h
    funext i j; simp [let_fixed2]
    by_cases hi: (i = m)
    · subst hi; simp
      by_cases hj: (j < n)
      · simp [hj]
      · intro; rw [<- h]; omega
    · simp [hi]

-- `let_fixed2` is idempotent
lemma let_fixed2_idem {T: Type}
  (s: stream (stream T)) (m n: ℕ):
    let_fixed2 (let_fixed2 s m n) m n = let_fixed2 s m n := by
  funext i j; simp [let_fixed2]
  intro h; subst h; simp
  omega

lemma let_fixed2_row_m {T: Type}
  (s: stream (stream T)) (m n: ℕ):
    (let_fixed2 s m n) m = let_fixed1 (s m) n := by
  funext j; simp [let_fixed2, let_fixed1]

lemma let_fixed2_sprod2 {A B: Type}
  (s1: stream (stream A)) (s2: stream (stream B)) (m n: ℕ):
    let_fixed2 (sprod2 (s1, s2)) m n =
    sprod2 (let_fixed2 s1 m n, let_fixed2 s2 m n) := by
  funext i j; simp [let_fixed2, sprod2]
  split_ifs <;> simp

-- Nested version of `StFP1`
-- A nested state fixedpoint is a point `(m, n)` such that:
--  if the input becomes fixed after `(m, n)`,
--  then `(m, n)` will also be a nested internal fixedpoint.
def StFP2 {A B: VType} (c: Ckt A B 1) (x: SOVType 1 A) (m n: ℕ): Prop :=
  IntFP2 c (let_fixed2 x m n) m n

-- The nested internal fixedpoint is equivalent to
-- the nested state fixedpoint with the input being fixed after `(m, n)`
theorem IntFP2_StFP2 {A B: VType} (c: Ckt A B 1)
  (x: SOVType 1 A) :
    IntFP2 c x = SAnd2 (FixedAfter2 x) (StFP2 c x) := by
  funext m n; simp
  simp [StFP2]; constructor
  · intro hi
    have he := IntFP2_impl_ExtFP2 c x m n hi
    rcases he with ⟨h1, h2⟩
    constructor; tauto
    rw [<- let_fixed2_eq_iff] at h1
    rw [h1]; tauto
  · rintro ⟨h1, h2⟩
    rw [<- let_fixed2_eq_iff] at h1
    rw [<- h1]; tauto

-- The nested state fixedpoint of a circuit on input `x`
-- is equivalent to that on input `let_fixed2 m n x`
theorem StFP2_let_fixed1_eq {A B: VType} (c: Ckt A B 1)
  (x: SOVType 1 A) (m n: ℕ):
    StFP2 c (let_fixed2 x m n) m n <-> StFP2 c x m n := by
  simp [StFP2]; rw [let_fixed2_idem]

-- The nested state fixedpoint is CausalT
theorem StFP2_CausalT {A B: VType} (c: Ckt A B 1):
    CausalT (StFP2 c) := by
  intro x1 x2 m n hca
  simp [StFP2]; rw [iff_eq_eq]
  rw [IntFP2_causal]
  apply let_fixed2_causal; tauto

theorem StFP2_iff {A B: VType}
  {c: Ckt A B 1} {x: SOVType 1 A} {m n: ℕ}:
    StFP2 c x m n <->
    ∀ (y: SOVType 1 A), (y ={m, n}= x) -> FixedAfter2 y m n -> IntFP2 c y m n := by
  constructor
  · intro h y hag hf
    rw [IntFP2_StFP2]; simp
    constructor; tauto
    rw [StFP2_CausalT] <;> tauto
  · intro h
    simp [StFP2]
    apply h; symm; apply agreeT_let_fixed2
    apply FixedAfter2_let_fixed2

-- A high-level specification of the inner-level fixedpoint checker
-- the idea is to check the nested state fixedpoint `StFP2` at runtime:
noncomputable def FPChecker2 {A B: VType} (c: Ckt A B 1) (x: SOVType 1 A): stream (stream Prop) :=
  match c with
  -- primitive nodes and convenient constructs
  | Ckt.id => STrue2
  | Ckt.fst => STrue2
  | Ckt.snd => STrue2
  | Ckt.add => STrue2
  | Ckt.sub => STrue2
  -- sequential and parallel composition
  | Ckt.seq c1 c2 => SAnd2 (FPChecker2 c1 x) (FPChecker2 c2 (denote c1 x))
  | Ckt.par c1 c2 => SAnd2 (FPChecker2 c1 x) (FPChecker2 c2 x)
  -- Nested delay needs to check whether the input from last row has reached the fixedpoint
  -- which is assumed to be stored in the state at the end of last outer iteration
  | Ckt.delay => fun m n => FixedAfter2 (z⁻¹ x) m n
  -- This is where `FPChecker2` depends on `FPChecker1`
  -- `c↑ c` checks the `StFP1` of the inner circuit `c`
  | Ckt.lifting c => fun m n => FPChecker1 c (x m) n
  -- The checking for loop is similar to that of delay, but more complicated
  -- it checks the internal circuit
  -- and also whether the output from last row has reached fixedpoint
  | Ckt.loop c => fun m n => let o := denote (Ckt.loop c) x
      FPChecker2 c (sprod2 (x, z⁻¹ o)) m n ∧ FixedAfter2 (z⁻¹ o) m n
  -- The lifted_loop checks the internal circuit
  -- and also whether the output is equal to the stored state (i.e. the lifting-delayed output)
  | Ckt.loop_lifted c => fun m n => let o := denote (Ckt.loop_lifted c) x
      FPChecker2 c (sprod2 (x, ↑↑z⁻¹ o)) m n ∧ o m n = (↑↑z⁻¹ o) m n

lemma ExtFP2_lifted_scalar_Ckt_let_fixed2 {A B: VType}
  (c: Ckt A B 1) (x: SOVType 1 A) (m n: ℕ) (hc: lifted_scalar_Ckt c):
    ExtFP2 c (let_fixed2 x m n) m n := by
  have h1 := FixedAfter2_let_fixed2 x m n
  have h2 := lifted_scalar_Ckt_ExtFP2 c (let_fixed2 x m n) hc
  rw [h2]; tauto

lemma FixedAfter2_denote_let_fixed2_agree {A B: VType}
  (c: Ckt A B 1) (x: SOVType 1 A) (m n: ℕ)
  (hf: FixedAfter2 (denote c (let_fixed2 x m n)) m n):
    let_fixed2 (denote c x) m n =[m]= denote c (let_fixed2 x m n) := by
  have hca := ckt_causalO c
  simp [CausalO] at hca
  intro i him
  funext j; simp [let_fixed2]
  split_ifs with hi hj
  · subst hi
    apply hca
    apply agreeT_imply_AgreeNested
    apply agreeT_let_fixed2
    simp [le_time]; omega
  · subst hi
    rw [hf _ (by omega)]
    apply hca
    apply agreeT_imply_AgreeNested
    apply agreeT_let_fixed2
    simp [le_time]
  · apply hca
    apply agreeT_imply_AgreeNested
    apply agreeT_let_fixed2
    simp [le_time]; omega

lemma loop_FixedAfter2_StFP2_iff {A B: VType}
  (c: Ckt (A ×ᵥB) B 1) (x: SOVType 1 A) (m n: ℕ)
  (hf: FixedAfter2 x m n):
    StFP2 c (sprod2 (x, z⁻¹ (denote (cloop c) x))) m n ∧
    FixedAfter2 (z⁻¹ (denote (cloop c) x)) m n <->
    StFP2 (cloop c) x m n := by
  calc
    _ <-> IntFP2 c (sprod2 (x, z⁻¹ (denote (cloop c) x))) m n := by
      rw [IntFP2_StFP2]; simp
      rw [FixedAfter2_sprod2]; tauto
    _ <-> IntFP2 (cloop c) x m n := by
      simp [IntFP2]
    _ <-> _ := by
      rw [IntFP2_StFP2]; simp [*]

lemma loop_FPChecker2_correct {A B: VType}
  (c: Ckt (A ×ᵥB) B 1) (x: SOVType 1 A) (m n: ℕ):
    StFP2 c (sprod2 (x, z⁻¹ (denote (cloop c) x))) m n ∧
    FixedAfter2 (z⁻¹ (denote (cloop c) x)) m n <->
    StFP2 (cloop c) x m n := by
  have hy1 := agreeT_let_fixed2 x m n
  have hy2 := FixedAfter2_let_fixed2 x m n
  set y := let_fixed2 x m n
  rw [StFP2_CausalT]
  case a =>
    rw [agreeT_sprod2]
    constructor; apply hy1
    apply causalT_agreeT; apply delay_causalT
    apply causalT_agreeT; apply ckt_causalT
    apply hy1
  rw [FixedAfter2_causal (s2:= z⁻¹ (denote (cloop c) y))]
  case heq =>
    apply delay_strict
    intro i hi
    apply ckt_causal
    rcases m; omega
    rw [agreeT_succ_iff] at hy1
    rcases hy1 with ⟨hy1, _⟩
    apply agreeUpto_weaken; apply hy1; omega
  nth_rw 2 [StFP2_CausalT]
  case a => apply hy1
  apply loop_FixedAfter2_StFP2_iff; tauto

lemma loop_lifted_FixedAfter2_ind {A B: VType}
  (c: Ckt (A ×ᵥB) B 1) (x: SOVType 1 A) (m n: ℕ)
  (he: denote (cloop2 c) x m n = z⁻¹ (denote (cloop2 c) x m) n)
  (h: FixedAfter2 (denote c (sprod2 (x, let_fixed2 (↑↑z⁻¹ (denote (cloop2 c) x)) m n))) m n):
    FixedAfter2 (↑↑z⁻¹ (denote (cloop2 c) x)) m n := by
  suffices: ↑↑z⁻¹ (denote (cloop2 c) x) =[m]= let_fixed2 (↑↑z⁻¹ (denote (cloop2 c) x)) m n
  · specialize this  m (by omega)
    rw [FixedAfter2_causal]
    case heq =>
      apply this
    apply FixedAfter2_let_fixed2
  intro i hi
  funext j; simp
  induction' j using Nat.strong_induction_on with j ihj
  rcases j with _ | j
  · simp [let_fixed2]
    intro hi hn; subst hi hn; simp
  simp [let_fixed2]
  intro hi; symm at hi; subst hi; clear hi
  split_ifs with hj; simp
  by_cases hjn: (j < n)
  · have : n = j + 1 := by omega
    subst this; simp
  simp [let_fixed2] at ihj
  specialize h j (by omega)
  have het :
    let_fixed2 (↑↑z⁻¹ (denote (cloop2 c) x)) m n ={m ,j}=
      ↑↑z⁻¹ (denote (cloop2 c) x) := by
    intro a b hab
    simp [let_fixed2]
    intro ha; subst a
    split_ifs with hb; simp
    simp [le_time] at hab
    symm; apply ihj <;> omega
  calc
    _ = denote c (sprod2 (x, let_fixed2 (↑↑z⁻¹ (denote (cloop2 c) x)) m n)) m j := by
      nth_rw 1 [loop_lifted_unfold]
      apply ckt_CausalNested
      apply agreeT_imply_AgreeNested
      rw [agreeT_sprod2]
      constructor; rfl
      symm; apply het
      rfl
    _ = _ := h
    _ = _ := by
      rw [<- he]
      nth_rw 2 [loop_lifted_unfold]
      apply ckt_CausalNested
      apply agreeT_imply_AgreeNested
      rw [agreeT_sprod2]
      constructor; rfl
      apply het; simp [le_time]; omega

lemma loop_lifted_FixedAfter2_StFP2_iff {A B: VType}
  (c: Ckt (A ×ᵥB) B 1) (x: SOVType 1 A) (m n: ℕ)
  (hf: FixedAfter2 x m n):
    StFP2 c (sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c) x))) m n ∧
    denote (cloop2 c) x m n = z⁻¹ (denote (cloop2 c) x m) n <->
    StFP2 (cloop2 c) x m n := by
  calc
  _ <-> IntFP2 c (sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c) x))) m n := by
    rw [IntFP2_StFP2]; simp
    rw [and_comm]; simp; intro hs
    constructor; swap
    -- This direction is easier
    · intro h
      rw [FixedAfter2_sprod2] at h
      rcases h with ⟨_, h⟩
      specialize h (n+1) (by omega)
      simp at h; tauto
    -- This direction is harder
    · intro h
      simp [StFP2] at hs
      rw [let_fixed2_sprod2] at hs
      have he := hf
      rw [<- let_fixed2_eq_iff] at he
      rw [he] at hs
      apply IntFP2_impl_ExtFP2 at hs
      rcases hs with ⟨_, hf2⟩
      rw [FixedAfter2_sprod2]
      constructor; tauto
      apply loop_lifted_FixedAfter2_ind <;> tauto
  _ <-> IntFP2 (cloop2 c) x m n := by
    simp [IntFP2]
  _ <-> _ := by
    rw [IntFP2_StFP2]; simp [*]

lemma loop_lifted_FPChecker2_correct {A B: VType}
  (c: Ckt (A ×ᵥB) B 1) (x: SOVType 1 A) (m n: ℕ):
    StFP2 c (sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c) x))) m n ∧
    denote (cloop2 c) x m n = z⁻¹ (denote (cloop2 c) x m) n <->
    StFP2 (cloop2 c) x m n := by
  have hy1 := agreeT_let_fixed2 x m n
  have hy2 := FixedAfter2_let_fixed2 x m n
  set y := let_fixed2 x m n
  rw [StFP2_CausalT]
  case a =>
    rw [agreeT_sprod2]
    constructor; apply hy1
    apply causalT_agreeT; apply lifting_causalT; apply delay_causal
    apply causalT_agreeT; apply ckt_causalT
    apply hy1
  nth_rw 2 [StFP2_CausalT]
  case a => apply hy1
  have : denote (cloop2 c) x m n =  denote (cloop2 c) y m n := by
    apply ckt_CausalNested
    apply agreeT_imply_AgreeNested <;> tauto
  rw [this]
  have : z⁻¹ (denote (cloop2 c) x m) n = z⁻¹ (denote (cloop2 c) y m) n := by
    apply delay_strict
    intro i hi
    apply ckt_CausalNested
    apply agreeT_imply_AgreeNested; tauto
    simp [le_time]; omega
  rw [this]
  apply loop_lifted_FixedAfter2_StFP2_iff; tauto

-- The corrrectness of `FPChecker2`
-- It is sound and complete w.r.t. `StFP2`
theorem FPChecker2_correct {A B: VType}
  (c: Ckt A B 1) (x: SOVType 1 A):
    FPChecker2 c x = StFP2 c x := by
  funext m n; simp
  revert c; apply Ckt_generalize_ns_1
  intro ns c hns; revert x m n
  induction c <;> intro x m n <;> (try subst hns) <;>
  simp [FPChecker2] <;>
  -- base cases are trivial since they are lifted functions
  try simp [StFP2, IntFP2]; apply ExtFP2_lifted_scalar_Ckt_let_fixed2; simp [lifted_scalar_Ckt]; tauto
  -- For lifting, the soundness depends on that of `FPChecker1`
  case lifting c ih =>
    simp [StFP2, IntFP2]
    clear ih; rw [FPChecker1_correct]
    simp [StFP1]; rw [let_fixed2_row_m]
  case seq c1 c2 ih1 ih2 =>
    simp [StFP2, IntFP2]
    simp at ih1 ih2
    rw [ih1, ih2]; simp [StFP2]
    intro h; apply IntFP2_impl_ExtFP2 at h
    suffices heq:
      let_fixed2 (denote c1 x) m n =[m]= denote c1 (let_fixed2 x m n)
    · rw [iff_eq_eq]
      rw [IntFP2_causal]; tauto
    rcases h with ⟨_, he⟩
    apply FixedAfter2_denote_let_fixed2_agree; tauto
  case par c1 c2 ih1 ih2 =>
    simp [StFP2, IntFP2]
    simp at ih1 ih2
    rw [ih1, ih2, StFP2, StFP2]
  case delay =>
    simp [StFP2, IntFP2]
    have hf := FixedAfter2_let_fixed2 x m n
    simp [ExtFP2, hf, denote]
    rw [FixedAfter2_causal]
    rcases m with (_ | m) <;> simp
    funext i; simp [let_fixed2]
  case loop c ih =>
    simp at ih; rw [ih]
    apply loop_FPChecker2_correct
  case loop_lifted c ih =>
    simp at ih; rw [ih]
    apply loop_lifted_FPChecker2_correct

end FPChecker2

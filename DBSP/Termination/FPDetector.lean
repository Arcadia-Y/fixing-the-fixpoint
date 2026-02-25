import DBSP.StreamTheory.Linear
import DBSP.Logic.SProp
import DBSP.Termination.Spec
import DBSP.Termination.FPProp
open CktBasic

-- Fixpoint Detector
-- for the outer iteration, i.e. the **1st** time dimension
section FPDetector1
variable {A B C: VType}

-- `let_fixed1 s n` is the stream acquired by
--  letting `s` be fixed after `n`
def let_fixed1 {T: Type} (s: stream T) (n: ℕ) : stream T :=
    fun i => if i < n then s i else s n

lemma agree_let_fixed1 {T: Type} (s: stream T) (n: ℕ):
   (let_fixed1 s n) =[n]= s   := by
  intro i hi; simp [let_fixed1]; intro
  have : n = i := by omega
  simp [this]

lemma FixAfter1_let_fixed1 {T: Type} (s: stream T) (n: ℕ):
    FixAfter1 (let_fixed1 s n) n := by
  intro m hm; simp [let_fixed1]; omega

lemma let_fixed1_eq_iff {T: Type} (s: stream T) (n: ℕ):
    (let_fixed1 s n) = s <-> FixAfter1 s n := by
  constructor
  · intro h; rw [<- h]; apply FixAfter1_let_fixed1
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

  -- A State Fixpoint is an index `n` such that:
  --  if after the outer iteration `n`, the input becomes fixed,
  --  then `n` will also be an internal fixedpoint.
  -- It's called the State Fixpoint because
  --   the state of the circuit after `n` is determined by the input up to `n`.
  def StFP1 {A B: VType} {ns: Bool} (c: Ckt A B ns) (x: SOVType ns A) (n: ℕ): Prop :=
    IntFP1 c (let_fixed1 x n) n

-- The internal fixedpoint is equivalent to
-- the State Fixpoint with the input being fixed after `n`
theorem IntFP1_StFP1 {A B: VType} {ns: Bool} (c: Ckt A B ns)
  (x: SOVType ns A):
    IntFP1 c x = SAnd (FixAfter1 x) (StFP1 c x) := by
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
  (hf: FixAfter1 x n) (hs: StFP1 c x n):
    IntFP1 c x n := by
  rw [IntFP1_StFP1]; simp; tauto

-- The State Fixpoint of a circuit on input `x`
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
    ∀ (y: SOVType ns A), (y =[n]= x) -> FixAfter1 y n -> IntFP1 c y n := by
  constructor
  · intro h y hag hf
    rw [IntFP1_StFP1]; simp
    constructor; tauto
    rw [StFP1_causal] <;> tauto
  · intro h
    simp [StFP1]
    apply h; apply agree_let_fixed1
    apply FixAfter1_let_fixed1

-- A high-level algorithm to detect the State Fixpoint `StFP1` at runtime.
-- For nested-circuits, this is run at the end of each outer iteration.
noncomputable def FPDetector1 {A B: VType} {ns: Bool} (c: Ckt A B ns) (x: SOVType ns A): stream Prop :=
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
  | Ckt.seq c1 c2 => SAnd (FPDetector1 c1 x) (FPDetector1 c2 (denote c1 x))
  | Ckt.par c1 c2 => SAnd (FPDetector1 c1 x) (FPDetector1 c2 x)
  -- checks whether the input is equal to the stored state (the last input)
  -- for non-nested delay, it's a single value
  -- for nested delay, it's a list
  | Ckt.delay => fun n => x n = (z⁻¹ x) n
  -- For `c↑ c`, returns true since it has no states across outer iterations
  | Ckt.lifting c => STrue
  -- It's the same for `lifted_delay`
  | Ckt.lifted_delay => STrue
  -- The detection for loop is similar to that of delay, but more complicated
  -- it detects the internal circuit
  -- and also checks whether the output is equal to the stored state (i.e. the delayed output)
  | Ckt.loop c =>
    fun n => let o := denote (Ckt.loop c) x
      FPDetector1 c (sprodO ns (x, z⁻¹ o)) n ∧ o n = (z⁻¹ o) n
  -- The lifted_loop itself has no states across outer iterations
  -- but the internal circuit may have states across outer iterations
  -- so we need to detect the internal circuit
  | Ckt.lifted_loop c => fun n => let o := denote (Ckt.lifted_loop c) x
      FPDetector1 c (sprod2 (x, ↑↑z⁻¹ o)) n
  -- We need to detect the internal circuit
  -- for the same reason as lifted_loop
  | Ckt.bracket c => fun n => FPDetector1 c (↑↑δ0 x) n

lemma ExtFP1_lifted_Ckt_let_fixed1 {A B: VType} {ns: Bool}
  (c: Ckt A B ns) (x: SOVType ns A) (n: ℕ) (hc: lifted_Ckt c):
    ExtFP1 c (let_fixed1 x n) n := by
  have h1 := FixAfter1_let_fixed1 x n
  have h2 := lifted_Ckt_ExtFP1 c (let_fixed1 x n) hc
  rw [h2]; tauto

lemma loop_FixAfter1_ind {A B: VType} {ns: Bool}
  (c: Ckt (A ×ᵥB) B ns) (x: SOVType ns A) (n: ℕ)
  (hf: FixAfter1 (denote c (sprodO ns (x, let_fixed1 (z⁻¹ (denote (cloop c) x)) n))) n)
  (heq: denote (cloop c) x n = z⁻¹ (denote (cloop c) x) n):
    FixAfter1 (z⁻¹ (denote (cloop c) x)) n := by
  suffices: z⁻¹ (denote (cloop c) x) = let_fixed1 (z⁻¹ (denote (cloop c) x)) n
  · rw [this]; apply FixAfter1_let_fixed1
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

lemma loop_FPDetector1_correct {A B: VType} {ns: Bool}
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
    rw [FixAfter1_sprodO] at he
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
    FixAfter1 (z⁻¹ (denote (cloop c) (let_fixed1 x n))) n
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
  apply loop_FixAfter1_ind <;> tauto

-- The proof is similar to `loop_FixAfter1_ind`
-- but needs induction on both two dimensions
lemma lifted_loop_FixAfter1_ind {A B: VType}
  (c: Ckt (A ×ᵥB) B 1) (x: SOVType 1 A) (n: ℕ)
  (hf: FixAfter1 (denote c (sprod2 (x, let_fixed1 (↑↑z⁻¹ (denote (cloop2 c) x)) n))) n):
    FixAfter1 (↑↑z⁻¹ (denote (cloop2 c) x)) n := by
  suffices: ↑↑z⁻¹ (denote (cloop2 c) x) = let_fixed1 (↑↑z⁻¹ (denote (cloop2 c) x)) n
  · rw [this]; apply FixAfter1_let_fixed1
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
  rw [lifted_loop_unfold]
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

-- This proof is similar to `loop_FPDetector1_correct`, but simpler
lemma lifted_loop_FPDetector1_correct {A B: VType} (c: Ckt (A ×ᵥB) B 1)
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
    rw [FixAfter1_sprod2] at he
    rcases he with ⟨_, he⟩
    rw [<- let_fixed1_eq_iff] at he
    rw [he]; tauto
  -- This direction is harder
  intro hi
  suffices hf:
    FixAfter1 (↑↑z⁻¹ (denote (cloop2 c) (let_fixed1 x n))) n
  · rw [<- let_fixed1_eq_iff] at hf
    rw [<- hf]; tauto
  apply IntFP1_impl_ExtFP1 at hi
  rcases hi with ⟨_, hf⟩
  apply lifted_loop_FixAfter1_ind; tauto

-- The corrrectness of `FPDetector1`
-- It is sound and complete w.r.t. `StFP1`
theorem FPDetector1_correct {A B: VType} {ns: Bool} (c: Ckt A B ns)
  (x: SOVType ns A):
    FPDetector1 c x = StFP1 c x := by
  funext n; simp; revert x; induction c <;>
  intro x <;> simp [FPDetector1, StFP1, IntFP1] <;>
  -- base cases are trivial since they are lifted functions
  (try  apply ExtFP1_lifted_Ckt_let_fixed1) <;>
  (try unfold lifted_Ckt; simp [lifted_Ckt, denote, liftO]) <;>
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
    have hf := FixAfter1_let_fixed1 x n
    simp [hf, denote]
    rw [<- FixAfter1_extend]
    rw [FixAfter1_delay_succ]; simp [hf]
    rcases n <;> simp [let_fixed1] <;> tauto
  case loop ns _ _ c ih =>
    rw [ih]; apply loop_FPDetector1_correct
  case lifted_loop c ih =>
    rw [ih, StFP1]
    rw [let_fixed1_sprod2]
    apply lifted_loop_FPDetector1_correct
  case bracket c ih =>
    rw [ih, StFP1]
    rw [iff_eq_eq]; congr
    funext i j
    by_cases hi:(i < n)
    · simp [hi, let_fixed1]
    by_cases hj:(j = 0)
    · simp [hj, hi, let_fixed1]
    simp [hi, hj, let_fixed1]

end FPDetector1


-- Fixedpoint Detector
-- for the inner iteration, i.e. the **2nd** time dimension
section FPDetector2
variable {A B C: VType}

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

lemma FixAfter2_let_fixed2 {T: Type}
  (s: stream (stream T)) (m n: ℕ):
    FixAfter2 (let_fixed2 s m n) m n := by
  simp [FixAfter2]; intro i hi
  simp [let_fixed2]; intros; omega

lemma let_fixed2_eq_iff {T: Type}
  (s: stream (stream T)) (m n: ℕ):
    (let_fixed2 s m n) = s <-> FixAfter2 s m n := by
  constructor
  · intro h; rw [<- h]; apply FixAfter2_let_fixed2
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
-- A nested State Fixpoint is a point `(m, n)` such that:
--  if the input becomes fixed after `(m, n)`,
--  then `(m, n)` will also be a nested internal fixedpoint.
def StFP2 {A B: VType} (c: Ckt A B 1) (x: SOVType 1 A) (m n: ℕ): Prop :=
  IntFP2 c (let_fixed2 x m n) m n

-- The nested internal fixedpoint is equivalent to
-- the nested State Fixpoint with the input being fixed after `(m, n)`
theorem IntFP2_StFP2 {A B: VType} (c: Ckt A B 1)
  (x: SOVType 1 A) :
    IntFP2 c x = SAnd2 (FixAfter2 x) (StFP2 c x) := by
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

-- The nested State Fixpoint of a circuit on input `x`
-- is equivalent to that on input `let_fixed2 m n x`
theorem StFP2_let_fixed1_eq {A B: VType} (c: Ckt A B 1)
  (x: SOVType 1 A) (m n: ℕ):
    StFP2 c (let_fixed2 x m n) m n <-> StFP2 c x m n := by
  simp [StFP2]; rw [let_fixed2_idem]

-- The nested State Fixpoint is CausalT
theorem StFP2_CausalT {A B: VType} (c: Ckt A B 1):
    CausalT (StFP2 c) := by
  intro x1 x2 m n hca
  simp [StFP2]; rw [iff_eq_eq]
  rw [IntFP2_causal]
  apply let_fixed2_causal; tauto

theorem StFP2_iff {A B: VType}
  {c: Ckt A B 1} {x: SOVType 1 A} {m n: ℕ}:
    StFP2 c x m n <->
    ∀ (y: SOVType 1 A), (y ={m, n}= x) -> FixAfter2 y m n -> IntFP2 c y m n := by
  constructor
  · intro h y hag hf
    rw [IntFP2_StFP2]; simp
    constructor; tauto
    rw [StFP2_CausalT] <;> tauto
  · intro h
    simp [StFP2]
    apply h; symm; apply agreeT_let_fixed2
    apply FixAfter2_let_fixed2

-- A high-level algorithm to detect the nested State Fixpoint `StFP2` at runtime
noncomputable def FPDetector2 {A B: VType} (c: Ckt A B 1) (x: SOVType 1 A): stream (stream Prop) :=
  match c with
  -- primitive nodes and convenient constructs
  | Ckt.node1 f => STrue2
  | Ckt.node2 f => STrue2
  | Ckt.const k => STrue2
  | Ckt.id => STrue2
  | Ckt.fst => STrue2
  | Ckt.snd => STrue2
  | Ckt.add => STrue2
  | Ckt.sub => STrue2
  -- sequential and parallel composition
  | Ckt.seq c1 c2 => SAnd2 (FPDetector2 c1 x) (FPDetector2 c2 (denote c1 x))
  | Ckt.par c1 c2 => SAnd2 (FPDetector2 c1 x) (FPDetector2 c2 x)
  -- Nested delay needs to detect whether the input from last row has reached the fixedpoint
  -- which is assumed to be stored in the state at the end of last outer iteration
  | Ckt.delay => fun m n => FixAfter2 (z⁻¹ x) m n
  -- This is where `FPDetector2` depends on `FPDetector1`
  -- For `c↑ c`, it detects the `StFP1` of the inner circuit `c`
  | Ckt.lifting c => fun m n => FPDetector1 c (x m) n
  -- For the lifted_delay, the following is just the simplication of `FPDetector1 delay (x m) n`
  | Ckt.lifted_delay => fun m n => x m n = z⁻¹ (x m) n
  -- The detection for loop is similar to that of delay, but more complicated
  -- it detects the internal circuit
  -- and also checks whether the output from last row has reached fixedpoint
  | Ckt.loop c => fun m n => let o := denote (Ckt.loop c) x
      FPDetector2 c (sprod2 (x, z⁻¹ o)) m n ∧ FixAfter2 (z⁻¹ o) m n
  -- The lifted_loop detects the internal circuit
  -- and also checks whether the output is equal to the stored state (i.e. the lifting-delayed output)
  | Ckt.lifted_loop c => fun m n => let o := denote (Ckt.lifted_loop c) x
      FPDetector2 c (sprod2 (x, ↑↑z⁻¹ o)) m n ∧ o m n = (↑↑z⁻¹ o) m n

lemma ExtFP2_lifted_scalar_Ckt_let_fixed2 {A B: VType} {f}
  (c: Ckt A B 1) (x: SOVType 1 A) (m n: ℕ) (hc: DenoteLiftedScalar c f):
    ExtFP2 c (let_fixed2 x m n) m n := by
  have h1 := FixAfter2_let_fixed2 x m n
  have h2 := DenoteLiftedScalar_ExtFP2 c (let_fixed2 x m n) hc
  rw [h2]; tauto

lemma FixAfter2_denote_let_fixed2_agree {A B: VType}
  (c: Ckt A B 1) (x: SOVType 1 A) (m n: ℕ)
  (hf: FixAfter2 (denote c (let_fixed2 x m n)) m n):
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

lemma loop_FixAfter2_StFP2_iff {A B: VType}
  (c: Ckt (A ×ᵥB) B 1) (x: SOVType 1 A) (m n: ℕ)
  (hf: FixAfter2 x m n):
    StFP2 c (sprod2 (x, z⁻¹ (denote (cloop c) x))) m n ∧
    FixAfter2 (z⁻¹ (denote (cloop c) x)) m n <->
    StFP2 (cloop c) x m n := by
  calc
    _ <-> IntFP2 c (sprod2 (x, z⁻¹ (denote (cloop c) x))) m n := by
      rw [IntFP2_StFP2]; simp
      rw [FixAfter2_sprod2_iff]; tauto
    _ <-> IntFP2 (cloop c) x m n := by
      simp [IntFP2]
    _ <-> _ := by
      rw [IntFP2_StFP2]; simp [*]

lemma loop_FPDetector2_correct {A B: VType}
  (c: Ckt (A ×ᵥB) B 1) (x: SOVType 1 A) (m n: ℕ):
    StFP2 c (sprod2 (x, z⁻¹ (denote (cloop c) x))) m n ∧
    FixAfter2 (z⁻¹ (denote (cloop c) x)) m n <->
    StFP2 (cloop c) x m n := by
  have hy1 := agreeT_let_fixed2 x m n
  have hy2 := FixAfter2_let_fixed2 x m n
  set y := let_fixed2 x m n
  rw [StFP2_CausalT]
  case a =>
    rw [agreeT_sprod2]
    constructor; apply hy1
    apply causalT_agreeT; apply delay_causalT
    apply causalT_agreeT; apply ckt_causalT
    apply hy1
  rw [FixAfter2_causal (s2:= z⁻¹ (denote (cloop c) y))]
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
  apply loop_FixAfter2_StFP2_iff; tauto

lemma lifted_loop_FixAfter2_ind {A B: VType}
  (c: Ckt (A ×ᵥB) B 1) (x: SOVType 1 A) (m n: ℕ)
  (he: denote (cloop2 c) x m n = z⁻¹ (denote (cloop2 c) x m) n)
  (h: FixAfter2 (denote c (sprod2 (x, let_fixed2 (↑↑z⁻¹ (denote (cloop2 c) x)) m n))) m n):
    FixAfter2 (↑↑z⁻¹ (denote (cloop2 c) x)) m n := by
  suffices: ↑↑z⁻¹ (denote (cloop2 c) x) =[m]= let_fixed2 (↑↑z⁻¹ (denote (cloop2 c) x)) m n
  · specialize this  m (by omega)
    rw [FixAfter2_causal]
    case heq =>
      apply this
    apply FixAfter2_let_fixed2
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
      nth_rw 1 [lifted_loop_unfold]
      apply ckt_CausalNested
      apply agreeT_imply_AgreeNested
      rw [agreeT_sprod2]
      constructor; rfl
      symm; apply het
      rfl
    _ = _ := h
    _ = _ := by
      rw [<- he]
      nth_rw 2 [lifted_loop_unfold]
      apply ckt_CausalNested
      apply agreeT_imply_AgreeNested
      rw [agreeT_sprod2]
      constructor; rfl
      apply het; simp [le_time]; omega

lemma lifted_loop_FixAfter2_StFP2_iff {A B: VType}
  (c: Ckt (A ×ᵥB) B 1) (x: SOVType 1 A) (m n: ℕ)
  (hf: FixAfter2 x m n):
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
      rw [FixAfter2_sprod2_iff] at h
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
      rw [FixAfter2_sprod2_iff]
      constructor; tauto
      apply lifted_loop_FixAfter2_ind <;> tauto
  _ <-> IntFP2 (cloop2 c) x m n := by
    simp [IntFP2]
  _ <-> _ := by
    rw [IntFP2_StFP2]; simp [*]

lemma lifted_loop_FPDetector2_correct {A B: VType}
  (c: Ckt (A ×ᵥB) B 1) (x: SOVType 1 A) (m n: ℕ):
    StFP2 c (sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c) x))) m n ∧
    denote (cloop2 c) x m n = z⁻¹ (denote (cloop2 c) x m) n <->
    StFP2 (cloop2 c) x m n := by
  have hy1 := agreeT_let_fixed2 x m n
  have hy2 := FixAfter2_let_fixed2 x m n
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
  apply lifted_loop_FixAfter2_StFP2_iff; tauto

-- The corrrectness of `FPDetector2`
-- It is sound and complete w.r.t. `StFP2`
theorem FPDetector2_correct {A B: VType}
  (c: Ckt A B 1) (x: SOVType 1 A):
    FPDetector2 c x = StFP2 c x := by
  funext m n; simp
  revert c; apply Ckt_generalize_ns_1
  intro ns c hns; revert x m n
  induction c <;> intro x m n <;> (try subst hns) <;>
  simp [FPDetector2] <;>
  -- base cases are trivial since they are lifted functions
  try simp [StFP2, IntFP2]; apply ExtFP2_lifted_scalar_Ckt_let_fixed2; simp [DenoteLiftedScalar]; tauto
  -- For lifting, the correctness depends on that of `FPDetector1`
  case lifting c ih =>
    simp [StFP2, IntFP2]
    clear ih; rw [FPDetector1_correct]
    simp [StFP1]; rw [let_fixed2_row_m]
  case lifted_delay =>
    simp [StFP2, IntFP2, ExtFP2, denote, lifting, FixAfter2]
    have hf := FixAfter1_let_fixed1 (x m) n
    simp [hf, let_fixed2_row_m]
    rw [<- FixAfter1_extend]
    rw [FixAfter1_delay_succ]
    simp [hf, let_fixed1]
    rcases n <;> simp [let_fixed1] <;> tauto
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
    apply FixAfter2_denote_let_fixed2_agree; tauto
  case par c1 c2 ih1 ih2 =>
    simp [StFP2, IntFP2]
    simp at ih1 ih2
    rw [ih1, ih2, StFP2, StFP2]
  case delay =>
    simp [StFP2, IntFP2]
    have hf := FixAfter2_let_fixed2 x m n
    simp [ExtFP2, hf, denote]
    rw [FixAfter2_causal]
    rcases m with (_ | m) <;> simp
    funext i; simp [let_fixed2]
  case loop c ih =>
    simp at ih; rw [ih]
    apply loop_FPDetector2_correct
  case lifted_loop c ih =>
    simp at ih; rw [ih]
    apply lifted_loop_FPDetector2_correct

end FPDetector2

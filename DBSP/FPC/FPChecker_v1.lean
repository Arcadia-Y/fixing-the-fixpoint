import DBSP.Circuits.Circuits_v4
import DBSP.StreamTheory.Linear
import DBSP.Logic.SProp
open CktBasic

section FPChecker
variable {A B C: VType}

def FixedAfter {T: Type} (s: stream T) (n: ℕ): Prop :=
  ∀ m ≥ n, s m = s n

lemma FixedAfter_mono {T: Type} {s: stream T} {n1 n2: ℕ}
  (h: FixedAfter s n1)(hn: n1 ≤ n2):
     FixedAfter s n2 := by
  intro m hm
  have := h _ hn
  specialize h m (by omega)
  rw [this, h]

lemma FixedAfter_sprod {A B: Type} {s1: stream A} {s2: stream B}
  {p: ℕ}:
    FixedAfter (sprod (s1, s2)) p <->
    FixedAfter s1 p ∧ FixedAfter s2 p := by
  simp [FixedAfter]; constructor <;> intros; swap; tauto
  rename_i h; constructor <;> intros m hm <;> specialize h m hm <;> tauto

lemma FixedAfter_sprod2 {A B: Type} {s1: stream (stream A)} {s2: stream (stream B)}
  {m n: ℕ}:
    FixedAfter (sprod2 (s1, s2) m) n  <->
    FixedAfter (s1 m) n ∧ FixedAfter (s2 m) n := by
  simp [FixedAfter]; constructor <;> intros; swap; tauto
  rename_i h; constructor <;> intros m hm <;> specialize h m hm <;> tauto

lemma FixedAfter_delay_0 {T: Type} [Zero T] {s: stream T}:
    FixedAfter (z⁻¹ s) 0 <-> s = 0 := by
  simp [FixedAfter, delay]; constructor
  · intro h; funext m; specialize h (m+1) (by omega)
    simp at h; rw [h]; rfl
  · intro h; rw [h]; simp [FixedAfter]

lemma FixedAfter_delay_succ {T: Type} [Zero T] {s: stream T} {n: ℕ}:
    FixedAfter (z⁻¹ s) (n+1) <-> FixedAfter s n := by
  simp [FixedAfter]; constructor
  · intro h m hm
    specialize h (m+1) (by omega)
    simp at h; tauto
  · intro h m hm
    specialize h (m-1) (by omega)
    simp [delay]
    rcases m; omega
    simp at h ⊢; tauto

lemma FixedAfter_lifting {A B: Type} {s: stream A} {n: ℕ}
  {f: A -> B} (hx: FixedAfter s n):
    FixedAfter (↑↑f s) n := by
  simp [FixedAfter, lifting] at hx ⊢
  intros; congr 1; apply hx; tauto

-- SPos is the type of the position in a stream or a stream of streams
@[reducible]
def SPos (ns: Bool): Type :=
  if ns then ℕ × ℕ else ℕ

@[simp]
lemma SPos_false: SPos false = ℕ := by rfl
@[simp]
lemma SPos_true: SPos true = (ℕ × ℕ) := by rfl

def SPread {ns: Bool} {T: Type}
  (s: SOType ns T) (p: SPos ns): T :=
  match ns with
  | false => s p
  | true => s p.1 p.2

@[simp]
lemma SPread_false {T: Type} (s: SOType false T) (n: ℕ):
    SPread s n = s n := by rfl

@[simp]
lemma SPread_true {T: Type} (s: SOType true T) (m n: ℕ):
    SPread s (m, n) = s m n := by rfl

@[simp]
lemma SPread_STrue {ns: Bool} (p: SPos ns):
    SPread STrue p = True := by
  rcases ns <;> simp [SPread]

-- SFixedAfter is a version of FixedAfter that works for both nested and non-nested streams
def SFixedAfter {T: Type} {ns: Bool} (s: SOType ns T) (p: SPos ns): Prop :=
  match ns with
  | false => FixedAfter s p
  | true => FixedAfter (s p.1) p.2

@[simp]
lemma SFixedAfter_false {T: Type} (s: SOType false T) (n: ℕ):
    SFixedAfter s n = FixedAfter s n := by rfl

@[simp]
lemma SFixedAfter_true {T: Type} (s: SOType true T) (m n: ℕ):
    SFixedAfter s (m, n) = FixedAfter (s m) n := by rfl

lemma SFixedAfter_liftO {A B: Type} {ns: Bool} {s: SOType ns A} {p: SPos ns}
  {f: A -> B} (hx: SFixedAfter s p):
    SFixedAfter (liftO ns f s) p := by
  simp [FixedAfter, liftO] at hx ⊢
  rcases ns <;> simp <;> apply FixedAfter_lifting hx

-- The external fixedpoint is a point after which,
-- both the input and output of the circuit become fixed.
def ExtFP {ns: Bool} (c: Ckt A B ns 0) (x: SOVType ns A) (p: SPos ns): Prop :=
  SFixedAfter x p ∧ SFixedAfter (denote c x) p

-- For lifted circuits, ExtFP is equivalent to input being fixed after `p`
theorem lifted_Ckt_ExtFP {A B: VType} {ns: Bool} (c: Ckt A B ns 0)
  (x: SOVType ns A) (p: SPos ns) (hc: lifted_Ckt c):
    ExtFP c x p <-> SFixedAfter x p := by
  simp [ExtFP]; intro h
  rcases hc with ⟨f, hc⟩; rw [hc]
  apply SFixedAfter_liftO h

-- For nested circuits, the external fixedpoint is causal
theorem ExtFP_nested_causal (c: Ckt A B 1 0) (x1 x2: SOVType 1 A)
  (m n: ℕ) (hca: x1 =[m]= x2):
    ExtFP c x1 (m, n) <-> ExtFP c x2 (m, n) := by
  simp [ExtFP]
  have : x1 m = x2 m := by
    apply hca; rfl
  rw [this]
  have : denote c x1 m = denote c x2 m := by
    have := causalO_ckt c
    apply causalO_is_causal at this
    apply this; tauto
  rw [this]

-- The internal fixedpoint is a point after which,
-- for any internal operator in the circuit,
-- both the input and output become fixed.
def IntFP {A B: VType} {ns: Bool} (c: Ckt A B ns 0) (x: SOVType ns A) (p: SPos ns): Prop :=
  match c with
  | Ckt.node1 f => ExtFP (Ckt.node1 f) x p
  | Ckt.node2 f => ExtFP (Ckt.node2 f) x p
  | Ckt.const k => ExtFP (Ckt.const k) x p
  | Ckt.id => ExtFP (Ckt.id) x p
  | Ckt.fst => ExtFP (Ckt.fst) x p
  | Ckt.snd => ExtFP (Ckt.snd) x p
  | Ckt.add => ExtFP (Ckt.add) x p
  | Ckt.sub => ExtFP (Ckt.sub) x p
  | Ckt.seq c1 c2 => let o := denote c1 x
       IntFP c1 x p ∧ IntFP c2 o p
  | Ckt.par c1 c2 => IntFP c1 x p ∧ IntFP c2 x p
  | Ckt.delay => ExtFP Ckt.delay x p
  | Ckt.lifting c => IntFP c (x p.1) p.2
  | Ckt.loop c =>  IntFP c (sprodO ns (x, z⁻¹ (denote (Ckt.loop c) x))) p
  | Ckt.loop_lifted c => IntFP c (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.loop_lifted c) x))) p

-- The internal fixedpoint implies the external fixedpoint
theorem IntFP_impl_ExtFP {ns: Bool} (c: Ckt A B ns 0) (x: SOVType ns A) (p: SPos ns):
    IntFP c x p -> ExtFP c x p := by
  revert c; apply Ckt_generalize_rec_0
  intro rec c; revert x p
  induction c <;> intro x p hr <;> (try subst hr) <;> simp [IntFP]
  case seq c1 c2 ih1 ih2 =>
    specialize ih1 x p; specialize ih2 (denote c1 x) p
    simp at ih1 ih2
    intro h1 h2; apply ih1 at h1; apply ih2 at h2
    rename Bool => ns; rcases ns <;> simp [ExtFP] at h1 h2 ⊢ <;>
    simp [denote] <;> tauto
  case par c1 c2 ih1 ih2 =>
    specialize ih1 x p; specialize ih2 x p
    simp at ih1 ih2
    intro h1 h2; apply ih1 at h1; apply ih2 at h2
    rename Bool => ns; rcases ns <;> simp [ExtFP] at h1 h2 ⊢ <;>
    simp [denote]
    · constructor; tauto
      rw [FixedAfter_sprod]; tauto
    · constructor; tauto
      simp [SFixedAfter]
      rw [FixedAfter_sprod2]; tauto
  case lifting c ih =>
    specialize ih (x p.1) p.2
    intro h1; apply (ih hr) at h1
    simp [ExtFP] at h1 ⊢; tauto
  case loop c ih =>
    rename Bool => ns
    specialize ih (sprodO ns (x, z⁻¹ (denote (Ckt.loop c) x))) p; simp at ih
    intro h; apply ih at h
    rcases ns <;> simp [ExtFP] at h ⊢ <;> rcases h with ⟨h1, h2⟩
    · rw [FixedAfter_sprod] at h1; rcases h1 with ⟨h1a, h1b⟩
      rcases p
      · rw [FixedAfter_delay_0] at h1b; rw [h1b]
        tauto
      · rw [FixedAfter_delay_succ] at h1b
        constructor; tauto
        apply FixedAfter_mono h1b; simp
    · simp [SFixedAfter] at h1
      rw [FixedAfter_sprod2] at h1
      rcases p with ⟨p1, p2⟩; simp at *
      rw [loop_unfold]; simp; tauto
  case loop_lifted c ih =>
    specialize ih (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.loop_lifted c) x))) p
    simp at ih
    intro h; apply ih at h
    rcases h with ⟨h1, h2⟩
    simp [SFixedAfter] at h1
    rw [FixedAfter_sprod2] at h1
    constructor; tauto
    rcases h1 with ⟨_, h1⟩
    simp at h1
    rcases p with ⟨p1, p2⟩; simp at *
    rcases p2
    · rw [FixedAfter_delay_0] at h1; rw [h1]; tauto
    · rw [FixedAfter_delay_succ] at h1
      apply FixedAfter_mono h1; simp

-- For nested circuits, the internal fixedpoint is causal
theorem IntFP_nested_causal (c: Ckt A B 1 0) (x1 x2: SOVType 1 A)
  (p: ℕ × ℕ) (hca: x1 =[p.1]= x2):
    IntFP c x1 p <-> IntFP c x2 p := by
  revert c; apply Ckt_generalize_rec_0
  intro rec c hrec; revert c
  apply Ckt_generalize_ns_1
  intro ns c hns; revert x1 x2; induction c <;>
    (try subst hrec) <;> (try subst hns) <;>
    intro x1 x2 hca <;> simp [IntFP] <;>
    (try apply ExtFP_nested_causal; tauto)
  case seq c1 c2 ih1 ih2 =>
    simp at ih1 ih2
    specialize ih1 x1 x2 hca
    rw [<- ih1]; simp; intro h1
    apply ih2
    apply causal_respects_agreeUpto
    apply causalO_is_causal; apply causalO_ckt
    tauto
  case par c1 c2 ih1 ih2 =>
    simp at ih1 ih2
    specialize ih1 x1 x2 hca; specialize ih2 x1 x2 hca
    rw [ih1, ih2]
  case lifting c =>
    rcases p with ⟨m, n⟩; simp at *
    have : x1 m = x2 m := by
      apply hca; rfl
    rw [this]
  case loop c ih =>
    simp at ih; simp [sprodO]
    apply ih








-- `Seq_upto s1 s2 p` means that
--  `s1` and `s2` are equal up to the moment (position) `p`
def Seq_upto {ns: Bool} {T: Type} [Zero T] (p: SPos ns) (s1 s2: SOType ns T) : Prop :=
  match ns with
  | false => s1 =[p]= s2
  | true => ((z⁻¹ s1) =[p.1]= (z⁻¹ s2)) ∧ s1 p.1 =[p.2]= s2 p.1

notation:35 s1 " ={ " p " }= " s2 => Seq_upto p s1 s2

-- `Seq_upto` is an equivalence relation
@[refl]
lemma Seq_upto_refl {ns: Bool} {T: Type} [Zero T]
  (p: SPos ns) (s: SOType ns T) :
    s ={p}= s := by
  rcases ns <;> simp [Seq_upto]; rfl
  constructor <;> rfl

@[symm]
lemma Seq_upto_symm {ns: Bool} {T: Type} [Zero T]
  {p: SPos ns} {s1 s2: SOType ns T} :
    (s1 ={p}= s2) -> s2 ={p}= s1 := by
  rcases ns <;> simp [Seq_upto]
  · intro h; symm; tauto
  · intros; constructor <;> symm <;> tauto

@[trans]
lemma Seq_upto_trans {ns: Bool} {T: Type} [Zero T]
  {p: SPos ns} {s1 s2 s3: SOType ns T} :
    (s1 ={p}= s2) -> (s2 ={p}= s3) -> (s1 ={p}= s3) := by
  rcases ns <;> simp [Seq_upto]
  · intros; trans <;> tauto
  · intros; constructor <;> trans <;> tauto

-- `let_fixed s p` is the stream acquired by
--  letting `s` be fixed after `p`
def let_fixed {ns: Bool} {T: Type} [Zero T]
  (p: SPos ns) (s: SOType ns T) : SOType ns T :=
  match ns with
  | false => fun n => if n < p then s n else s p
  | true => fun m n =>
      if m != p.1 then s m n
      else if n < p.2 then s p.1 n
      else s p.1 p.2

lemma Seq_upto_let_fixed {ns: Bool} {T: Type} [Zero T]
  {s: SOType ns T} {p: SPos ns}:
    Seq_upto p s (let_fixed p s) := by
  rcases ns <;> simp [Seq_upto] <;> simp at p
  · intro i hi; simp [let_fixed]; intro
    have : p = i := by omega
    simp [this]
  · rcases p with ⟨m, n⟩; simp
    constructor
    · intro i hi
      rcases i <;> simp [let_fixed]
      funext j; simp; omega
    · intro i hi
      simp [let_fixed]; intros
      have : n = i := by omega
      simp [this]

lemma SFixedAfter_let_fixed {ns: Bool} {T: Type} [Zero T]
  (s: SOType ns T) (p: SPos ns):
    SFixedAfter (let_fixed p s) p := by
  rcases ns <;> simp [SFixedAfter, FixedAfter] <;> simp at p
  · intro m hm; simp [let_fixed]; omega
  · rcases p with ⟨m, n⟩; simp
    intro i hi; simp [let_fixed]; intros
    omega

lemma let_fixed_eq_iff {ns: Bool} {T: Type} [Zero T]
  {s: SOType ns T} {p: SPos ns}:
    (let_fixed p s) = s <-> SFixedAfter s p := by
  constructor
  · intro h; rw [<- h]; apply SFixedAfter_let_fixed
  intro h; rcases ns <;> simp at p
  · funext n; simp [let_fixed]
    intro hn; rw [<- h]; omega
  · rcases p with ⟨p1, p2⟩; funext m n
    simp [let_fixed]
    intro hm; subst hm
    simp; intro hn; rw [<- h]; omega

-- `let_fixed` is idempotent
lemma let_fixed_idem {ns: Bool} {T: Type} [Zero T]
  (s: SOType ns T) (p: SPos ns):
    let_fixed p (let_fixed p s) = let_fixed p s := by
  rcases ns <;> simp at p
  · funext n; simp [let_fixed]; omega
  · rcases p with ⟨p1, p2⟩; funext m n; simp [let_fixed]
    intro hm; subst hm
    simp; omega

-- A state fixedpoint is a point `p` that:
--  if the input becomes fixed after `p`,
--  then `p` will also be an internal fixedpoint.
-- It's called the state fixedpoint because
--   the state of the circuit at `p` is determined by the input up to `p`.
def StFP {A B: VType} {ns: Bool} (c: Ckt A B ns 0) (x: SOVType ns A) (p: SPos ns): Prop :=
  IntFP c (let_fixed p x) p

-- The internal fixedpoint is equivalent to
-- the state fixedpoint with the input being fixed after `p`
theorem IntFP_StFP {A B: VType} {ns: Bool} (c: Ckt A B ns 0)
  (x: SOVType ns A) (p: SPos ns):
    IntFP c x p <-> (SFixedAfter x p ∧ StFP c x p) := by
  simp [StFP]; constructor
  · intro hi
    have he := IntFP_impl_ExtFP c x p hi
    rcases he with ⟨h1, h2⟩
    constructor; tauto
    rw [<- let_fixed_eq_iff] at h1
    rw [h1]; tauto
  · rintro ⟨h1, h2⟩
    rw [<- let_fixed_eq_iff] at h1
    rw [<- h1]; tauto

lemma ExtFP_lifted_Ckt_let_fixed {A B: VType} {ns: Bool} (c: Ckt A B ns 0)
  (x: SOVType ns A) (p: SPos ns) (hc: lifted_Ckt c):
    ExtFP c (let_fixed p x) p := by
  rw [lifted_Ckt_ExtFP]
  apply SFixedAfter_let_fixed; tauto

-- The state fixedpoint of a circuit on input `x`
-- is equivalent to that on input `let_fixed p x`
theorem StFP_let_fixed_eq {A B: VType} {ns: Bool} (c: Ckt A B ns 0)
  (x: SOVType ns A) (p: SPos ns):
    StFP c (let_fixed p x) p <-> StFP c x p := by
  simp [StFP]; rw [let_fixed_idem]

-- A high-level specification of the fixedpoint checker
-- the idea is to check the state fixedpoint `StFP` at runtime:
noncomputable def FPChecker {A B: VType} {ns: Bool} (c: Ckt A B ns 0) (x: SOVType ns A): SOType ns Prop :=
  match c with
  | Ckt.node1 f => STrue
  | Ckt.node2 f => STrue
  | Ckt.const k => STrue
  | Ckt.id => STrue
  | Ckt.fst => STrue
  | Ckt.snd => STrue
  | Ckt.add => STrue
  | Ckt.sub => STrue
  | Ckt.seq c1 c2 => SAnd (FPChecker c1 x) (FPChecker c2 (denote c1 x))
  | Ckt.par c1 c2 => SAnd (FPChecker c1 x) (FPChecker c2 x)
  | Ckt.delay => match ns with
    -- for non-nested delay, it checks whether the input is equal to the stored state (the output)
    | false => fun n => x n = (z⁻¹ x) n
    -- for nested delay, it checks whether the input from last row has reached fixedpoint
    --   which is also assumed to be stored in the state
    | true => fun m n => FixedAfter (z⁻¹ x m) n
  | Ckt.lifting c => fun m n => FPChecker c (x m) n
  -- The checking for loop is similar to that of delay, but more complicated
  | Ckt.loop c => match ns with
    -- for non-nested loop, it checks the internal circuit
    -- and also whether the output is equal to the stored state (i.e. the delayed output)
    | false => fun n => let o := denote (Ckt.loop c) x
      FPChecker c (sprod (x, z⁻¹ o)) n ∧ o n = (z⁻¹ o) n
    -- for nested loop, it checks the internal circuit
    -- and also whether the output from last row has reached fixedpoint
    | true => fun m n => let o := denote (Ckt.loop c) x
      FPChecker c (sprod2 (x, z⁻¹ o)) m n ∧ FixedAfter (z⁻¹ o m) n
  -- The checking for loop_lifted is similar to that of non-nested loop
  | Ckt.loop_lifted c => fun m n => let o := denote (Ckt.loop_lifted c) x
      FPChecker c (sprod2 (x, ↑↑z⁻¹ o)) m n ∧ o m n = (↑↑z⁻¹ o) m n

--  The soundness of `FPChecker` w.r.t. the idea mentinioned above
theorem FPChecker_sound {A B: VType} {ns: Bool} (c: Ckt A B ns 0)
  (x: SOVType ns A) (p: SPos ns):
    SPread (FPChecker c x) p <-> StFP c x p := by
  revert c; apply Ckt_generalize_rec_0
  intro rec c; revert x p
  induction c <;> intro x p hr <;> (try subst hr) <;>
  simp [FPChecker, StFP, IntFP] <;>
  -- base cases are trivial since they are lifted functions
  try apply ExtFP_lifted_Ckt_let_fixed; simp [lifted_Ckt]; tauto
  case id =>
    apply ExtFP_lifted_Ckt_let_fixed; simp [lifted_Ckt]
    rename Bool => ns; rcases ns <;> tauto
  case lifting c ih =>
    simp at ih
    rcases p with ⟨m, n⟩; simp
    set s1 := let_fixed (m, n) x m
    simp at s1
    set s2 := @let_fixed false _ (by infer_instance) n (x m)
    unfold SOType at s2; simp at s2
    have : s1 = s2 := by
      funext k; simp [s1, s2, let_fixed]
    rw [this]
    unfold s2; apply ih
  case seq c1 c2 ih1 ih2 =>
    simp at ih1 ih2
    rename Bool => ns; rcases ns <;> simp at p ih1 ih2 ⊢
    · rw [ih1, ih2]
      simp_rw [IntFP_StFP, StFP_let_fixed_eq]
      have := SFixedAfter_let_fixed x p
      have := SFixedAfter_let_fixed (denote c1 x) p

    · rcases p with ⟨m, n⟩; simp
      rw [ih1, ih2]; simp [StFP]
      specialize ih1 x m n hx; rw [ih1]
      suffices h: IntFP c1 x (m, n) ->
        (FPChecker c2 (denote c1 x) m n <-> IntFP c2 (denote c1 x) (m, n))
      tauto
      intro h; apply IntFP_impl_ExtFP at h
      apply ih2; apply h.2
  case par c1 c2 ih1 ih2 =>
    simp at ih1 ih2
    specialize ih1 x p hx; specialize ih2 x p hx
    rw [<- ih1, <- ih2]
    rename Bool => ns; rcases ns; simp
    rcases p; simp
  case delay =>
    rename Bool => ns; rcases ns
    · simp at p; simp [FPChecker, denote]
      have : FixedAfter (z⁻¹ x) p <-> x p = (z⁻¹ x) p := by
        constructor <;> intro h
        · specialize h (p+1) (by omega)
          rw [<- h]; rfl
        · rcases p
          · rw [FixedAfter_delay_0]; funext n
            rw [hx, h]; simp; simp
          rw [FixedAfter_delay_succ]
          intro m hm; simp at h
          rename_i n; by_cases he: (m = n)
          rw [he]
          rw [<- h]; apply hx; omega
      tauto
    · rcases p with ⟨m, n⟩; simp at hx
      simp [FPChecker, denote]; tauto
  case loop c ih =>
    simp at ih; rename Bool => ns; rcases ns
    · simp at p; simp [FPChecker]
      constructor; rintro ⟨hf, he⟩











-- our goal is that
-- ∀ x, fix_checker c x = LocalFixedPoint c x
-- def LocalFix {ns: Bool}: (Ckt ns A B) -> (SOVType ns A) -> SOType ns Prop
--   | Ckt.node1 f => fun _ _ => True
--   | Ckt.node2 f => fun _ _ => True
--   | Ckt.const x => fun _ _ => True
--   | Ckt.id => liftO ns (fun _ => True)
--   | Ckt.fst => liftO ns (fun _ => True)
--   | Ckt.snd => liftO ns (fun _ => True)
--   | Ckt.add => liftO ns (fun _ => True)
--   | Ckt.sub => liftO ns (fun _ => True)
--   | Ckt.seq c1 c2 => fun x => let o := denote c1 x
--       match ns with
--       | false => fun n => (fix_checker c1 x n) ∧ (fix_checker c2 o n)
--       | true => fun m n => (fix_checker c1 x m n) ∧ (fix_checker c2 o m n)
--   | Ckt.par c1 c2 => fun x => sprodO ns (denote c1 x, denote c2 x)
--   | Ckt.delay => delay
--   | Ckt.lifting c => lifting (denote c)
--   | Ckt.loop c =>  fun a => fix (fun s => denote c (sprodO ns (a, z⁻¹ s)))
--   | Ckt.loop_lifted c => fun a => fix2 (fun s => denote c (sprod2 (a, ↑↑z⁻¹ s)))
--   | Ckt.bracket c _ => ↑↑∫0 ∘ denote c ∘ ↑↑δ0

end FPChecker

import DBSP.Circuits.Circuits
import DBSP.Practical.Sequiv
import DBSP.Practical.Refine
import DBSP.Practical.Preserve
open CktBasic

-- incrementalizable unary nodes
class IncUnary {A B} [BaseType A] [BaseType B] (f :@UnaryNode A B _ _) where
  opt: {ns: Bool} -> Ckt (VType.base A) (VType.base B) ns
  sequiv: ∀ ns, cΔ (c₁ f) ≃ @opt ns
  refine1: ∀ ns, (Ckt.node1 (ns:=ns) f) ↝₁ opt
  refine2: (c₁ f) ↝₂ opt

-- a default low-priority instance
-- the incremental version is simply unoptimized
instance (priority := low) {A B} [BaseType A] [BaseType B]
  (f :@UnaryNode A B _ _): IncUnary f where
  opt := cΔ (Ckt.node1 f)
  sequiv := by intro ns; rfl
  refine1 := by intro ns; apply Preserve1_incr
  refine2 := by apply Preserve2_incr

-- incrementalizable binary nodes
class IncBinary {A B C} [BaseType A] [BaseType B] [BaseType C] (f :@BinaryNode A B C _ _ _) where
  opt: {ns: Bool} -> Ckt (VType.base A ×ᵥ VType.base B) (VType.base C) ns
  sequiv: ∀ ns, cΔ (c₂ f) ≃ @opt ns
  refine1: ∀ ns, (Ckt.node2 (ns:=ns) f) ↝₁ opt
  refine2: (c₂ f) ↝₂ opt

-- a default low-priority instance
-- the incremental version is simply unoptimized
instance (priority := low) {A B C} [BaseType A] [BaseType B] [BaseType C]
  (f :@BinaryNode A B C _ _ _): IncBinary f where
  opt := cΔ (Ckt.node2 f)
  sequiv := by intro ns; rfl
  refine1 := by intro ns; apply Preserve1_incr
  refine2 := by apply Preserve2_incr

-- The recursive evidence for incrementalizability
inductive IncEvidence : ∀ {a b ns}, Ckt a b ns -> Type 1
  | node1 {A B: Type} [BaseType A] [BaseType B]
      (n: @UnaryNode A B _ _) [IncUnary n] :
    IncEvidence (Ckt.node1 n)
  | node2 {A B C: Type} [BaseType A] [BaseType B] [BaseType C]
      (n: @BinaryNode A B C _ _ _) [IncBinary n] :
    IncEvidence (Ckt.node2 n)
  | const {b: VType} (x: VType_interp b) : IncEvidence (Ckt.const x)
  | id : IncEvidence (Ckt.id)
  | fst : IncEvidence (Ckt.fst)
  | snd : IncEvidence (Ckt.snd)
  | add : IncEvidence (Ckt.add)
  | sub : IncEvidence (Ckt.sub)
  | seq {ns a b c} (c1 : Ckt a b ns) (c2 : Ckt b c ns) :
      IncEvidence c1 -> IncEvidence c2 -> IncEvidence (Ckt.seq c1 c2)
  | par {ns a b c} (c1 : Ckt a b ns) (c2 : Ckt a c ns) :
      IncEvidence c1 -> IncEvidence c2 -> IncEvidence (Ckt.par c1 c2)
  | delay : IncEvidence (Ckt.delay)
  | lifted_delay: IncEvidence (Ckt.lifted_delay)
  | lifting {a b} (c: Ckt a b 0) :
      IncEvidence c -> IncEvidence (Ckt.lifting c)
  | loop {ns a b} (c: Ckt (a ×ᵥ b) b ns):
      IncEvidence c -> IncEvidence (Ckt.loop c)
  | lifted_loop {a b} (c: Ckt (a ×ᵥ b) b 1):
      IncEvidence c -> IncEvidence (Ckt.lifted_loop c)
  | bracket {a b} (c: Ckt a b 1) :
      IncEvidence c -> IncEvidence (Ckt.bracket c)

-- incrementalizable circuits
class IncCkt {a b ns} (c : Ckt a b ns) where
  -- The evidence tree is data, not a proof
  evidence : IncEvidence c

-- automatic instance resolution
instance {ns A B} [BaseType A] [BaseType B]
  (n :@UnaryNode A B _ _) [IncUnary n] : IncCkt (Ckt.node1 (ns:=ns) n) := by
  repeat constructor

instance {ns A B C} [BaseType A] [BaseType B] [BaseType C]
  (n :@BinaryNode A B C _ _ _) [IncBinary n] : IncCkt (Ckt.node2 (ns:=ns) n) := by
  repeat constructor

instance {ns A}: IncCkt (@Ckt.id ns A) := by
  repeat constructor

instance {ns a b} (x: VType_interp b): IncCkt (@Ckt.const ns a b x) := by
  repeat constructor

instance {ns a b}: IncCkt (@Ckt.fst ns a b) := by
  repeat constructor

instance {ns a b}: IncCkt (@Ckt.snd ns a b) := by
  repeat constructor

instance {ns a}: IncCkt (@Ckt.add ns a) := by
  repeat constructor

instance {ns a}: IncCkt (@Ckt.sub ns a) := by
  repeat constructor

instance {ns a b c} (c1 : Ckt a b ns) (c2 : Ckt b c ns) [IncCkt c1] [IncCkt c2] : IncCkt (Ckt.seq c1 c2) :=
  ⟨IncEvidence.seq c1 c2 IncCkt.evidence IncCkt.evidence⟩

instance {ns a b c} (c1 : Ckt a b ns) (c2 : Ckt a c ns) [IncCkt c1] [IncCkt c2] : IncCkt (Ckt.par c1 c2) :=
  ⟨IncEvidence.par c1 c2 IncCkt.evidence IncCkt.evidence⟩

instance {ns a}: IncCkt (@Ckt.delay ns a) := by
  repeat constructor

instance {a}: IncCkt (@Ckt.lifted_delay a) := by
  repeat constructor

instance {a b} (c: Ckt a b 0) [IncCkt c] : IncCkt (Ckt.lifting c) :=
  ⟨IncEvidence.lifting c IncCkt.evidence⟩

instance {ns a b} (c: Ckt (a ×ᵥ b) b ns) [IncCkt c]: IncCkt (Ckt.loop c) :=
  ⟨IncEvidence.loop c IncCkt.evidence⟩

instance {a b}(c: Ckt (a ×ᵥ b) b 1) [IncCkt c]: IncCkt (Ckt.lifted_loop c) :=
  ⟨IncEvidence.lifted_loop c IncCkt.evidence⟩

instance {a b} (c: Ckt a b 1) [IncCkt c] : IncCkt (Ckt.bracket c) :=
  ⟨IncEvidence.bracket c IncCkt.evidence⟩

-- The incremental optimization algorithm helper function
def incOptOfEvidence {a b ns} {c: Ckt a b ns} (e: IncEvidence c) : Ckt a b ns :=
  match e with
  | IncEvidence.node1 n => IncUnary.opt n
  | IncEvidence.node2 n => IncBinary.opt n
  | IncEvidence.const x => Ckt.const x >>c cD
  | IncEvidence.id => Ckt.id
  | IncEvidence.fst => Ckt.fst
  | IncEvidence.snd => Ckt.snd
  | IncEvidence.add => Ckt.add
  | IncEvidence.sub => Ckt.sub
  | IncEvidence.seq _ _ h1 h2 => (incOptOfEvidence h1) >>c (incOptOfEvidence h2)
  | IncEvidence.par _ _ h1 h2 => (incOptOfEvidence h1) &&c (incOptOfEvidence h2)
  | IncEvidence.delay => Ckt.delay
  | IncEvidence.lifted_delay => Ckt.lifted_delay
  | IncEvidence.lifting c _ => cΔ (c↑ c)
  | IncEvidence.loop _ h => Ckt.loop (incOptOfEvidence h)
  | IncEvidence.lifted_loop _ h => Ckt.lifted_loop (incOptOfEvidence h)
  | IncEvidence.bracket _ h => Ckt.bracket (incOptOfEvidence h)

-- The incremental optimization algorithm
def incOpt {a b ns} (c: Ckt a b ns) [h: IncCkt c] : Ckt a b ns :=
  incOptOfEvidence h.evidence

namespace IncrementalizeProof
variable {ns: Bool} {A B: VType} (c: Ckt A B ns) [hic: IncCkt c]

-- We need a strong induction hypothesis to prove the correctness of `incOpt`
-- So we will construct an IH as the conjunction of three properties:
-- 1. Refinement
-- 2. Preservation of IntFP1
-- 3. Preservation of IntFP2Vec
-- Actually only 1 and 3 need to be inducted together with 2 could be proved separately, but for simplicity we do them together.
def IH {ns A B} {c: Ckt A B ns} (e: IncEvidence c) : Prop :=
  ((cΔ c) ⊑ (incOptOfEvidence e)) ∧ (c ↝₁ (incOptOfEvidence e)) ∧
    (match ns with
    | 0 => True
    | 1 => c ↝₂ (incOptOfEvidence e)
    )

-- Thus the following lemmas are merely for proof, not for use
lemma incOpt_induction {ns A B} {c: Ckt A B ns} (e: IncEvidence c):
    IH e:= by
  induction e <;> rename Bool => ns <;> simp [IH, incOptOfEvidence]
  case node1 h | node2 h =>
    constructor
    · apply Sequiv_to_Refine; apply h.sequiv
    constructor
    · apply h.refine1
    · cases ns <;> simp
      exact h.refine2
  case id | fst | snd | add | sub =>
    constructor
    · apply Sequiv_to_Refine
      try apply Sequiv_incr_id
      try apply Sequiv_incr_fst
      try apply Sequiv_incr_snd
      try apply Sequiv_incr_add
      try apply Sequiv_incr_sub
    constructor
    · try apply Preserve1_id
      try apply Preserve1_fst
      try apply Preserve1_snd
      try apply Preserve1_add
      try apply Preserve1_sub
    · cases ns <;> simp
      try apply Preserve2_id
      try apply Preserve2_fst
      try apply Preserve2_snd
      try apply Preserve2_add
      try apply Preserve2_sub
  case const =>
    constructor
    · apply Sequiv_to_Refine
      apply Sequiv_incr_const
    constructor
    · apply Preserve1_const
    · cases ns <;> simp
      apply Preserve2_const
  case seq ih1 ih2 =>
    simp [IH] at ih1 ih2
    constructor
    · apply Refine_trans
      apply Sequiv_to_Refine
      apply Sequiv_incr_seq
      apply Refine_seq
      exact ih1.1
      exact ih2.1
    constructor
    · apply Preserve1_seq
      exact ih1.2.1
      exact ih2.2.1
      exact ih1.1
    · cases ns <;> simp [incOptOfEvidence]
      simp at ih1 ih2
      apply Preserve2_seq
      exact ih1.2.2
      exact ih2.2.2
      exact ih1.1
  case par ih1 ih2 =>
    simp [IH] at ih1 ih2
    constructor
    · apply Refine_trans
      apply Sequiv_to_Refine
      apply Sequiv_incr_par
      apply Refine_par
      exact ih1.1
      exact ih2.1
    constructor
    · apply Preserve1_par
      exact ih1.2.1
      exact ih2.2.1
    · cases ns <;> simp [incOptOfEvidence]
      simp at ih1 ih2
      apply Preserve2_par
      exact ih1.2.2
      exact ih2.2.2
  case delay =>
    constructor
    · apply Sequiv_to_Refine
      apply Sequiv_incr_delay
    constructor
    · apply Preserve1_delay
    · cases ns <;> simp
      apply Preserve2_delay
  case lifted_delay =>
    constructor
    · apply Sequiv_to_Refine
      apply Sequiv_incr_lifted_delay
    constructor
    · apply Preserve1_lifted_delay
    · apply Preserve2_lifted_delay
  case lifting =>
    constructor
    · rfl
    constructor
    · apply Preserve1_incr
    · apply Preserve2_incr
  case loop ih =>
    simp [IH] at ih
    constructor
    · apply Refine_incr_loop
      exact ih.1
    constructor
    · apply Preserve1_loop
      exact ih.2.1
      exact ih.1
    · cases ns <;> simp [incOptOfEvidence]
      simp at ih
      apply Preserve2_loop
      exact ih.2.2
      exact ih.1
  case lifted_loop ih =>
    simp [IH] at ih
    constructor
    · apply Refine_incr_loop2
      exact ih.1
    constructor
    · apply Preserve1_lifted_loop
      exact ih.2.1
      exact ih.1
    · apply Preserve2_lifted_loop
      exact ih.2.2
      exact ih.1
  case bracket ih =>
    simp [IH] at ih
    constructor
    · apply Refine_incOpt_bracket
      exact ih.1
      exact ih.2.2
    · apply Preserve1_bracket
      exact ih.2.1

lemma incOpt_correctness:
    ((cΔ c) ⊑ (incOpt c)) ∧ (c ↝₁ (incOpt c)) ∧
    (match ns, c, hic with
    | 0, _, _ => True
    | 1, c1, _ => c1 ↝₂ (incOpt c1)
    ):= by
  have h := incOpt_induction hic.evidence
  simp [IH] at h
  simp [incOpt]
  constructor
  · exact h.1
  constructor
  · exact h.2.1
  · cases ns
    · trivial
    · exact h.2.2

end IncrementalizeProof

theorem incOpt_Refine {ns A B} (c: Ckt A B ns) [hic: IncCkt c] :
    (cΔ c) ⊑ (incOpt c) := by
  have h := IncrementalizeProof.incOpt_correctness c
  exact h.1

theorem incOpt_Preserve1 {ns A B} (c: Ckt A B ns) [hic: IncCkt c] :
    c ↝₁ (incOpt c) := by
  have h := IncrementalizeProof.incOpt_correctness c
  exact h.2.1

theorem incOpt_Preserve2 {A B} (c: Ckt A B 1) [hic: IncCkt c] :
    c ↝₂ (incOpt c) := by
  have h := IncrementalizeProof.incOpt_correctness c
  simp at h; tauto

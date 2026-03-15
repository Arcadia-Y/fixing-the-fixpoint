import DBSP.Circuits.Circuits
import DBSP.Practical.Sequiv
import DBSP.Practical.ConvEq
import DBSP.Practical.Preserve
open CktBasic

-- `c2` is a sound incremental form of `c1`
structure SoundIncr {a b ns} (c1 c2: Ckt a b ns) where
  conv: (cΔ c1) ≋ c2
  preserve1: c1 ↝₁ c2
  preserve2: match ns with
    | false => True
    | true => c1 ↝₂ c2
  preserveIC: c1 ↝c c2

-- incrementalizable unary nodes
class IncUnary {A B} [BaseType A] [BaseType B] (f :@UnaryNode A B _ _) where
  opt: {ns: Bool} -> Ckt (VType.base A) (VType.base B) ns
  sound: ∀ ns, SoundIncr (Ckt.node1 (ns:=ns) f) (@opt ns)

-- a default low-priority instance
-- the incremental version is simply unoptimized
instance (priority := low) IncUnaryDefault
  {A B} [BaseType A] [BaseType B]
  (f: UnaryNode A B): IncUnary f where
  opt := cΔ (Ckt.node1 f)
  sound := by
    intro ns
    exact ⟨by rfl, by apply Preserve1_incr, by cases ns <;> simp; apply Preserve2_incr, by apply IntConv_cΔ⟩

-- linear unary functions
instance IncUnaryLinear
  {A B} [BaseType A] [BaseType B]
  (un: UnaryNode A B)
  (hfl: ∀ x y, un.f (x + y) = un.f x + un.f y):
    IncUnary un where
  opt := c₁ un
  sound := by
    intro ns
    exact ⟨by apply Sequiv_to_ConvEq; apply Sequiv_incr_linear_node1; tauto,
      by apply Preserve1_node1_self,
      by cases ns <;> simp; apply Preserve2_node1_self,
      by intro x hx; simp [IntConv]⟩

-- incrementalizable binary nodes
class IncBinary {A B C} [BaseType A] [BaseType B] [BaseType C] (f :BinaryNode A B C) where
  opt: {ns: Bool} -> Ckt (VType.base A ×ᵥ VType.base B) (VType.base C) ns
  sound: ∀ ns, SoundIncr (Ckt.node2 (ns:=ns) f) (@opt ns)

-- a default low-priority instance
-- the incremental version is simply unoptimized
instance (priority := low) IncBinaryDefault
  {A B C} [BaseType A] [BaseType B] [BaseType C]
  (f :BinaryNode A B C): IncBinary f where
  opt := cΔ (Ckt.node2 f)
  sound := by
    intro ns
    exact ⟨by rfl,  by apply Preserve1_incr, by cases ns <;> simp; apply Preserve2_incr, by apply IntConv_cΔ⟩

-- linear binary functions
instance IncBinaryLinear
  {A B C} [BaseType A] [BaseType B] [BaseType C]
  (bn: BinaryNode A B C)
  (hfl: ∀ x y, bn.f (x + y) = bn.f x + bn.f y):
    IncBinary bn where
  opt := c₂ bn
  sound := by
    intro ns
    exact ⟨by apply Sequiv_to_ConvEq; apply Sequiv_incr_linear_node2; tauto,
      by apply Preserve1_node2_self,
      by cases ns <;> simp; apply Preserve2_node2_self,
      by intro x hx; simp [IntConv],⟩

-- bilinear binary functions
instance IncBinaryBilinear
  {A B C} [BaseType A] [BaseType B] [BaseType C]
  (bn: BinaryNode A B C)
  (hb1: ∀ x y z, bn.f (x+y, z) = bn.f (x, z) + bn.f (y, z))
  (hb2: ∀ x y z, bn.f (x, y+z) = bn.f (x, y) + bn.f (x, z)):
    IncBinary bn where
  opt := bilinear_opt (c₂ bn)
  sound := by
    intro ns
    exact ⟨by apply Sequiv_to_ConvEq; apply Sequiv_incr_bilinear_node2 <;> tauto,
      by apply Preserve1_node2_bilinear,
      by cases ns <;> simp; apply Preserve2_node2_bilinear,
      by intro x hx; simp[IntConv, bilinear_opt],⟩

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

instance {ns a}: IncCkt (@cD a ns) := by
  unfold cD; infer_instance

instance {ns a}: IncCkt (@cI a ns) := by
  unfold cI; infer_instance

instance {a}: IncCkt (@lifted_I a) := by
  unfold lifted_I; infer_instance

instance {a}: IncCkt (@lifted_D a) := by
  unfold lifted_D; infer_instance

-- The incremental optimization algorithm helper function
@[simp]
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

-- simp lemmas to make `incOpt` compute by structure, without exposing evidence
@[simp] lemma incOpt_node1 {ns A B} [BaseType A] [BaseType B]
  (n : @UnaryNode A B _ _) [IncUnary n] :
  incOpt (Ckt.node1 (ns:=ns) n) = IncUnary.opt n := by
  rfl

@[simp] lemma incOpt_node2 {ns A B C} [BaseType A] [BaseType B] [BaseType C]
  (n : @BinaryNode A B C _ _ _) [IncBinary n] :
  incOpt (Ckt.node2 (ns:=ns) n) = IncBinary.opt n := by
  rfl

@[simp] lemma incOpt_const {ns a b} (x: VType_interp b) :
  incOpt (@Ckt.const ns a b x) = Ckt.const x >>c cD := by
  rfl

@[simp] lemma incOpt_id {ns A} :
  incOpt (@Ckt.id ns A) = Ckt.id := by
  rfl

@[simp] lemma incOpt_fst {ns a b} :
  incOpt (@Ckt.fst ns a b) = Ckt.fst := by
  rfl

@[simp] lemma incOpt_snd {ns a b} :
  incOpt (@Ckt.snd ns a b) = Ckt.snd := by
  rfl

@[simp] lemma incOpt_add {ns a} :
  incOpt (@Ckt.add ns a) = Ckt.add := by
  rfl

@[simp] lemma incOpt_sub {ns a} :
  incOpt (@Ckt.sub ns a) = Ckt.sub := by
  rfl

@[simp] lemma incOpt_seq {ns a b c} (c1 : Ckt a b ns) (c2 : Ckt b c ns)
  [IncCkt c1] [IncCkt c2] :
  incOpt (Ckt.seq c1 c2) = (incOpt c1) >>c (incOpt c2) := by
  rfl

@[simp] lemma incOpt_par {ns a b c} (c1 : Ckt a b ns) (c2 : Ckt a c ns)
  [IncCkt c1] [IncCkt c2] :
  incOpt (Ckt.par c1 c2) = ((incOpt c1) &&c (incOpt c2)) := by
  rfl

@[simp] lemma incOpt_delay {ns a} :
  incOpt (@Ckt.delay ns a) = Ckt.delay := by
  rfl

@[simp] lemma incOpt_lifted_delay {a} :
  incOpt (@Ckt.lifted_delay a) = Ckt.lifted_delay := by
  rfl

@[simp] lemma incOpt_lifting {a b} (c: Ckt a b 0) [IncCkt c] :
  incOpt (Ckt.lifting c) = cΔ (c↑ c) := by
  rfl

@[simp] lemma incOpt_loop {ns a b} (c: Ckt (a ×ᵥ b) b ns) [IncCkt c] :
  incOpt (Ckt.loop c) = Ckt.loop (incOpt c) := by
  rfl

@[simp] lemma incOpt_lifted_loop {a b} (c: Ckt (a ×ᵥ b) b 1) [IncCkt c] :
  incOpt (Ckt.lifted_loop c) = Ckt.lifted_loop (incOpt c) := by
  rfl

@[simp] lemma incOpt_bracket {a b} (c: Ckt a b 1) [IncCkt c] :
  incOpt (Ckt.bracket c) = Ckt.bracket (incOpt c) := by
  rfl

namespace IncrementalizeProof
variable {ns: Bool} {A B: VType} (c: Ckt A B ns) [hic: IncCkt c]

-- The correctness of `incOpt` by induction on the evidence tree.
lemma incOpt_induction {ns A B} {c: Ckt A B ns} (e: IncEvidence c):
    SoundIncr c (incOptOfEvidence e) := by
  induction e <;> rename Bool => ns <;> simp [incOptOfEvidence]
  case node1 h | node2 h =>
    exact h.sound ns
  case id | fst | snd | add | sub =>
    exact {
      conv := by apply Sequiv_to_ConvEq
                 try apply Sequiv_incr_id
                 try apply Sequiv_incr_fst
                 try apply Sequiv_incr_snd
                 try apply Sequiv_incr_add
                 try apply Sequiv_incr_sub,
      preserve1 := by try apply Preserve1_id
                      try apply Preserve1_fst
                      try apply Preserve1_snd
                      try apply Preserve1_add
                      try apply Preserve1_sub,
      preserve2 := by cases ns <;> simp
                      try apply Preserve2_id
                      try apply Preserve2_fst
                      try apply Preserve2_snd
                      try apply Preserve2_add
                      try apply Preserve2_sub,
      preserveIC := by
        intro x hx
        simp [IntConv]
    }
  case const =>
    exact {
      conv := by apply Sequiv_to_ConvEq; apply Sequiv_incr_const,
      preserve1 := by apply Preserve1_const,
      preserve2 := by cases ns <;> simp; apply Preserve2_const,
      preserveIC := by
        intro x hx
        simp [IntConv]
    }
  case seq ih1 ih2 =>
    exact {
      conv := by apply ConvEq_trans
                 apply Sequiv_to_ConvEq; apply Sequiv_incr_seq
                 apply ConvEq_seq
                 exact ih1.conv
                 exact ih2.conv,
      preserve1 := by apply Preserve1_seq
                      exact ih1.preserve1
                      exact ih2.preserve1
                      exact ih1.conv,
      preserve2 := by cases ns <;> simp [incOptOfEvidence]
                      apply Preserve2_seq
                      exact ih1.preserve2
                      exact ih2.preserve2
                      exact ih1.conv,
      preserveIC := by
        apply PreserveIC_seq
        · exact ih1.preserveIC
        · exact ih2.preserveIC
        · exact ih1.conv
    }
  case par ih1 ih2 =>
    exact {
      conv := by apply ConvEq_trans
                 apply Sequiv_to_ConvEq; apply Sequiv_incr_par
                 apply ConvEq_par
                 exact ih1.conv
                 exact ih2.conv,
      preserve1 := by apply Preserve1_par
                      exact ih1.preserve1
                      exact ih2.preserve1,
      preserve2 := by cases ns <;> simp [incOptOfEvidence]
                      apply Preserve2_par
                      exact ih1.preserve2
                      exact ih2.preserve2,
      preserveIC := by
        apply PreserveIC_par
        · exact ih1.preserveIC
        · exact ih2.preserveIC
    }
  case delay =>
    exact {
      conv := by apply Sequiv_to_ConvEq; apply Sequiv_incr_delay,
      preserve1 := by apply Preserve1_delay,
      preserve2 := by cases ns <;> simp; apply Preserve2_delay,
      preserveIC := by
        intro x hx
        simp [IntConv]
    }
  case lifted_delay =>
    exact {
      conv := by apply Sequiv_to_ConvEq; apply Sequiv_incr_lifted_delay,
      preserve1 := by apply Preserve1_lifted_delay,
      preserve2 := by apply Preserve2_lifted_delay,
      preserveIC := by
        intro x hx
        simp [IntConv]
    }
  case lifting =>
    exact {
      conv := by rfl,
      preserve1 := by apply Preserve1_incr,
      preserve2 := by apply Preserve2_incr,
      preserveIC := by
        intro x hx
        exact IntConv_cΔ hx
    }
  case loop c e ih =>
    exact {
      conv := by apply ConvEq_incr_loop; exact ih.conv,
      preserve1 := by apply Preserve1_loop
                      exact ih.preserve1
                      apply ConvEq_incr_loop
                      exact ih.conv,
      preserve2 := by cases ns <;> simp [incOptOfEvidence]
                      apply Preserve2_loop
                      exact ih.preserve2
                      apply ConvEq_incr_loop
                      exact ih.conv,
      preserveIC := by
        apply PreserveIC_loop
        · exact ih.preserveIC
        · apply ConvEq_incr_loop
          exact ih.conv
    }
  case lifted_loop c e ih =>
    exact {
      conv := by apply ConvEq_incr_loop2; exact ih.conv,
      preserve1 := by apply Preserve1_lifted_loop
                      exact ih.preserve1
                      apply ConvEq_incr_loop2
                      exact ih.conv,
      preserve2 := by apply Preserve2_lifted_loop
                      exact ih.preserve2
                      apply ConvEq_incr_loop2
                      exact ih.conv,
      preserveIC := by
        apply PreserveIC_lifted_loop
        · exact ih.preserveIC
        · apply ConvEq_incr_loop2
          exact ih.conv
    }
  case bracket c e ih =>
    exact {
      conv := by apply ConvEq_incOpt_bracket
                 exact ih.conv
      preserve1 := by apply Preserve1_bracket; exact ih.preserve1,
      preserve2 := by trivial,
      preserveIC := by
        apply PreserveIC_bracket
        · exact ih.preserveIC
        · exact ih.conv
        · exact ih.preserve2
    }

lemma incOpt_correctness:
    SoundIncr c (incOpt c) := by
  have h := incOpt_induction hic.evidence
  simp [incOpt]; exact h

end IncrementalizeProof

theorem incOpt_ConvEq {ns A B} (c: Ckt A B ns) [hic: IncCkt c] :
    (cΔ c) ≋ (incOpt c) := by
  have h := IncrementalizeProof.incOpt_correctness c
  exact h.conv

theorem incOpt_Preserve1 {ns A B} (c: Ckt A B ns) [hic: IncCkt c] :
    c ↝₁ (incOpt c) := by
  have h := IncrementalizeProof.incOpt_correctness c
  exact h.preserve1

theorem incOpt_Preserve2 {A B} (c: Ckt A B 1) [hic: IncCkt c] :
    c ↝₂ (incOpt c) := by
  have h := IncrementalizeProof.incOpt_correctness c
  exact h.preserve2

theorem incOpt_PreserveIC {ns A B} (c: Ckt A B ns) [hic: IncCkt c] :
  c ↝c (incOpt c) := by
  have h := IncrementalizeProof.incOpt_correctness c
  exact h.preserveIC

@[simp]
lemma incOpt_I {ns A}:
    incOpt (@cI A ns) = cI := rfl

@[simp]
lemma incOpt_D {ns A}:
    incOpt (@cD A ns) = cD := rfl

@[simp]
lemma incOpt_lifted_I {A}:
    incOpt (@lifted_I A) = c↑I := rfl

@[simp]
lemma incOpt_lifted_D {A}:
    incOpt (@lifted_D A) = c↑D := rfl

theorem incOpt_IntConv {ns A B}
  (c: Ckt A B ns) [hic: IncCkt c]
  {x} (ht: IntConv c x):
    IntConv (incOpt c) (D x) := by
  exact incOpt_PreserveIC c x ht

theorem incOpt_ExtConv_iff {ns a b}
  (c: Ckt a b ns) [hic: IncCkt c] {x}:
    ExtConv c x <-> ExtConv (incOpt c) (D x) := by
  rw [<- (incOpt_ConvEq c).conv]
  simp [cΔ, ExtConv, denote]

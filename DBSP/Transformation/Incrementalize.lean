import DBSP.Circuits.Circuits_v6
open CktBasic

-- incrementalizable unary nodes
class IncUnary {A B} [BaseType A] [BaseType B] (n :@UnaryNode A B _ _) where
  opt: {ns: Bool} -> Ckt (VType.base A) (VType.base B) ns

-- incrementalizable binary nodes
class IncBinary {A B C} [BaseType A] [BaseType B] [BaseType C] (n :@BinaryNode A B C _ _ _) where
  opt: {ns: Bool} -> Ckt (VType.base A ×ᵥ VType.base B) (VType.base C) ns

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
  | lifting {a b} (c: Ckt a b 0) :
      IncEvidence c -> IncEvidence (Ckt.lifting c)
  | loop {ns a b} (c: Ckt (a ×ᵥ b) b ns):
      IncEvidence c -> IncEvidence (Ckt.loop c)
  | loop_lifted {a b} (c: Ckt (a ×ᵥ b) b 1):
      IncEvidence c -> IncEvidence (Ckt.loop_lifted c)
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

instance {a b} (c: Ckt a b 0) [IncCkt c] : IncCkt (Ckt.lifting c) :=
  ⟨IncEvidence.lifting c IncCkt.evidence⟩

instance {ns a b} (c: Ckt (a ×ᵥ b) b ns) [IncCkt c]: IncCkt (Ckt.loop c) :=
  ⟨IncEvidence.loop c IncCkt.evidence⟩

instance {a b}(c: Ckt (a ×ᵥ b) b 1) [IncCkt c]: IncCkt (Ckt.loop_lifted c) :=
  ⟨IncEvidence.loop_lifted c IncCkt.evidence⟩

instance {a b} (c: Ckt a b 1) [IncCkt c] : IncCkt (Ckt.bracket c) :=
  ⟨IncEvidence.bracket c IncCkt.evidence⟩

-- The incremental optimization algorithm
def incOpt {a b ns} (c: Ckt a b ns) [h: IncCkt c] : Ckt a b ns:=
  match h.evidence with
  | IncEvidence.node1 n => IncUnary.opt n
  | IncEvidence.node2 n => IncBinary.opt n
  | IncEvidence.const x => Ckt.const x >>c cD
  | IncEvidence.id => Ckt.id
  | IncEvidence.fst => Ckt.fst
  | IncEvidence.snd => Ckt.snd
  | IncEvidence.add => Ckt.add
  | IncEvidence.sub => Ckt.sub
  | IncEvidence.seq c1 c2 h1 h2 => (incOpt c1 (h:=⟨h1⟩)) >>c (incOpt c2 (h:=⟨h2⟩))
  | IncEvidence.par c1 c2 h1 h2 => (incOpt c1 (h:=⟨h1⟩)) &&c (incOpt c2 (h:=⟨h2⟩))
  | IncEvidence.delay => Ckt.delay
  | IncEvidence.lifting c _ => cΔ (c↑ c)
  | IncEvidence.loop c h => Ckt.loop (incOpt c (h:=⟨h⟩))
  | IncEvidence.loop_lifted c h => Ckt.loop_lifted (incOpt c (h:=⟨h⟩))
  | IncEvidence.bracket c h => Ckt.bracket (incOpt c (h:=⟨h⟩))

-- Specification for termination, or streaming progress
import DBSP.Circuits.Circuits
open CktBasic

-- Fixpoint Specification
-- for the outer iteration, i.e. the **1st** time dimension
section FPSpec1
variable {A B C: VType}

def FixedAfter1 {T: Type} (s: stream T) (n: ℕ): Prop :=
  ∀ m ≥ n, s m = s n

-- For any circuit, the External Fixpoint is
--   an index `n` of the outer stream such that
--   after `n` both the input and output of the circuit become fixed.
-- For the nested circuit, `n` is a column index,
--   and "fixed" means that the same stream repeats after `n`,
--   not that a single value repeats after `n`.
def ExtFP1 {ns: Bool} (c: Ckt A B ns) (x: SOVType ns A) (n: ℕ): Prop :=
  FixedAfter1 x n ∧ FixedAfter1 (denote c x) n

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
  | Ckt.lifted_delay => ExtFP1 Ckt.lifted_delay x n
  -- For `c↑ c`, since the internal circuit doesn't have across-iteration states,
  -- thus the Internal Fixpoint is simply the External Fixpoint
  | Ckt.lifting c => ExtFP1 (Ckt.lifting c) x n
  | Ckt.loop c =>  IntFP1 c (sprodO ns (x, z⁻¹ (denote (Ckt.loop c) x))) n
  | Ckt.lifted_loop c => IntFP1 c (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.lifted_loop c) x))) n
  | Ckt.bracket c => IntFP1 c (↑↑δ0 x) n

end FPSpec1

-- Fixedpoint checking theory
-- for the inner iteration, i.e. the **2nd** time dimension
section FPSpec2
variable {A B C: VType}
-- FixedAfter2 is like FixedAfter1 but for a row of a nested stream
def FixedAfter2 {T: Type} (s: stream (stream T)) (m n: ℕ): Prop :=
  FixedAfter1 (s m) n

-- For nested circuits,
-- the nested External Fixpoint is a point `(m, n)`,
-- such that in row `m`, both the input and output become fixed after column `n`.
def ExtFP2 {A B: VType} (c: Ckt A B 1) (x: SOVType 1 A) (m: ℕ) (n: ℕ): Prop :=
  FixedAfter2 x m n ∧ FixedAfter2 (denote c x) m n

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
  | Ckt.lifted_delay => ExtFP2 Ckt.lifted_delay x m n
  -- This is where `IntFP2` depends on `IntFP1`
  -- For `c↑ c`, the nested Internal Fixpoint is `(m, n)` means that
  -- the Internal Fixpoint of `c` on input `x m` is `n`
  | Ckt.lifting c => IntFP1 c (x m) n
  | Ckt.loop c =>  IntFP2 c (sprod2 (x, z⁻¹ (denote (Ckt.loop c) x))) m n
  | Ckt.lifted_loop c => IntFP2 c (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.lifted_loop c) x))) m n

-- The vetorized version of FixedAfter2
def FixedAfter2Vec {T: Type} (s: stream (stream T)) (b: stream ℕ): Prop :=
  ∀ i, FixedAfter2 s i (b i)

-- The vectorized version of ExtFP2
def ExtFP2Vec (c: Ckt A B 1) (x: SOVType 1 A) (b: stream ℕ): Prop :=
  ∀ i, ExtFP2 c x i (b i)

-- The vectorized version of IntFP2
def IntFP2Vec (c: Ckt A B 1) (x: SOVType 1 A) (b: stream ℕ): Prop :=
  ∀ i, IntFP2 c x i (b i)

def ZeroAfterVec {A: Type} [Zero A] (x:  stream (stream A)) (b: stream ℕ): Prop :=
  ∀ i, ZeroAfter (x i) (b i)

-- Termination (Streaming Progress) Specification
-- `Terminate c x` means that circuit `c` will always terminate when computing any finite prefix of the output on input `x`
def Terminate {ns: Bool} {A B: VType} (c: Ckt A B ns) (x: SOVType ns A): Prop :=
  match c with
  -- the core definition
  | Ckt.bracket c =>
      Terminate c (↑↑δ0 x) ∧
      ∃ b, IntFP2Vec c (↑↑δ0 x) b ∧ ZeroAfterVec (denote c (↑↑δ0 x)) b
  -- other structural constructs
  | Ckt.seq c1 c2 => Terminate c1 x ∧ Terminate c2 (denote c1 x)
  | Ckt.par c1 c2 => Terminate c1 x ∧ Terminate c2 x
  | Ckt.lifting c => ∀ j, Terminate c (x j)
  | Ckt.loop c =>  Terminate c (sprodO ns (x, z⁻¹ (denote (Ckt.loop c) x)))
  | Ckt.lifted_loop c => Terminate c (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.lifted_loop c) x)))
  -- all other primitive nodes are terminating
  | _ => true

end FPSpec2

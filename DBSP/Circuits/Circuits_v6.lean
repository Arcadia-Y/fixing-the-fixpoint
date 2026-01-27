-- The formal definition of the DBSP language, i.e. well-formed circuits
import DBSP.StreamTheory.Operators
import DBSP.StreamTheory.Stream
import DBSP.StreamTheory.Linear
import DBSP.Circuits.PSType
import DBSP.StreamTheory.StreamElim

namespace CktBasic

-- BaseType with Abelian group structure
class BaseType (T:Type) where
  has_group: AddCommGroup T
  size: T -> ℕ
  add_cost: T × T -> ℕ
  sub_cost: T × T -> ℕ

instance (T: Type) [BaseType T]: AddCommGroup T :=
  BaseType.has_group

-- the type of the basetype values with Cartesian product
inductive VType: Type 1 where
  | base (T: Type) [BaseType T]: VType
  | prod (a b: VType) : VType

macro "[" t:term "]v" : term => `(VType.base $t)

notation a "×ᵥ" b :30 => VType.prod a b

@[reducible]
def VType_interp (a: VType): Type :=
  match a with
  | VType.base T => T
  | VType.prod a b => VType_interp a × VType_interp b

@[reducible]
def VType_struct (T: Type) (a: VType): PType T :=
  match a with
  | VType.base _ => PType.base
  | VType.prod a b => PType.prod (VType_struct T a) (VType_struct T b)

@[reducible]
def VType_Nat (a: VType) : Type :=
  PType_interp (VType_struct ℕ a)

instance VType_Nat_AddCancelCommMonoid (a: VType) : AddCancelCommMonoid (VType_Nat a) :=
  by infer_instance

instance stream_VType_Nat_AddCancelCommMonoid (a: VType) : AddCancelCommMonoid (stream (VType_Nat a)) :=
  by infer_instance

@[simp]
def VType_size {A: VType}: (VType_interp A) -> (VType_Nat A) :=
  match A with
  | VType.base _ => BaseType.size
  | VType.prod _ _ => fun x => (VType_size x.fst, VType_size x.snd)

instance VType_interp_Group (a: VType) : AddCommGroup (VType_interp a) :=
  match a with
  | VType.base T => by infer_instance
  | VType.prod a b => by haveI := VType_interp_Group a; haveI := VType_interp_Group b; infer_instance

-- Primitive node structure
structure UnaryNode {A B: Type} [BaseType A] [BaseType B] where
  f: A -> B
  -- The cost of the operation is assumed to be bounded by `cost`
  cost: A -> ℕ

structure BinaryNode {A B C: Type} [BaseType A] [BaseType B] [BaseType C] where
  f: (A × B) -> C
  -- The cost of the operation is assumed to be bounded by `cost`
  cost: A × B -> ℕ

-- Indexed-Type Well-Formed Circuit
-- `Ckt a b ns` is a circuit with input type `a` and output type `b`
-- `ns` indicates whether the circuit is on nested streams
inductive Ckt: VType -> VType -> Bool -> Type 1
  -- primitive nodes (ns = 0 means ↑node, ns = 1 means ↑↑node)
  | node1 {ns} {A B: Type} [BaseType A] [BaseType B] (f: @UnaryNode A B _ _) :
      Ckt (VType.base A) (VType.base B) ns
  | node2 {ns} {A B C: Type} [BaseType A] [BaseType B] [BaseType C]
      (f: @BinaryNode A B C _ _ _) : Ckt (VType.base A ×ᵥ VType.base B) (VType.base C) ns
  -- constant
  | const {ns} {a b: VType} (x: VType_interp b) : Ckt a b ns
  -- product combinators
  | id {ns} {a: VType} : Ckt a a ns
  | fst {ns} {a b: VType} : Ckt (a ×ᵥ b) a ns
  | snd {ns} {a b: VType} : Ckt (a ×ᵥ b) b ns
  -- group operations
  | add {ns} {a: VType} : Ckt (a ×ᵥ a) a ns
  | sub {ns} {a: VType} : Ckt (a ×ᵥ a) a ns
  -- sequential composition
  | seq {ns a b c} (c1 : Ckt a b ns) (c2 : Ckt b c ns) : Ckt a c ns
  -- parallel composition
  | par {ns a b c} (c1 : Ckt a b ns) (c2 : Ckt a c ns) : Ckt a (b ×ᵥ c) ns
  -- delay
  | delay {ns a} : Ckt a a ns
  -- lifted delay
  | lifted_delay {a} : Ckt a a 1
  -- lifting
  | lifting {a b} (c: Ckt a b 0) : Ckt a b 1
  -- feedback loop with normal delay
  | loop {ns a b} (c: Ckt (a ×ᵥ b) b ns): Ckt a b ns
  -- loop with lifted delay (delay by column)
  | lifted_loop {a b} (c: Ckt (a ×ᵥ b) b 1): Ckt a b 1
  -- stream introduction and elimination
  | bracket {a b} (c: Ckt a b 1) : Ckt a b 0

--- Notation for circuits
-- Sequential Composition
infixl:60 " >>c "  => Ckt.seq
-- Parallel Composition
infixl:50 " &&c " => Ckt.par

notation "cconst " x => Ckt.const x
notation "cid" => Ckt.id
notation "c1st" => Ckt.fst
notation "c2nd" => Ckt.snd
notation:max "c↑ " c:max => Ckt.lifting c
notation "cz⁻¹" => Ckt.delay
notation "c↑z⁻¹" => Ckt.lifted_delay
notation "cloop " c:max => Ckt.loop c
notation "cloop2 " c:max => Ckt.lifted_loop c
notation:max "c₁ " f => Ckt.node1 f
notation:max "c₂ " f => Ckt.node2 f
notation "cbracket " => Ckt.bracket
notation "cadd" => Ckt.add
notation "csub" => Ckt.sub

-- Polymorphic lifting w.r.t. nested streams
def liftO (ns: Bool) {a b: Type} (f: a -> b): Operator (Optstream ns a) (Optstream ns b) :=
  match ns with
  | false => ↑↑ f
  | true => ↑↑↑↑ f

def sprodO (ns: Bool) {a b: Type} (x: stream (Optstream ns a) × stream (Optstream ns b)): stream (Optstream ns (a × b)) :=
  match ns with
  | false => sprod (x.1, x.2)
  | true => sprod2 (x.1, x.2)

@[simp]
lemma liftO_false {a b: Type} (f: a -> b) (x: stream (Optstream false a)):
    liftO false f x = ↑↑ f x := by rfl

@[simp]
lemma liftO_true {a b: Type} (f: a -> b) (x: stream (Optstream true a)):
    liftO true f x = ↑↑↑↑ f x := by rfl

@[simp]
lemma sprodO_false {a b: Type} (x: stream (Optstream false a) × stream (Optstream false b)):
    sprodO false x = sprod (x.1, x.2) := by rfl

@[simp]
lemma sprodO_true {a b: Type} (x: stream (Optstream true a) × stream (Optstream true b)):
    sprodO true x = sprod2 (x.1, x.2) := by rfl

@[simp]
lemma liftO_fst_sprodO (ns: Bool) {a b: Type} (x: stream (Optstream ns a) × stream (Optstream ns b)):
    (liftO ns Prod.fst) (sprodO ns x) = x.1 := by
  rcases ns <;> rfl

@[simp]
lemma liftO_snd_sprodO (ns: Bool) {a b: Type} (x: stream (Optstream ns a) × stream (Optstream ns b)):
    (liftO ns Prod.snd) (sprodO ns x) = x.2 := by
  rcases ns <;> rfl

@[simp]
lemma lift_fst_sprod (a b: Type) (x: stream a × stream b):
    (↑↑ Prod.fst) (sprod x) = x.1 := by rfl

@[simp]
lemma lift_snd_sprod (a b: Type) (x: stream a × stream b):
    (↑↑ Prod.snd) (sprod x) = x.2 := by rfl

lemma liftO_id (ns: Bool) {a: Type}:
    liftO ns (@id a) = id := by
  funext x
  rcases ns <;> rfl

-- Type abbreviations
@[reducible]
def OVType (ns: Bool) (A: VType) :=
  Optstream ns (VType_interp A)
@[reducible]
def SOType (ns: Bool) (T: Type) :=
  stream (Optstream ns T)
@[reducible]
def SOVType (ns: Bool) (A: VType) :=
  SOType ns (VType_interp A)

@[simp]
lemma OVType_false (A: VType):
    OVType false A = VType_interp A := by rfl
@[simp]
lemma OVType_true (A: VType):
    OVType true A = stream (VType_interp A) := by rfl
@[simp]
lemma SOVType_false (A: VType):
    SOVType false A = stream (VType_interp A) := by rfl
@[simp]
lemma SOVType_true (A: VType):
    SOVType true A = stream (stream (VType_interp A)) := by rfl
@[simp]
lemma SOVType_1 (A: VType):
    SOVType 1 A = stream (stream (VType_interp A)) := by rfl
@[simp]
lemma SOType_false (T: Type):
    SOType false T = stream T := by rfl
@[simp]
lemma SOType_true (T: Type):
    SOType true T = stream (stream T) := by rfl

-- Type of the denotational semantics of circuits
-- both input and output types are streams
-- `ns` denotes whether the circuit is nested
@[reducible, simp]
def DenoteType (ns: Bool) (a b: VType) :=
  Operator (OVType ns a) (OVType ns b)

-- denotational semantics of circuits
-- the semantics is "partial" w.r.t. termination
-- `denote c x = y` denotes that if `c` terminates on input `x` then the output is `y`
noncomputable def denote {a b: VType} {ns: Bool}: (Ckt a b ns) -> DenoteType ns a b
  | Ckt.node1 f => liftO ns f.f
  | Ckt.node2 f => liftO ns f.f
  | Ckt.const x => liftO ns (fun _ => x)
  | Ckt.id => liftO ns id
  | Ckt.fst => liftO ns Prod.fst
  | Ckt.snd => liftO ns Prod.snd
  | Ckt.add => liftO ns (fun x => x.1 + x.2)
  | Ckt.sub => liftO ns (fun x => x.1 - x.2)
  | Ckt.seq c1 c2 => denote c2 ∘ denote c1
  | Ckt.par c1 c2 => fun x => sprodO ns (denote c1 x, denote c2 x)
  | Ckt.delay => delay
  | Ckt.lifted_delay => ↑↑ delay
  | Ckt.lifting c => lifting (denote c)
  | Ckt.loop c =>  fun a => fix (fun s => denote c (sprodO ns (a, z⁻¹ s)))
  | Ckt.lifted_loop c => fun a => fix2 (fun s => denote c (sprod2 (a, ↑↑z⁻¹ s)))
  | Ckt.bracket c => ↑↑∫0 ∘ denote c ∘ ↑↑δ0

-- I and D circuits
def cI {a: VType} {ns: Bool}: Ckt a a ns := cloop cadd
def cD {a: VType} {ns: Bool}: Ckt a a ns := (cid &&c cz⁻¹) >>c csub
def cΔ {a b: VType} {ns: Bool} (c: Ckt a b ns) := cI >>c c >>c cD

@[simp]
lemma cI_denote {ns} {a: VType}:
    denote cI = (@I (Optstream ns (VType_interp a)) AddCommGroup.toAddCommMonoid) := by
  rcases ns <;> simp [cI, denote] <;> rfl

@[simp]
lemma cD_denote {ns} {a: VType}:
    denote cD = (@D (Optstream ns (VType_interp a)) _) := by
  rcases ns <;> simp [cD, denote] <;> rfl

@[simp]
lemma cΔ_denote {ns} {a b: VType} (c: Ckt a b ns):
    denote (cΔ c) = ((denote c)^Δ) := by
  simp [cΔ, denote]
  funext x; simp [incremental]

end CktBasic

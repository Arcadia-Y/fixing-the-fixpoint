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

-- Fixpoint Convergence checker structure
-- the first `True` in each row is expected to indicate the convergence
structure FixChecker {A: VType} where
  f: Operator (stream (VType_interp A)) (stream Prop)
  -- The checker should be causal
  causal: CausalNested f
  -- The implementation of the checker is assumed to be bounded by `cost`
  cost: Operator (stream (VType_interp A)) (stream ℕ)

-- Well-Formed Circuit
inductive Ckt: Bool -> VType -> VType -> Type 1
  -- primitive nodes (lifted by default)
  | node1 {A B: Type} [BaseType A] [BaseType B] (f: @UnaryNode A B _ _) : Ckt 0 (VType.base A) (VType.base B)
  | node2 {A B C: Type} [BaseType A] [BaseType B] [BaseType C]
      (f: @BinaryNode A B C _ _ _) : Ckt 0 (VType.base A ×ᵥ VType.base B) (VType.base C)
  -- constant
  | const {a b: VType} (x: VType_interp b) : Ckt 0 a b
  -- product combinators
  | id {ns} {a: VType} : Ckt ns a a
  | fst {ns a b} : Ckt ns (a ×ᵥ b) a
  | snd {ns a b} : Ckt ns (a ×ᵥ b) b
  -- group operations
  | add {ns a} : Ckt ns (a ×ᵥ a) a
  | sub {ns a} : Ckt ns (a ×ᵥ a) a
  -- sequential composition
  | seq {ns a b c} (c1 : Ckt ns a b) (c2 : Ckt ns b c) : Ckt ns a c
  -- parallel composition
  | par {ns a b c} (c1 : Ckt ns a b) (c2 : Ckt ns a c) : Ckt ns a (b ×ᵥ c)
  -- delay
  | delay {ns a} : Ckt ns a a
  -- lifting
  | lifting {a b} (c: Ckt 0 a b) : Ckt 1 a b
  -- feedback loop with normal delay
  | loop {ns a b} (c: Ckt ns (a ×ᵥ b) b): Ckt ns a b
  -- loop with lifted delay (delay by column)
  | loop_lifted {a b} (c: Ckt 1 (a ×ᵥ b) b): Ckt 1 a b
  -- stream introduction and elimination
  | bracket {a b} (c: Ckt 1 a b) (fc: @FixChecker b) : Ckt 0 a b

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
notation "cloop " c:max => Ckt.loop c
notation "cloop2 " c:max => Ckt.loop_lifted c
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

-- Type abbreviations
@[reducible, simp]
def OVType (ns: Bool) (A: VType) :=
  Optstream ns (VType_interp A)
@[reducible, simp]
def SOType (ns: Bool) (T: Type) :=
  stream (Optstream ns T)
@[reducible, simp]
def SOVType (ns: Bool) (A: VType) :=
  SOType ns (VType_interp A)

-- Type of the denotational semantics of circuits
-- both input and output types are streams
-- `ns` denotes whether the circuit is nested
@[reducible, simp]
def DenoteType (ns: Bool) (a b: VType) :=
  Operator (OVType ns a) (OVType ns b)

-- denotational semantics of circuits
-- the semantics is "partial" w.r.t. termination
-- `denote c x = y` denotes that if `c` terminates on input `x` then the output is `y`
noncomputable def denote {ns} {a b: VType}: (Ckt ns a b) -> DenoteType ns a b
  | Ckt.node1 f => lifting f.f
  | Ckt.node2 f => lifting f.f
  | Ckt.const x => fun _ _ => x
  | Ckt.id => id
  | Ckt.fst => liftO ns Prod.fst
  | Ckt.snd => liftO ns Prod.snd
  | Ckt.add => liftO ns (fun x => x.1 + x.2)
  | Ckt.sub => liftO ns (fun x => x.1 - x.2)
  | Ckt.seq c1 c2 => denote c2 ∘ denote c1
  | Ckt.par c1 c2 => fun x => sprodO ns (denote c1 x, denote c2 x)
  | Ckt.delay => delay
  | Ckt.lifting c => lifting (denote c)
  | Ckt.loop c =>  fun a => fix (fun s => denote c (sprodO ns (a, z⁻¹ s)))
  | Ckt.loop_lifted c => fun a => fix2 (fun s => denote c (sprod2 (a, ↑↑z⁻¹ s)))
  | Ckt.bracket c _ => ↑↑∫0 ∘ denote c ∘ ↑↑δ0

-- I and D circuits
def cI {ns} {a: VType}: Ckt ns a a := cloop cadd
def cD {ns} {a: VType}: Ckt ns a a := (cid &&c cz⁻¹) >>c csub
def cΔ {ns} {a b: VType} (c: Ckt ns a b): Ckt ns a b := cI >>c c >>c cD

@[simp]
lemma cI_denote {ns} {a: VType}:
    denote cI = (@I (Optstream ns (VType_interp a)) AddCommGroup.toAddCommMonoid) := by
  rcases ns <;> simp [cI, denote] <;> rfl

@[simp]
lemma cD_denote {ns} {a: VType}:
    denote cD = (@D (Optstream ns (VType_interp a)) _) := by
  rcases ns <;> simp [cD, denote] <;> rfl

@[simp]
lemma cΔ_denote {ns} {a b: VType} (c: Ckt ns a b):
    denote (cΔ c) = ((denote c)^Δ) := by
  simp [cΔ, denote]
  funext x; simp [incremental]

-- polymorphic causality w.r.t. nested streams
def CausalO (ns: Bool) {a b: Type} (f: Operator (Optstream ns a) (Optstream ns b)): Prop :=
  match ns with
  | false => Causal f
  | true => CausalNested f

@[simp]
lemma causalO_false {a b: Type} (f: Operator (Optstream false a) (Optstream false b)):
    CausalO false f <-> Causal f := by rfl
@[simp]
lemma causalO_true {a b: Type} (f: Operator (Optstream true a) (Optstream true b)):
    CausalO true f <-> CausalNested f := by rfl

theorem causalO_liftO {ns} {a b: Type} (f: a -> b):
    CausalO ns (liftO ns f) := by
  rcases ns <;> simp [liftO]

theorem causalO_id {ns} {a: Type}:
    CausalO ns (@id (stream (Optstream ns a))) := by
  rcases ns <;> simp <;> tauto

theorem causalO_const {ns} {a b: Type} (c:stream (Optstream ns b)):
    CausalO ns (fun (_: stream (Optstream ns a)) => c) := by
  rcases ns <;> simp; tauto

theorem causalO_sprodO {ns} {a b c: Type}
  (S1 : Operator (Optstream ns a) (Optstream ns b)) (h1 : CausalO ns S1)
  (S2 : Operator (Optstream ns a) (Optstream ns c)) (h2 : CausalO ns S2) :
    CausalO ns (fun x => sprodO ns (S1 x, S2 x)) := by
  rcases ns <;> simp [sprodO]
  · intro s1 s2 n heq; simp
    constructor
    · apply h1; tauto
    · apply h2; tauto
  · intro s1 s2 n t h; simp
    simp at S1 S2 h1 h2
    constructor
    · apply h1; tauto
    · apply h2; tauto

theorem causalO_comp {ns} {a b c: Type}
  (f: Operator (Optstream ns a) (Optstream ns b))
  (g: Operator (Optstream ns b) (Optstream ns c))
  (hg: CausalO ns g) (hf: CausalO ns f):
    CausalO ns (g ∘ f) := by
  rcases ns <;> simp at *
  · apply causal_comp_causal f <;> tauto
  · apply causalNested_comp g <;> tauto

theorem causalO_delay {ns} {a: Type} [Zero a]:
    CausalO ns (@delay (Optstream ns a) _) := by
  rcases ns <;> simp
  · apply delay_causal
  · intro s1 s2 n t h
    simp [delay]; split_ifs; simp
    apply h <;> omega

theorem causalO_ckt {ns} {a b: VType} (c: Ckt ns a b): CausalO ns (denote c) := by
  induction c <;> simp [denote] <;> try apply causalO_liftO
  case const =>
    tauto
  case id =>
    apply causalO_id
  case seq ns _ _ _ c1 c2 ih1 ih2 =>
    apply causalO_comp <;> tauto
  case par c1 c2 ih1 ih2 =>
    apply causalO_sprodO <;> tauto
  case delay ns _ =>
    apply causalO_delay
  case lifting ih =>
    apply causalNested_lifting; apply ih
  case loop ns _ _ c ih =>
    rcases ns <;> simp
    · apply loop1_causal; apply ih
    · apply causalNested_loop; apply ih
  case loop_lifted c ih =>
    apply causalNested_loop_lifted; apply ih
  case bracket c _ ih =>
    apply causal_comp_causal (denote c ∘ ↑↑δ0)
    apply causal_comp_causal (↑↑δ0)
    apply lifting_causal
    apply casualNested_is_causal; apply ih
    apply lifting_causal

theorem causalO_is_causal {ns} {a b: Type}
  (f: Operator (Optstream ns a) (Optstream ns b))
  (h: CausalO ns f):
    Causal f := by
  rcases ns <;> simp at h; tauto
  apply casualNested_is_causal; tauto

theorem sprodO_delay_strict {ns a b} (x: stream (Optstream ns (VType_interp a))):
    Strict fun (s: stream (Optstream ns (VType_interp b))) ↦ sprodO ns (x, z⁻¹ s) := by
  apply causal_strict_strict (T := fun s ↦ sprodO ns (x, s))
  · apply delay_strict
  · apply causalO_is_causal; apply causalO_sprodO
    · apply causalO_const
    · apply causalO_id

theorem loop_body_strict {ns a b} (c: Ckt ns (a ×ᵥ b) b) x:
    Strict fun s ↦ denote c (sprodO ns (x, z⁻¹ s)) := by
  apply causal_strict_strict (T := fun s ↦ denote c (sprodO ns (x, s)))
  · apply delay_strict
  apply causalO_is_causal; apply causalO_comp
  · apply causalO_ckt
  · apply causalO_sprodO
    apply causalO_const; apply causalO_id

theorem loop_unfold {ns a b} (c: Ckt ns (a ×ᵥ b) b) x:
    denote (Ckt.loop c) x = denote c (sprodO ns (x, z⁻¹ (denote (Ckt.loop c) x))) := by
  simp [denote]
  nth_rw 1 [fix_eq]
  apply loop_body_strict

theorem loop_lifted_body_strict {a b} (c: Ckt 1 (a ×ᵥ b) b) x:
    Strict2 fun s ↦ denote c (sprod2 (x, ↑↑z⁻¹ s)) := by
  apply causalNested_strict2_strict2
  · suffices CausalO true (denote c) by apply this
    apply causalO_ckt
  apply lifting_delay_strict2

theorem loop_lifted_unfold {a b} (c: Ckt 1 (a ×ᵥ b) b) x:
    denote (Ckt.loop_lifted c) x = denote c (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.loop_lifted c) x))) := by
  simp [denote]
  nth_rw 1 [fix2_eq]
  apply loop_lifted_body_strict

def add_cost {a: VType} (x: VType_interp a × VType_interp a): ℕ :=
  match a with
  | VType.base _ => BaseType.add_cost x
  | VType.prod _ _ => add_cost (x.1.1, x.2.1) + add_cost (x.1.2, x.2.2)

def sub_cost {a: VType} (x: VType_interp a × VType_interp a): ℕ :=
  match a with
  | VType.base _ => BaseType.sub_cost x
  | VType.prod _ _ => sub_cost (x.1.1, x.2.1) + sub_cost (x.1.2, x.2.2)

def VType_space {a: VType} (x: VType_interp a) :=
  PType_sum (VType_size x)

-- Type of cost function of a circuit
-- For `cf: CostFunType ns a`, `cf x` is the cost of computing the output on input `x`
-- If an entry of `cf x` is `some n`,
--   then if all previous computation terminate, the step terminates and the cost is `n`
-- otherwise if `cf x` is `⊤`,
--   then the step diverges
@[simp, reducible]
def CostFunType (ns: Bool) (a: VType) :=
  (SOVType ns a) -> (SOType ns ℕ∞)

instance (ns: Bool): CanonicallyOrderedAdd (SOType ns ℕ∞) := by
  rcases ns <;> simp [stream] <;> infer_instance

-- extend the `ℕ` in `f`'s domain to `ℕ∞`
@[simp]
def extend_fun {ns} {a: VType} (f: SOVType ns a -> SOType ns ℕ): CostFunType ns a :=
  fun x => match ns with
  | false => fun n => ↑(f x n)
  | true => fun m n => ↑(f x m n)

def FirstTrue (s: stream Prop) (n: ℕ): Prop :=
  s n ∧ ∀ m < n, ¬ s m

-- Cost model for circuits based on the default evaluation strategy
-- For a circuit `c`, `cost_f c` is a function maps an input of `c` to the cost of computing the output
noncomputable def cost_f {ns} {a b: VType}: (Ckt ns a b) -> (CostFunType ns a)
  | Ckt.node1 f => extend_fun (↑↑f.cost)
  | Ckt.node2 f => extend_fun (↑↑f.cost)
  | Ckt.const _ => 0
  | Ckt.id => 0
  | Ckt.fst => 0
  | Ckt.snd => 0
  | Ckt.add => extend_fun (liftO ns add_cost)
  | Ckt.sub => extend_fun (liftO ns sub_cost)
  | Ckt.seq c1 c2 => fun x => cost_f c1 x + cost_f c2 (denote c1 x)
  | Ckt.par c1 c2 => fun x => cost_f c1 x + cost_f c2 x
  | Ckt.delay => extend_fun (liftO ns VType_space)
  | Ckt.lifting c => ↑↑(cost_f c)
  | Ckt.loop c => fun x => let o := denote (Ckt.loop c) x
      cost_f c (sprodO ns (x, z⁻¹ o)) + extend_fun (liftO ns VType_space) o
  | Ckt.loop_lifted c => fun x => let o := denote (Ckt.loop_lifted c) x
      fun m n => cost_f c (sprod2 (x, ↑↑z⁻¹ o)) m n + (liftO 1 VType_space) o m n
  | Ckt.bracket c fc => fun x i => let o := denote c (↑↑δ0 x)
      -- If cost checker returns true for the first time at step n,
      -- and the stream does converge after n,
      -- then the cost is the sum of the cost of `c`, the integration cost and `fc.cost`
      match Classical.propDecidable (∃ n, FirstTrue ((fc.f o) i) n ∧ ZeroAfter (o i) n) with
      | Decidable.isTrue h =>
        let sumO := fun n => sumVals (o i) n
        let c_cost := cost_f c (↑↑δ0 x) i
        let integral_cost: stream ℕ∞ := fun n => ↑(add_cost (sumO n, o i n))
        let checker_cost := extend_fun fc.cost o i
        -- Question: should we omit the integral cost and the checker cost?
        sumVals
          (c_cost + integral_cost + checker_cost)
          (Classical.choose h + 1)
      | Decidable.isFalse _ => ⊤

end CktBasic

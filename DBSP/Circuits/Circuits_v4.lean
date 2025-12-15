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
-- `Ckt a b ns rec` is a circuit with input type `a` and output type `b`
-- `ns` indicates whether the circuit is on nested streams
-- `rec` indicates whether the circuit **may** contain recursive queries (i.e. `bracket` nodes)
-- which means `rec = 0` indicates the circuit must be free of recursive queries
-- `rec = 1` indicates the circuit may contain recursive queries, but not necessarily
inductive Ckt: VType -> VType -> Bool -> Bool -> Type 1
  -- primitive nodes (lifted by default)
  | node1 {rec} {A B: Type} [BaseType A] [BaseType B] (f: @UnaryNode A B _ _) :
      Ckt (VType.base A) (VType.base B) 0 rec
  | node2 {rec} {A B C: Type} [BaseType A] [BaseType B] [BaseType C]
      (f: @BinaryNode A B C _ _ _) : Ckt (VType.base A ×ᵥ VType.base B) (VType.base C) 0 rec
  -- constant
  | const {rec} {a b: VType} (x: VType_interp b) : Ckt a b 0 rec
  -- product combinators
  | id {ns rec} {a: VType} : Ckt a a ns rec
  | fst {ns rec} {a b: VType} : Ckt (a ×ᵥ b) a ns rec
  | snd {ns rec} {a b: VType} : Ckt (a ×ᵥ b) b ns rec
  -- group operations
  | add {ns rec} {a: VType} : Ckt (a ×ᵥ a) a ns rec
  | sub {ns rec} {a: VType} : Ckt (a ×ᵥ a) a ns rec
  -- sequential composition
  | seq {ns rec a b c} (c1 : Ckt a b ns rec) (c2 : Ckt b c ns rec) : Ckt a c ns rec
  -- parallel composition
  | par {ns rec a b c} (c1 : Ckt a b ns rec) (c2 : Ckt a c ns rec) : Ckt a (b ×ᵥ c) ns rec
  -- delay
  | delay {ns rec a} : Ckt a a ns rec
  -- lifting
  -- only circuits without recursive queries can be lifted
  | lifting {a b} (c: Ckt a b 0 0) : Ckt a b 1 0
  -- feedback loop with normal delay
  | loop {ns rec a b} (c: Ckt (a ×ᵥ b) b ns rec): Ckt a b ns rec
  -- loop with lifted delay (delay by column)
  | loop_lifted {a b} (c: Ckt (a ×ᵥ b) b 1 0): Ckt a b 1 0
  -- stream introduction and elimination
  -- only circuits without recursive queries can be included in bracket
  | bracket {a b} (c: Ckt a b 1 0) : Ckt a b 0 1

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

lemma Ckt_generalize_rec_0 {A B: VType} {ns: Bool} {P: Ckt A B ns 0 -> Prop}
  (h: ∀ rec (c: Ckt A B ns rec), rec = 0 ->
    match rec with
    | 0 => P c
    | 1 => True):
    ∀ c: Ckt A B ns 0, P c := by
  intros c; specialize h 0 c (by tauto); apply h

lemma Ckt_generalize_ns_1 {A B: VType} {rec: Bool} {P: Ckt A B 1 rec -> Prop}
  (h: ∀ ns (c: Ckt A B ns rec), ns = 1 ->
    match ns with
    | false => True
    | true => P c):
    ∀ (c: Ckt A B 1 rec), P c := by
  intros c; specialize h 1 c (by tauto); apply h

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

def STrue {ns: Bool}: SOType ns Prop :=
  match ns with
  | false => fun _ => True
  | true => fun _ _ => True

@[simp]
lemma STrue_false_apply {n: ℕ}:
    @STrue false n = True := by rfl

@[simp]
lemma STrue_true_apply {m n: ℕ}:
    @STrue true m n = True := by rfl

def SAnd {ns: Bool}: SOType ns Prop -> SOType ns Prop -> SOType ns Prop :=
  match ns with
  | false => fun P Q x => P x ∧ Q x
  | true => fun P Q x y => P x y ∧ Q x y

@[simp]
lemma SAnd_false_apply (P Q: SOType false Prop) (n: ℕ):
    SAnd P Q n = (P n ∧ Q n) := by rfl

@[simp]
lemma SAnd_true_apply (P Q: SOType true Prop) (m n: ℕ):
    SAnd P Q m n = (P m n ∧ Q m n) := by rfl

-- Type of the denotational semantics of circuits
-- both input and output types are streams
-- `ns` denotes whether the circuit is nested
@[reducible, simp]
def DenoteType (ns: Bool) (a b: VType) :=
  Operator (OVType ns a) (OVType ns b)

-- denotational semantics of circuits
-- the semantics is "partial" w.r.t. termination
-- `denote c x = y` denotes that if `c` terminates on input `x` then the output is `y`
noncomputable def denote {a b: VType} {ns rec: Bool}: (Ckt a b ns rec) -> DenoteType ns a b
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
  | Ckt.bracket c => ↑↑∫0 ∘ denote c ∘ ↑↑δ0

-- I and D circuits
def cI {a: VType} {ns rec: Bool}: Ckt a a ns rec := cloop cadd
def cD {a: VType} {ns rec: Bool}: Ckt a a ns rec := (cid &&c cz⁻¹) >>c csub
def cΔ {a b: VType} {ns rec: Bool} (c: Ckt a b ns rec) := cI >>c c >>c cD

@[simp]
lemma cI_denote {ns rec} {a: VType}:
    denote (cI (rec := rec)) = (@I (Optstream ns (VType_interp a)) AddCommGroup.toAddCommMonoid) := by
  rcases ns <;> simp [cI, denote] <;> rfl

@[simp]
lemma cD_denote {ns rec} {a: VType}:
    denote (cD (rec := rec)) = (@D (Optstream ns (VType_interp a)) _) := by
  rcases ns <;> simp [cD, denote] <;> rfl

@[simp]
lemma cΔ_denote {ns rec} {a b: VType} (c: Ckt a b ns rec):
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

theorem causalO_ckt {ns rec} {a b: VType} (c: Ckt a b ns rec): CausalO ns (denote c) := by
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
  case loop ns _ _ _ c ih =>
    rcases ns <;> simp
    · apply loop1_causal; apply ih
    · apply causalNested_loop; apply ih
  case loop_lifted c ih =>
    apply causalNested_loop_lifted; apply ih
  case bracket c ih =>
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

theorem loop_body_strict {ns rec a b} (c: Ckt (a ×ᵥ b) b ns rec) x:
    Strict fun s ↦ denote c (sprodO ns (x, z⁻¹ s)) := by
  apply causal_strict_strict (T := fun s ↦ denote c (sprodO ns (x, s)))
  · apply delay_strict
  apply causalO_is_causal; apply causalO_comp
  · apply causalO_ckt
  · apply causalO_sprodO
    apply causalO_const; apply causalO_id

theorem loop_unfold {ns rec a b} (c: Ckt (a ×ᵥ b) b ns rec) x:
    denote (Ckt.loop c) x = denote c (sprodO ns (x, z⁻¹ (denote (Ckt.loop c) x))) := by
  simp [denote]
  nth_rw 1 [fix_eq]
  apply loop_body_strict

theorem loop_lifted_body_strict {a b} (c: Ckt (a ×ᵥ b) b 1 0) x:
    Strict2 fun s ↦ denote c (sprod2 (x, ↑↑z⁻¹ s)) := by
  apply causalNested_strict2_strict2
  · suffices CausalO true (denote c) by apply this
    apply causalO_ckt
  apply lifting_delay_strict2

theorem loop_lifted_unfold {a b} (c: Ckt (a ×ᵥ b) b 1 0) x:
    denote (Ckt.loop_lifted c) x = denote c (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.loop_lifted c) x))) := by
  simp [denote]
  nth_rw 1 [fix2_eq]
  apply loop_lifted_body_strict

-- A lifted circuit is a lifted scalar function
def lifted_Ckt {ns rec} {A B: VType} (c: Ckt A B ns rec): Prop :=
  ∃ f, denote c = liftO ns f

end CktBasic

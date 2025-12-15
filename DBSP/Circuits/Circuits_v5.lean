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
  -- primitive nodes (lifted by default)
  | node1 {A B: Type} [BaseType A] [BaseType B] (f: @UnaryNode A B _ _) :
      Ckt (VType.base A) (VType.base B) 0
  | node2{A B C: Type} [BaseType A] [BaseType B] [BaseType C]
      (f: @BinaryNode A B C _ _ _) : Ckt (VType.base A ×ᵥ VType.base B) (VType.base C) 0
  -- constant
  | const {a b: VType} (x: VType_interp b) : Ckt a b 0
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
  -- lifting
  | lifting {a b} (c: Ckt a b 0) : Ckt a b 1
  -- feedback loop with normal delay
  | loop {ns a b} (c: Ckt (a ×ᵥ b) b ns): Ckt a b ns
  -- loop with lifted delay (delay by column)
  | loop_lifted {a b} (c: Ckt (a ×ᵥ b) b 1): Ckt a b 1
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
notation "cloop " c:max => Ckt.loop c
notation "cloop2 " c:max => Ckt.loop_lifted c
notation:max "c₁ " f => Ckt.node1 f
notation:max "c₂ " f => Ckt.node2 f
notation "cbracket " => Ckt.bracket
notation "cadd" => Ckt.add
notation "csub" => Ckt.sub

lemma Ckt_generalize_ns_1 {A B: VType} {P: Ckt A B 1 -> Prop}
  (h: ∀ ns (c: Ckt A B ns), ns = 1 ->
    match ns with
    | false => True
    | true => P c):
    ∀ (c: Ckt A B 1), P c := by
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

lemma sprod_eq_iff {a b: Type}
  (x1 x2: stream a) (y1 y2: stream b):
    sprod (x1, y1) = sprod (x2, y2) <-> x1 = x2 ∧ y1 = y2 := by
  constructor
  · intro h
    constructor <;> funext n <;>
    have := congr_fun h n <;>
    simp at this <;> tauto
  · rintro ⟨h1, h2⟩;
    subst h1 h2; simp

lemma sprod2_eq_iff {a b: Type}
  (x1 x2: stream (stream a)) (y1 y2: stream (stream b)):
    sprod2 (x1, y1) = sprod2 (x2, y2) <-> x1 = x2 ∧ y1 = y2 := by
  constructor
  · intro h
    constructor <;> funext n m <;>
    have := congr_fun (congr_fun h n) m <;>
    simp at this <;> tauto
  · rintro ⟨h1, h2⟩;
    subst h1 h2; simp

lemma sprodO_eq_iff {ns: Bool} {a b: Type}
  (x1 x2: stream (Optstream ns a)) (y1 y2: stream (Optstream ns b)):
    sprodO ns (x1, y1) = sprodO ns (x2, y2) <-> x1 = x2 ∧ y1 = y2 := by
  rcases ns <;> simp [sprodO]
  · apply sprod_eq_iff
  · apply sprod2_eq_iff

lemma sprod_causal {a b: Type}
  (x1 x2: stream a) (y1 y2: stream b) (n: ℕ):
    (sprod (x1, y1) =[n]= sprod (x2, y2)) <->
    ((x1 =[n]= x2) ∧ (y1 =[n]= y2)) := by
  constructor
  · intro h; simp at h; constructor
    · intro m hm; specialize h m hm; simp at h; tauto
    · intro m hm; specialize h m hm; simp at h; tauto
  · rintro ⟨h1, h2⟩ m hm; simp; constructor
    · apply h1; tauto
    · apply h2; tauto

lemma sprod2_causal {a b: Type}
  (x1 x2: stream (stream a)) (y1 y2: stream (stream b)) (n: ℕ):
    (sprod2 (x1, y1) =[n]= sprod2 (x2, y2)) <->
    ((x1 =[n]= x2) ∧ (y1 =[n]= y2)) := by
  constructor
  · intro h; simp at h; constructor <;>
    intro m hm <;> specialize h m hm <;>
    funext i <;> apply congr_fun (a:=i) at h <;>
    simp at h <;> tauto
  · rintro ⟨h1, h2⟩ m hm; funext n; simp; constructor
    · rw [h1]; tauto
    · rw [h2]; tauto

lemma sprodO_causal {ns: Bool} {a b: Type}
  (x1 x2: stream (Optstream ns a)) (y1 y2: stream (Optstream ns b)) (n: ℕ):
    (sprodO ns (x1, y1) =[n]= sprodO ns (x2, y2)) <->
    ((x1 =[n]= x2) ∧ (y1 =[n]= y2)) := by
  rcases ns <;> simp [sprodO]
  · apply sprod_causal
  · apply sprod2_causal

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
  | Ckt.node1 f => lifting f.f
  | Ckt.node2 f => lifting f.f
  | Ckt.const x => fun _ _ => x
  | Ckt.id => liftO ns id
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

theorem ckt_causalO {ns} {a b: VType} (c: Ckt a b ns): CausalO ns (denote c) := by
  induction c <;> simp [denote] <;> try apply causalO_liftO
  case const =>
    tauto
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

theorem ckt_causal {ns} {a b: VType} (c: Ckt a b ns): Causal (denote c) := by
  apply causalO_is_causal; apply ckt_causalO

theorem ckt_CausalNested {a b: VType} (c: Ckt a b 1): CausalNested (denote c) := by
  have := ckt_causalO c; simp at this; tauto

theorem sprodO_delay_strict {ns a b} (x: stream (Optstream ns (VType_interp a))):
    Strict fun (s: stream (Optstream ns (VType_interp b))) ↦ sprodO ns (x, z⁻¹ s) := by
  apply causal_strict_strict (T := fun s ↦ sprodO ns (x, s))
  · apply delay_strict
  · apply causalO_is_causal; apply causalO_sprodO
    · apply causalO_const
    · apply causalO_id

theorem loop_body_strict {ns a b} (c: Ckt (a ×ᵥ b) b ns) x:
    Strict fun s ↦ denote c (sprodO ns (x, z⁻¹ s)) := by
  apply causal_strict_strict (T := fun s ↦ denote c (sprodO ns (x, s)))
  · apply delay_strict
  apply causalO_is_causal; apply causalO_comp
  · apply ckt_causalO
  · apply causalO_sprodO
    apply causalO_const; apply causalO_id

theorem loop_unfold {ns a b} (c: Ckt (a ×ᵥ b) b ns) x:
    denote (Ckt.loop c) x = denote c (sprodO ns (x, z⁻¹ (denote (Ckt.loop c) x))) := by
  simp [denote]
  nth_rw 1 [fix_eq]
  apply loop_body_strict

theorem loop_lifted_body_strict {a b} (c: Ckt (a ×ᵥ b) b 1) x:
    Strict2 fun s ↦ denote c (sprod2 (x, ↑↑z⁻¹ s)) := by
  apply causalNested_strict2_strict2
  · suffices CausalO true (denote c) by apply this
    apply ckt_causalO
  apply lifting_delay_strict2

theorem loop_lifted_unfold {a b} (c: Ckt (a ×ᵥ b) b 1) x:
    denote (Ckt.loop_lifted c) x = denote c (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.loop_lifted c) x))) := by
  simp [denote]
  nth_rw 1 [fix2_eq]
  apply loop_lifted_body_strict

def lifted_Ckt {ns} {A B: VType} (c: Ckt A B ns): Prop :=
  ∃ f, denote c = ↑↑f

def lifted_scalar_Ckt {ns} {A B: VType} (c: Ckt A B ns): Prop :=
  ∃ f, denote c = liftO ns f

end CktBasic

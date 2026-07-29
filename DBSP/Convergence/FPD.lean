import DBSP.Convergence.Spec
import Mathlib.Computability.Halting

/-!
# The fixpoint detection problem

This file formalizes the paper's general, semantic notion of a fixpoint
detector.  It is distinct from `FPDetector1` and `FPDetector2` in
`DBSP.Convergence.FPDetector`, which are the concrete StFP detectors introduced
later in the paper.
-/

open CktBasic

namespace FPD

/-- A Boolean stream encounters its first `true` value at index `n`. -/
def FirstTrue1 (s : stream Bool) (n : Nat) : Prop :=
  s n = true ∧ ∀ m < n, s m = false

/-- Row-wise first-`true` indices for a nested Boolean stream. -/
def FirstTrue2 (s : stream (stream Bool)) (b : stream Nat) : Prop :=
  ∀ i, FirstTrue1 (s i) (b i)

/-- A candidate level-1 fixpoint detector for circuits with input type `A`. -/
abbrev FixpointDetector1 (A : VType) :=
  stream (VType_interp A) → stream Bool

/-- Soundness of a level-1 fixpoint detector (Eq. 5 in the paper). -/
def SoundFixpointDetector1 {A B : VType}
    (c : Ckt A B 0) (f : FixpointDetector1 A) : Prop :=
  ∀ (x : VType_interp A) n,
    FirstTrue1 (f (δ0 x)) n →
      ZeroAfter (denote c (δ0 x)) n

/-- Completeness of a level-1 fixpoint detector (Eq. 6 in the paper). -/
def CompleteFixpointDetector1 {A B : VType}
    (c : Ckt A B 0) (f : FixpointDetector1 A) : Prop :=
  ∀ (x : VType_interp A) n,
    ZeroAfter (denote c (δ0 x)) n →
      ∃ m, FirstTrue1 (f (δ0 x)) m

/-- The level-1 FPD problem from Definition 4.3. -/
def IsFixpointDetector1 {A B : VType}
    (c : Ckt A B 0) (f : FixpointDetector1 A) : Prop :=
  SoundFixpointDetector1 c f ∧ CompleteFixpointDetector1 c f

/-- A candidate level-2 fixpoint detector for circuits with input type `A`. -/
abbrev FixpointDetector2 (A : VType) :=
  stream (stream (VType_interp A)) → stream (stream Bool)

/-- Soundness of a level-2 fixpoint detector (Eq. 7 in the paper). -/
def SoundFixpointDetector2 {A B : VType}
    (c : Ckt A B 1) (f : FixpointDetector2 A) : Prop :=
  ∀ (x : stream (VType_interp A)) (b : stream Nat),
    FirstTrue2 (f ((↑↑δ0) x)) b →
      ZeroAfterVec (denote c ((↑↑δ0) x)) b

/-- Completeness of a level-2 fixpoint detector (Eq. 8 in the paper). -/
def CompleteFixpointDetector2 {A B : VType}
    (c : Ckt A B 1) (f : FixpointDetector2 A) : Prop :=
  ∀ (x : stream (VType_interp A)) (b : stream Nat),
    ZeroAfterVec (denote c ((↑↑δ0) x)) b →
      ∃ b', FirstTrue2 (f ((↑↑δ0) x)) b'

/-- The level-2 FPD problem from Definition 4.3. -/
def IsFixpointDetector2 {A B : VType}
    (c : Ckt A B 1) (f : FixpointDetector2 A) : Prop :=
  SoundFixpointDetector2 c f ∧ CompleteFixpointDetector2 c f

/-- Computability of the observable restriction of a level-1 detector to an
encoded family of canonical inputs.

The paper only queries a detector on streams of the form `δ0 (embed x)`.
Consequently, no encoding of arbitrary infinite streams is needed: the
first-order function `(x, n) ↦ f (δ0 (embed x)) n` is the relevant
computability requirement. -/
def ComputableOnDelta1 {A : VType} {X : Type} [Primcodable X]
    (embed : X → VType_interp A) (f : FixpointDetector1 A) : Prop :=
  Computable₂ fun x n => f (δ0 (embed x)) n

/-- A level-1 detector is computable when each output entry on every canonical
input `δ0 x` is computable from `x` and the entry index. -/
def ComputableFixpointDetector1 {A : VType}
    [Primcodable (VType_interp A)] (f : FixpointDetector1 A) : Prop :=
  ComputableOnDelta1 (fun x : VType_interp A => x) f

end FPD

/-!
# Undecidability of exact fixpoint detection

When primitive DBSP nodes can express primitive-recursive functions, there is
a level-1 circuit with no computable sound and complete fixpoint detector.

The proof first establishes impossibility for the detector's observable
restriction to canonical inputs `δ0 x`, then packages that reduction using the
general level-1 FPD definition above.
-/

namespace FPDUndecidability

open Nat.Partrec
open Nat.Partrec.Code
open FPD

/-- Integers are used as the circuit's scalar type because DBSP base types form
additive commutative groups. -/
instance intBaseType : BaseType Int where
  has_group := inferInstance
  size := fun _ => 0
  add_cost := fun _ => 0
  sub_cost := fun _ => 0

/-- The expressiveness assumption used by the paper, restricted to the binary
primitive-recursive functions needed by this reduction. -/
def PrimitiveNodesExpressPrimrec : Prop :=
  ∀ f : Nat → Nat → Nat, Primrec₂ f →
    ∃ node : BinaryNode Int Int Int,
      ∀ x y : Nat, node.f ((x : Int), (y : Int)) = (f x y : Int)

/-- `boundedHalting code steps` is `1` exactly when the partial-recursive
program encoded by `code` has halted on input `0` within `steps` units of
the universal evaluator's fuel. -/
def boundedHalting (code steps : Nat) : Nat :=
  bif (evaln steps (Denumerable.ofNat Code code) 0).isSome then 1 else 0

theorem boundedHalting_primrec : Primrec₂ boundedHalting := by
  apply Primrec₂.mk
  have heval :
      Primrec
        (fun p : Nat × Nat =>
          evaln p.2 (Denumerable.ofNat Code p.1) 0) := by
    exact primrec_evaln.comp
      ((Primrec.snd.pair ((Primrec.ofNat Code).comp Primrec.fst)).pair
        (Primrec.const 0))
  exact Primrec.cond (Primrec.option_isSome.comp heval)
    (Primrec.const 1) (Primrec.const 0)

/-- A clock stream: the value at iteration `n` is `n + 1`. -/
def clockCircuit : Ckt [Int]v [Int]v 0 :=
  (Ckt.const (ns := 0) (a := [Int]v) (1 : Int)) >>c
    (@cI [Int]v 0)

/-- The fixed circuit used in the reduction. Its first input to `node` is the
encoded program, and its second input is the current clock value. -/
def haltingCircuit (node : BinaryNode Int Int Int) :
    Ckt [Int]v [Int]v 0 :=
  ((@cI [Int]v 0) &&c clockCircuit) >>c Ckt.node2 node

private lemma integral_one (n : Nat) :
    I (fun _ : Nat => (1 : Int)) n = (n + 1 : Nat) := by
  induction n with
  | zero => simp [integral_0]
  | succ n ih =>
      rw [integral_succ]
      simp only [ih]
      omega

theorem denote_haltingCircuit
    (node : BinaryNode Int Int Int)
    (hnode : ∀ x y : Nat,
      node.f ((x : Int), (y : Int)) = (boundedHalting x y : Int))
    (code n : Nat) :
    denote (haltingCircuit node) (δ0 (code : Int)) n =
      (boundedHalting code (n + 1) : Int) := by
  simp only [haltingCircuit, clockCircuit, denote, Function.comp_apply,
    liftO_0, lifting_eq, sprodO_0, sprod_apply, integral_delta_apply,
    id_eq]
  rw [cI_denote]
  simp only [integral_delta_apply, lifting_eq]
  change node.f ((code : Int), I (fun _ : Nat => (1 : Int)) n) =
    (boundedHalting code (n + 1) : Int)
  rw [integral_one, hnode]

/-- The observable part of a level-1 detector on canonical inputs: `d x n` is
the detector's result at iteration `n` on input `δ0 x`.  This first-order
interface is the part of the paper's stream-to-stream detector that FPD
soundness and completeness actually inspect. -/
abbrev Detector := Nat → Nat → Bool

def SoundDetector
    (c : Ckt [Int]v [Int]v 0) (d : Detector) : Prop :=
  ∀ (input : Nat) n, FirstTrue1 (d input) n →
    ZeroAfter
      (denote c (δ0 (input : Int))) n

def CompleteDetector
    (c : Ckt [Int]v [Int]v 0) (d : Detector) : Prop :=
  ∀ (input : Nat) n,
    ZeroAfter
      (denote c (δ0 (input : Int))) n →
    ∃ m, FirstTrue1 (d input) m

def SoundCompleteDetector
    (c : Ckt [Int]v [Int]v 0) (d : Detector) : Prop :=
  SoundDetector c d ∧ CompleteDetector c d

private lemma boundedHalting_encode_eq_one_iff (code : Code) (steps : Nat) :
    boundedHalting (Encodable.encode code) steps = 1 ↔
      (evaln steps code 0).isSome = true := by
  generalize hopt : evaln steps code 0 = result
  cases result <;> simp [boundedHalting, hopt]

private lemma boundedHalting_encode_eq_zero_iff (code : Code) (steps : Nat) :
    boundedHalting (Encodable.encode code) steps = 0 ↔
      (evaln steps code 0).isSome = false := by
  generalize hopt : evaln steps code 0 = result
  cases result <;> simp [boundedHalting, hopt]

/-- The circuit's output is eventually zero exactly for programs which do not
halt on input `0`.  Notice that this equivalence holds at every proposed
zero-after bound, since a halting program eventually produces `1` forever. -/
theorem zeroAfter_haltingCircuit_iff_not_dom
    (node : BinaryNode Int Int Int)
    (hnode : ∀ x y : Nat,
      node.f ((x : Int), (y : Int)) = (boundedHalting x y : Int))
    (code : Code) (n : Nat) :
    ZeroAfter
        (denote (haltingCircuit node)
          (δ0 ((Encodable.encode code : Nat) : Int))) n ↔
      ¬(eval code 0).Dom := by
  constructor
  · intro hzero hdom
    obtain ⟨value, hvalue⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨steps, hsteps⟩ := evaln_complete.mp hvalue
    let t := max n steps
    have hmono : value ∈ evaln (t + 1) code 0 :=
      evaln_mono (by simp [t]; omega) hsteps
    have hisSome : (evaln (t + 1) code 0).isSome = true := by
      cases hopt : evaln (t + 1) code 0 with
      | none => simp [hopt] at hmono
      | some _ => simp [hopt]
    have hone :
        boundedHalting (Encodable.encode code) (t + 1) = 1 :=
      (boundedHalting_encode_eq_one_iff code (t + 1)).mpr hisSome
    have hout := hzero t (by simp [t])
    rw [denote_haltingCircuit node hnode] at hout
    simp [hone] at hout
  · intro hnotdom t _
    rw [denote_haltingCircuit node hnode]
    have hnone : evaln (t + 1) code 0 = Option.none := by
      cases hopt : evaln (t + 1) code 0 with
      | none => rfl
      | some value =>
        exfalso
        apply hnotdom
        apply Part.dom_iff_mem.mpr
        have hmem : value ∈ evaln (t + 1) code 0 := by
          simp only [Option.mem_def, hopt]
        exact ⟨value, evaln_sound hmem⟩
    have hbounded :
        boundedHalting (Encodable.encode code) (t + 1) = 0 :=
      (boundedHalting_encode_eq_zero_iff code (t + 1)).mpr (by simp [hnone])
    simp [hbounded]

private theorem rfind_dom_iff_exists_firstTrue (s : Nat → Bool) :
    (Nat.rfind s).Dom ↔ ∃ n, FirstTrue1 s n := by
  constructor
  · intro hdom
    obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp hdom
    refine ⟨n, ?_, ?_⟩
    · simpa using Nat.rfind_spec hn
    · intro m hm
      simpa using Nat.rfind_min hn hm
  · rintro ⟨n, hn, hmin⟩
    apply Part.dom_iff_mem.mpr
    refine ⟨n, Nat.mem_rfind.mpr ⟨?_, ?_⟩⟩
    · simpa using hn
    · intro m hm
      simpa using hmin m hm

/-- The first-order core of the reduction: even on nonnegative scalar inputs,
there is no computable sound and complete detector. -/
theorem no_computable_detector_on_nat_inputs
    (hexpressive : PrimitiveNodesExpressPrimrec) :
    ∃ c : Ckt [Int]v [Int]v 0,
      ¬∃ d : Detector, Computable₂ d ∧ SoundCompleteDetector c d := by
  obtain ⟨node, hnode⟩ :=
    hexpressive boundedHalting boundedHalting_primrec
  refine ⟨haltingCircuit node, ?_⟩
  rintro ⟨detector, hcomputable, hsound, hcomplete⟩
  apply ComputablePred.halting_problem_not_re 0
  let codeDetector : Code → Nat → Bool :=
    fun code n => detector (Encodable.encode code) n
  have hcodeComputable : Computable₂ codeDetector := by
    apply Computable₂.mk
    have hpair :
        Computable fun p : Code × Nat =>
          (Encodable.encode p.1, p.2) :=
      ((@Computable.encode Code _).comp Computable.fst).pair Computable.snd
    exact
      Computable.comp
        (α := Code × Nat) (β := Nat × Nat) (σ := Bool)
        hcomputable hpair
  have hre :
      REPred fun code : Code => (Nat.rfind (codeDetector code)).Dom :=
    (Partrec.rfind hcodeComputable.partrec₂).dom_re
  apply hre.of_eq
  intro code
  rw [rfind_dom_iff_exists_firstTrue]
  constructor
  · rintro ⟨n, hfirst⟩
    exact
      (zeroAfter_haltingCircuit_iff_not_dom node hnode code n).mp
        (hsound (Encodable.encode code) n hfirst)
  · intro hnotdom
    exact hcomplete (Encodable.encode code) 0 <|
      (zeroAfter_haltingCircuit_iff_not_dom node hnode code 0).mpr
        hnotdom

/-- The inclusion of natural numbers into integers is computable for mathlib's
standard encodings. -/
private theorem computable_natCast_int :
    Computable fun n : Nat => (n : Int) := by
  apply Primrec.to_comp
  rw [Primrec.ofNat_iff]
  apply Primrec.encode_iff.mp
  exact Primrec.nat_mul.comp (Primrec.const 2) Primrec.id

/-- There is a fixed level-1 DBSP circuit for which no computable detector in
the sense of paper Definition 4.3 can be both sound and complete.

Computability is only required on the canonical inputs `δ0 x` inspected by the
FPD definition.  The proof then restricts such a detector to nonnegative
integer inputs, which already suffices for the contradiction. -/
theorem fpd_undecidable
    (hexpressive : PrimitiveNodesExpressPrimrec) :
    ∃ c : Ckt [Int]v [Int]v 0,
      ¬∃ f : FixpointDetector1 [Int]v,
        ComputableFixpointDetector1 f ∧
          IsFixpointDetector1 c f := by
  obtain ⟨c, hrestricted⟩ :=
    no_computable_detector_on_nat_inputs hexpressive
  refine ⟨c, ?_⟩
  rintro ⟨f, hcomputable, hsound, hcomplete⟩
  have hnatComputable :
      ComputableOnDelta1 (fun n : Nat => (n : Int)) f := by
    unfold ComputableFixpointDetector1 at hcomputable
    unfold ComputableOnDelta1 at hcomputable ⊢
    apply Computable₂.mk
    have hpair :
        Computable fun p : Nat × Nat => ((p.1 : Int), p.2) :=
      (computable_natCast_int.comp Computable.fst).pair Computable.snd
    exact
      Computable.comp
        (α := Nat × Nat) (β := Int × Nat) (σ := Bool)
        hcomputable hpair
  apply hrestricted
  refine
    ⟨(fun input n => f (δ0 (input : Int)) n), hnatComputable, ?_, ?_⟩
  · intro input n hfirst
    exact hsound (input : Int) n hfirst
  · intro input n hzero
    exact hcomplete (input : Int) n hzero

end FPDUndecidability

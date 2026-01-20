-- Some basic properties about Ckt, mainly related to causality
import DBSP.Circuits.Circuits_v6

namespace CktBasic

lemma Ckt_generalize_ns_1 {A B: VType} {P: Ckt A B 1 -> Prop}
  (h: ∀ ns (c: Ckt A B ns), ns = 1 ->
    match ns with
    | false => True
    | true => P c):
    ∀ (c: Ckt A B 1), P c := by
  intros c; specialize h 1 c (by tauto); apply h

-- lemmas on sprod, spord2 and sprodO
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

-- theorems on circuits' causality
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

-- unfold lemmas for loops
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

end CktBasic

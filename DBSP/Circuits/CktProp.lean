-- Some basic properties about Ckt, mainly related to causality
import DBSP.Circuits.Circuits

namespace CktBasic

lemma Ckt_generalize_ns_0 {A B: VType} {P: Ckt A B 0 -> Prop}
  (h: ∀ ns (c: Ckt A B ns), ns = 0 ->
    match ns with
    | true => True
    | false => P c):
    ∀ (c: Ckt A B 0), P c := by
  intros c; specialize h 0 c (by tauto); apply h

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

@[simp]
lemma lifting_spord_add {a: Type}
  [AddCommMonoid a] (x y: stream a):
    ↑↑(fun x => x.1 + x.2) (sprod (x, y)) = x + y := by
  funext k; simp

@[simp]
lemma lifting_binary_sprod {a b c: Type}
  (f: a -> b -> c) x y:
    ↑↑ (fun x => f x.1 x.2) (sprod (x, y)) = (fun i => f (x i) (y i)) := by
  funext k; simp

@[simp]
lemma lifting2_binary_sprod2 {a b c: Type}
  (f: a -> b -> c) x y:
    ↑↑↑↑ (fun x => f x.1 x.2) (sprod2 (x, y)) = (fun i j => f (x i j) (y i j)) := by
  funext i j; simp

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

lemma unfold_sprodO {ns: Bool} {a b: Type}
  (x: stream (Optstream ns (a × b))):
    x = sprodO ns (liftO ns Prod.fst x, liftO ns Prod.snd x) := by
  rcases ns
  · funext _; simp
  · funext _ _; simp

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

lemma D_lifting_delay_comm {a: Type} [AddCommGroup a] (x: stream (stream a)):
    D (↑↑z⁻¹ x) = ↑↑z⁻¹ (D x) := by
  funext m n
  simp [D]
  rcases m <;> rcases n <;> simp

lemma D_lifting_delta_comm {a: Type} [AddCommGroup a] (x: stream a):
    D (↑↑δ0 x) = ↑↑δ0 (D x) := by
  funext m n
  simp [D]
  rcases m <;> rcases n <;> simp

lemma D_sprod2 {a b: Type} [AddCommGroup a] [AddCommGroup b]
  (x: stream (stream a)) (y: stream (stream b)):
    D (sprod2 (x, y)) = sprod2 (D x, D y) := by
  funext m n; simp
  by_cases m = 0
  · subst m; simp
  · repeat' rw [derivative_difference_t] <;> try omega
    simp

lemma D_sprodO {ns: Bool} {a b: Type} [AddCommGroup a] [AddCommGroup b]
  (x: stream (Optstream ns a)) (y: stream (Optstream ns b)):
    D (sprodO ns (x, y)) = sprodO ns (D x, D y) := by
  rcases ns <;> simp [sprodO]
  · apply derivative_sprod
  · rw [D_sprod2]

lemma I_sprodO {ns: Bool} {a b: Type} [AddCommGroup a] [AddCommGroup b]
  (x: stream (Optstream ns a)) (y: stream (Optstream ns b)):
    I (sprodO ns (x, y)) = sprodO ns (I x, I y) := by
  rcases ns <;> simp [sprodO]
  · apply integral_sprod
  · apply integral_sprod2

lemma agreeUpto_delay_succ {A: Type} [Zero A]
  (s1 s2: stream A) (n: ℕ):
    (z⁻¹ s1 =[n+1]= z⁻¹ s2) <-> (s1 =[n]= s2) := by
  constructor <;> intro h
  · intro t ht
    specialize h (t+1) (by omega)
    simp at h; tauto
  · intro t ht
    rcases t with _|t'
    · simp
    simp; apply h; omega

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
  induction c <;> simp [denote, -liftO_id] <;> try apply causalO_liftO
  case seq ns _ _ _ c1 c2 ih1 ih2 =>
    apply causalO_comp <;> tauto
  case par c1 c2 ih1 ih2 =>
    apply causalO_sprodO <;> tauto
  case delay ns _ =>
    apply causalO_delay
  case lifted_delay _ =>
    apply causalNested_lifting; apply delay_causal
  case lifting ih =>
    apply causalNested_lifting; apply ih
  case loop ns _ _ c ih =>
    rcases ns <;> simp
    · apply loop1_causal; apply ih
    · apply causalNested_loop; apply ih
  case lifted_loop c ih =>
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

theorem lifted_loop_body_strict {a b} (c: Ckt (a ×ᵥ b) b 1) x:
    Strict2 fun s ↦ denote c (sprod2 (x, ↑↑z⁻¹ s)) := by
  apply causalNested_strict2_strict2
  · suffices CausalO true (denote c) by apply this
    apply ckt_causalO
  apply lifting_delay_strict2

theorem lifted_loop_unfold {a b} (c: Ckt (a ×ᵥ b) b 1) x:
    denote (Ckt.lifted_loop c) x = denote c (sprod2 (x, ↑↑z⁻¹ (denote (Ckt.lifted_loop c) x))) := by
  simp [denote]
  nth_rw 1 [fix2_eq]
  apply lifted_loop_body_strict

def lifted_Ckt {ns} {A B: VType} (c: Ckt A B ns): Prop :=
  ∃ f, denote c = ↑↑f

@[simp]
lemma lifted_Ckt_node1 {ns} {A B} [BaseType A] [BaseType B] (f: UnaryNode A B):
    lifted_Ckt (@Ckt.node1 ns A B _ _ f) := by
  rcases ns
  · use f.f; simp [denote, liftO]
  · use ↑↑f.f; simp [denote, liftO]

@[simp]
lemma lifted_Ckt_node2 {ns} {A B C} [BaseType A] [BaseType B] [BaseType C] (f: BinaryNode A B C):
    lifted_Ckt (@Ckt.node2 ns A B C _ _ _ f) := by
  rcases ns
  · use f.f; simp [denote, liftO]
  · use ↑↑f.f; simp [denote, liftO]

@[simp]
lemma lifted_Ckt_id {ns} {A: VType}: lifted_Ckt (@Ckt.id ns A) := by
  rcases ns
  · use id; simp [denote, liftO]
  · use ↑↑id; simp [denote, liftO]

@[simp]
lemma lifted_Ckt_fst {ns} {A B: VType}: lifted_Ckt (@Ckt.fst ns A B) := by
  rcases ns
  · use Prod.fst; simp [denote, liftO]
  · use ↑↑Prod.fst; simp [denote, liftO]

@[simp]
lemma lifted_Ckt_snd {ns} {A B: VType}: lifted_Ckt (@Ckt.snd ns A B) := by
  rcases ns
  · use Prod.snd; simp [denote, liftO]
  · use ↑↑Prod.snd; simp [denote, liftO]

@[simp]
lemma lifted_Ckt_add {ns} {A: VType}: lifted_Ckt (@Ckt.add ns A) := by
  rcases ns
  · use (fun x => x.1 + x.2); simp [denote, liftO]
  · use ↑↑(fun x => x.1 + x.2); simp [denote, liftO]

@[simp]
lemma lifted_Ckt_sub {ns} {A: VType}: lifted_Ckt (@Ckt.sub ns A) := by
  rcases ns
  · use (fun x => x.1 - x.2); simp [denote, liftO]
  · use ↑↑(fun x => x.1 - x.2); simp [denote, liftO]

@[simp]
lemma lifted_Ckt_const {ns} {A B: VType} (x: VType_interp B):
    lifted_Ckt (@Ckt.const ns A B x) := by
  rcases ns <;> simp [lifted_Ckt, denote, liftO]

@[simp]
lemma lifted_Ckt_lifted_delay {A: VType}:
    lifted_Ckt (@Ckt.lifted_delay A) := by
  use z⁻¹; simp [denote, liftO]
@[simp]
lemma lifted_Ckt_lifting {A B: VType} (c: Ckt A B 0):
    lifted_Ckt (c↑ c) := by
  use denote c; simp [lifted_Ckt, denote]

end CktBasic

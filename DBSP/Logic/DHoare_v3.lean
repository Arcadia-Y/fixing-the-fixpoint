import DBSP.CircuitsNew
import DBSP.StreamTheory.Linear
import Mathlib.Algebra.Group.Defs
import DBSP.Dominate
open CktBasic

section DHoare
-- VType_Nat lemmas
lemma VType_Nat_le_add {A: VType} (x1 y1 x2 y2: VType_Nat A)
  (h1: x1 ≤ y1) (h2: x2 ≤ y2):
    x1 + x2 ≤ y1 + y2 := by
  induction A
  · apply Nat.add_le_add <;> tauto
  · rcases h1 with ⟨h11,h12⟩; rcases h2 with ⟨h21,h22⟩
    constructor <;> try tauto

lemma VType_Nat_le_mul {A: VType} (x y: VType_Nat A)
  (k: ℕ) (h: x ≤ y):
    k • x ≤ k • y := by
  induction k; simp
  rw [add_nsmul]; rw [add_nsmul]; simp
  apply VType_Nat_le_add <;> tauto

lemma s_VType_Nat_le_add {A: VType} (x1 y1 x2 y2: stream (VType_Nat A))
  (h1: x1 ≤ y1) (h2: x2 ≤ y2):
    x1 + x2 ≤ y1 + y2 := by
  intro t; simp
  specialize h1 t; specialize h2 t
  apply VType_Nat_le_add <;> tauto

lemma s_VType_Nat_le_mul {A: VType} (x y: stream (VType_Nat A))
  (k: ℕ) (h: x ≤ y):
    k • x ≤ k • y := by
  intro t; simp
  specialize h t
  apply VType_Nat_le_mul; tauto

syntax "sV_linear" : tactic
macro_rules
| `(tactic| sV_linear) =>
    `(tactic| apply s_VType_Nat_le_add; swap; try trivial; apply s_VType_Nat_le_mul <;> try tauto
    )

-- definition of DHoare
@[reducible]
def SOVType (ns: Bool) (A: VType) :=
  stream (Optstream ns (VType_interp A))

@[reducible]
def SONat (ns: Bool) :=
  stream (Optstream ns ℕ)

variable {A B C: VType} {ns: Bool} {c: Ckt ns A B} {x: SOVType ns A}
  {r r1 r2: SONat ns} {Q: SOVType ns B -> Prop}

structure DHoare (c: Ckt ns A B) (x: SOVType ns A)
    (Q: SOVType ns B -> Prop) (k: ℕ) (r: SONat ns) where
  post: Q (denote c x)
  bound: (cost_f c x) <[k] r

variable {k k1 k2: ℕ}

theorem DHoare_conseq (Q': SOVType ns B -> Prop)
  (h: DHoare c x Q k r) (hy: ∀ y, Q y -> Q' y):
    DHoare c x Q' k r := by
  constructor
  case bound => exact h.bound
  apply hy; exact h.post

theorem DHoare_weaken (r': SONat ns)
  (h: DHoare c x Q k1 r) (hr: r <[k2] r'):
    DHoare c x Q (k1 * k2) r' where
  post := h.post
  bound := Dom_trans h.bound hr

theorem DHoare_seq {c1: Ckt ns A B} {c2: Ckt ns B C}
  {Q1: SOVType ns B -> Prop} {Q2: SOVType ns C -> Prop}
  (h1: DHoare c1 x Q1 k1 r1) (h2: ∀ y, Q1 y -> DHoare c2 y Q2 k2 r2):
    DHoare (c1 >>c c2) x Q2 (max k1 k2) (r1 + r2) := by
  specialize h2 (denote c1 x) (h1.post)
  constructor
  case post => exact h2.post
  case bound =>
    simp [cost_f]
    apply Dom_add_Dom
    exact h1.bound; exact h2.bound

theorem DHoare_par {c1: Ckt ns A B} {c2: Ckt ns A C}
  {Q1: SOVType ns B -> Prop} {Q2: SOVType ns C -> Prop}
  (h1: DHoare c1 x Q1 k1 r1) (h2: DHoare c2 x Q2 k2 r2):
    DHoare (c1 &&c c2) x
      (fun y => Q1 ((liftO ns Prod.fst) y) ∧ Q2 ((liftO ns Prod.snd) y))
      (max k1 k2) (r1 + r2) := by
  constructor
  case post =>
    simp [denote]; constructor
    apply h1.post; apply h2.post
  case bound =>
    simp [cost_f]
    apply Dom_add_Dom
    exact h1.bound; exact h2.bound

theorem DHoare_lifting {c: Ckt false A B} {x: stream (stream (VType_interp A))}
  {Q: stream (VType_interp B) -> Prop} {r: stream (stream ℕ)}
  (h: ∀ i, DHoare c (x i) Q k (r i)):
    DHoare (c↑ c) x (fun y => ∀ i, Q (y i)) k r := by
  constructor
  case post =>
    intro i; simp [denote]; apply (h i).post
  case bound =>
    intro i; simp [cost_f]
    specialize h i; apply h.bound

theorem DHoare_loop {c: Ckt ns (A ×ᵥ B) B}
  {x: SOVType ns A} {r: SONat ns}
  (I: (Optstream ns (VType_interp B)) -> Prop)
  (s: SONat ns) (h0: I 0)
  (ih: ∀ y n, I ((z⁻¹ y) n) -> DHoare c (sprodO ns (x, z⁻¹ y)) (fun y' => I (y' n)) k1 r)
  (hs: ∀ y, (∀ n, I (y n)) -> liftO ns VType_space y <[k2] s) :
    DHoare (cloop c) x (fun y' => ∀ n, I (y' n)) (max k1 k2) (r + s) := by
  have hStr: Strict fun s ↦ denote c (sprodO ns (x, z⁻¹ s)) := by
    sorry
  have hId: ∀ (n : ℕ), I (denote (cloop c) x n) := by
    simp [denote]
    set fp := fix fun s ↦ denote c (sprodO ns (x, z⁻¹ s))
    specialize ih fp
    intro n; induction n
    · specialize ih 0; simp at ih
      specialize ih h0
      have := ih.post
      subst fp; rewrite [fix_eq]; tauto
      apply hStr
    · rename_i n hn
      specialize ih (n+1) hn
      have := ih.post
      subst fp; rewrite [fix_eq]; tauto
      apply hStr
  constructor; tauto
  simp [cost_f]
  set y0 := (denote (cloop c) x)
  specialize ih y0
  apply Dom_add_Dom
  · intro t
    specialize ih t (by
      rcases t; apply h0
      apply hId
    )
    apply ih.bound
  · apply hs; tauto

@[simp]
def transpose {A: Type} (s: stream (stream A)): stream (stream A) :=
  fun n m => s m n
notation "TP" => transpose

@[simp]
lemma transpose_apply {A: Type} (s: stream (stream A)) (n m: ℕ):
  TP s n m = s m n := by rfl

theorem DHoare_loop_lifted {c: Ckt 1 (A ×ᵥ B) B}
  {x: stream (stream (VType_interp A))} {r: stream (stream ℕ)}
  (I: (stream (VType_interp B)) -> Prop)
  (s: stream (stream ℕ)) (h0: I 0)
  (ih: ∀ y n, I  (TP (↑↑z⁻¹ y) n) -> DHoare c (sprod2 (x, ↑↑z⁻¹ y)) (fun y' => I (TP y' n)) k1 r)
  (hs: ∀ y, (∀ n, I (TP y n)) -> liftO 1 VType_space y <[k2] s) :
    DHoare (cloop2 c) x (fun y' => ∀ n, I (TP y' n)) (max k1 k2) (r + s) := by
  have hStr: Strict fun s ↦ denote c (sprod2 (x, ↑↑z⁻¹ s)) := by
    sorry
  have hId: ∀ (n : ℕ), I (TP (denote (cloop2 c) x) n) := by
    simp [denote]
    set fp := fix fun s ↦ denote c (sprod2 (x, ↑↑z⁻¹ s))
    specialize ih fp
    intro n; induction n
    · specialize ih 0
      specialize ih h0
      have := ih.post
      subst fp; rewrite [fix_eq]; apply this
      apply hStr
    · rename_i n hn
      specialize ih (n+1) hn
      have := ih.post
      subst fp; rewrite [fix_eq]; tauto
      apply hStr
  constructor; tauto
  simp [cost_f]
  set y0 := (denote (cloop2 c) x)
  specialize ih y0
  apply Dom_add_Dom
  · intro t
    specialize ih t (by
      rcases t; apply h0
      apply hId
    )
    apply ih.bound
  · apply hs; tauto

theorem DHoare_bracket {c: Ckt 1 A B}
  {x: stream (VType_interp A)} {r: stream (stream ℕ)}
  {Q: stream (stream (VType_interp B)) -> Prop} (b: stream ℕ)
  (h: DHoare c (↑↑δ0 x) Q k r)
  (hb: ∀ y, Q y -> ∀ i, ZeroAfter (y i) (b i)) :
    DHoare (cbracket c) x
      (fun y => ∃ m, Q m ∧ ∀ i, y i = sumVals (m i) (b i))
      k (fun i => sumVals (r i) (b i)) := by
  set m := denote c (↑↑δ0 x)
  have : Q m := h.post
  specialize hb m this
  constructor
  case post =>
    simp [denote]
    use m; constructor; tauto
    intro i; simp [streamElim]
    specialize hb i
    cases Classical.propDecidable (∃ n, ZeroAfter (m i) n)
    · rename_i con; exfalso; apply con
      use (b i)
    · rename_i hn
      simp; sorry
  case bound =>
    simp [cost_f]; intro i; simp
    specialize hb i
    set spec := ∃ n, ZeroAfter (denote c (↑↑δ0 x) i) n ∧ ∀ m < n, ¬denote c (↑↑δ0 x) i m = 0
    cases Classical.propDecidable spec
    · rename_i con; exfalso; apply con
      use (b i); constructor; tauto
      sorry
    · rename_i hs; simp
      sorry

theorem SizeBound_delay:
    SizeBound (@Ckt.delay A) id := by
  constructor; apply MonoDom_id
  intros input
  simp [denote]; apply

theorem SizeBound_id:
    SizeBound (@Ckt.id A) id := by
  intros input i_bound hi
  simp [denote]; tauto

theorem SizeBound_fst:
    SizeBound (@Ckt.fst A B) (↑↑Prod.fst) := by
  intros input i_bound hi
  simp [denote]; intro t; simp
  specialize hi t
  rcases hi; tauto

theorem SizeBound_snd:
    SizeBound (@Ckt.snd A B) (↑↑Prod.snd) := by
  intros input i_bound hi
  simp [denote]; intro t; simp
  specialize hi t
  rcases hi; tauto

--- CostBound Rules
theorem CostBound_weaken cb {cb'}
  (H: CostBound c cb)
  (Hs: cb ≤ cb'):
    CostBound c cb' := by
  intros input i_bound; intro hi
  specialize H input i_bound hi
  eapply le_trans
  swap; apply Hs
  tauto

theorem CostBound_seq {C: VType} (c1: Ckt A B) (c2: Ckt B C)
  sb1 cb1 cb2 (H1s: SizeBound c1 sb1)
  (H1c: CostBound c1 cb1) (H2c: CostBound c2 cb2) :
    CostBound (c1 >>c c2) (fun is => cb1 is + cb2 (sb1 is)) := by
  intros input i_bound hi
  specialize H1s input i_bound hi
  specialize H1c input i_bound hi
  specialize H2c (denote c1 input) (sb1 i_bound) H1s
  simp [cost_f]; intro t; simp
  specialize H1c t; specialize H2c t
  apply Nat.add_le_add <;> tauto

theorem CostBound_par {C: VType} (c1: Ckt A B) (c2: Ckt A C)
  cb1 cb2 (H1c: CostBound c1 cb1) (H2c: CostBound c2 cb2) :
    CostBound (c1 &&c c2) (fun is => cb1 is + cb2 is) := by
  intros input i_bound hi
  specialize H1c input i_bound hi
  specialize H2c input i_bound hi
  simp [cost_f]; intro t; simp
  specialize H1c t; specialize H2c t
  apply Nat.add_le_add <;> tauto

theorem CostBound_loop (c: Ckt (A ×ᵥ B) B) cb sb'
  (Hc: CostBound c cb) (Hs: SizeBound (cloop c) sb') :
    CostBound
      (cloop c)
      (fun x => cb (x, z⁻¹ (sb' x)) + (↑↑PType_sum) (sb' x)) := by
  intros input i_bound hi
  set o := denote (cloop c) input
  simp [cost_f]; intro t; simp
  specialize Hc (input, z⁻¹ o) (i_bound, z⁻¹ (sb' i_bound)); simp at Hc
  specialize Hc (by
    intro t; simp; constructor <;> try tauto
    rw [VType_size_delay]; apply le_delay; tauto
    )
  specialize Hc t
  specialize Hs input i_bound hi
  specialize Hs t; simp at Hs
  have := PType_sum_Nat_mono _ _ Hs
  apply Nat.add_le_add <;> tauto

theorem CostBound_delay:
    CostBound (@Ckt.delay A) (↑↑PType_sum) := by
  intros input i_bound hi
  simp [cost_f]; intro t; simp
  apply PType_sum_Nat_mono; tauto

theorem CostBound_id:
    CostBound (@Ckt.id A) 0 := by
  intros input i_bound hi
  intro t; simp; simp [cost_f]

theorem CostBound_fst:
    CostBound (@Ckt.fst A B) 0 := by
  intros input i_bound hi
  intro t; simp; simp [cost_f]

theorem CostBound_snd:
    CostBound (@Ckt.snd A B) 0 := by
  intros input i_bound hi
  intro t; simp; simp [cost_f]

--- DHoare Rules
theorem DHoare_weaken_size sb {cb sb'}
  (H: DHoare c sb cb)
  (Hs: sb ≤ sb'):
    DHoare c sb' cb := by
  simp [DHoare] at *
  constructor <;> try tauto
  apply SizeBound_weaken <;> tauto

theorem DHoare_weaken_cost cb {sb cb'}
  (H: DHoare c sb cb)
  (Hs: cb ≤ cb'):
    DHoare c sb cb' := by
  simp [DHoare] at *
  constructor <;> try tauto
  apply CostBound_weaken <;> tauto

theorem DHoare_weaken sb cb {sb' cb'}
  (H: DHoare c sb cb)
  (Hs: sb ≤ sb') (Hc: cb ≤ cb'):
    DHoare c sb' cb' := by
  apply DHoare_weaken_size _ sb <;> try tauto
  apply DHoare_weaken_cost _ cb <;> tauto

theorem DHoare_seq {C: VType} (c1: Ckt A B) (c2: Ckt B C)
  sb1 sb2 cb1 cb2
  (H1: DHoare c1 sb1 cb1) (H2: DHoare c2 sb2 cb2) :
    DHoare (c1 >>c c2) (sb2 ∘ sb1) (fun is => cb1 is + cb2 (sb1 is)) := by
  simp [DHoare] at *; constructor
  · apply SizeBound_seq <;> tauto
  · apply CostBound_seq <;> tauto

theorem DHoare_par {C: VType} (c1: Ckt A B) (c2: Ckt A C)
  sb1 sb2 cb1 cb2
  (H1: DHoare c1 sb1 cb1) (H2: DHoare c2 sb2 cb2) :
    DHoare (c1 &&c c2)
           (fun is => (sb1 is, sb2 is))
           (fun is => cb1 is + cb2 is) := by
  simp [DHoare] at *; constructor
  · apply SizeBound_par <;> tauto
  · apply CostBound_par <;> tauto

theorem DHoare_loop
  (c: Ckt (A ×ᵥ B) B) sb cb (sb': Operator (VType_Nat A) (VType_Nat B))
  (H: DHoare c sb cb)
  (sb_ind: ∀ x, sb (x, z⁻¹ (sb' x)) ≤ sb' x) :
    DHoare (cloop c)
            sb'
           (fun x => cb (x, z⁻¹ (sb' x)) + (↑↑PType_sum) (sb' x)) := by
  simp [DHoare] at *
  have := SizeBound_loop c sb sb' (by tauto) sb_ind
  constructor <;> try tauto
  apply CostBound_loop <;> tauto

theorem DHoare_delay:
    DHoare (@Ckt.delay A) z⁻¹ (↑↑PType_sum) := by
  simp [DHoare]; constructor
  apply SizeBound_delay; apply CostBound_delay


theorem DHoare_id:
    DHoare (@Ckt.id A) id 0 := by
  simp [DHoare]; constructor
  apply SizeBound_id; apply CostBound_id

def DHoare_id (x: SOVType ns A):
    DHoare (@Ckt.id ns A) x (fun y => y = x) 0 := by
  constructor
  · simp [denote]
  · simp [cost_f]; apply Dom_refl

theorem DHoare_fst:
    DHoare (@Ckt.fst A B) (↑↑Prod.fst) 0 := by
  simp [DHoare]; constructor
  apply SizeBound_fst; apply CostBound_fst

theorem DHoare_snd:
    DHoare (@Ckt.snd A B) (↑↑Prod.snd) 0 := by
  simp [DHoare]; constructor
  apply SizeBound_snd; apply CostBound_snd

end DHoare

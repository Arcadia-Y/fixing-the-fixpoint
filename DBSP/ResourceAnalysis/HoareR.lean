import DBSP.Logic.HoareT
import DBSP.ResourceAnalysis.CktCost
import DBSP.ResourceAnalysis.Dominate
open CktBasic

section HoareR
variable {A B C: VType} {ns: Bool} {c: Ckt A B ns}
  {r r1 r2: SOType ns ℕ} {x: SOVType ns A}
  {P: SOVType ns A -> Prop} {Q: SOVType ns B -> Prop}

-- Hoare logic with resource bound
structure HoareR
    (P: SOVType ns A -> Prop)
    (c: Ckt A B ns)
    (Q: SOVType ns B -> Prop)
    (r: SOType ns ℕ) where
  post: HoareT P c Q
  cost: ∀ x, (h: P x) -> cost_f c x (post x h).1 ≤ r

variable {k k1 k2: ℕ}

theorem HoareR_conseq_pre
  {P': SOVType ns A -> Prop}
  (h: HoareR P' c Q r)
  (hp: ∀ x, P x -> P' x):
    HoareR P c Q r := by
  constructor
  case post =>
    apply HoareT_conseq_pre h.post hp
  case cost =>
    intro x hx
    apply h.cost
    apply hp x hx

theorem HoareR_conseq_post
  {Q': SOVType ns B -> Prop}
  (h: HoareR P c Q' r)
  (hq: ∀ x, Q' x -> Q x):
    HoareR P c Q r := by
  constructor
  case post =>
    apply HoareT_conseq_post h.post hq
  case cost =>
    intro x hx
    apply h.cost x hx

theorem HoareR_conseq
  {P': SOVType ns A -> Prop} {Q': SOVType ns B -> Prop}
  (h: HoareR P' c Q' r)
  (hp: ∀ x, P x -> P' x)
  (hq: ∀ x, Q' x -> Q x):
    HoareR P c Q r := by
  apply HoareR_conseq_pre
  apply HoareR_conseq_post h hq
  apply hp

theorem HoareT_to_HoareR
  (ht: HoareT P c Q)
  (hr: ∀ x, (hx: P x) -> cost_f c x (ht x hx).1 ≤ r):
    HoareR P c Q r := by
  constructor
  case post => exact ht
  case cost =>
    intro x hx
    apply hr; tauto

theorem HoareT_to_HoareR' {Q'}
  (ht: HoareT P c Q)
  (hr: HoareR P c Q' r):
    HoareR P c Q r := by
  constructor
  case post => exact ht
  case cost =>
    intro x hx
    apply hr.cost; tauto

theorem HoareR_weaken_bound
  (r': SOType ns ℕ)
  (h: HoareR P c Q r)
  (hr: r ≤ r'):
    HoareR P c Q r' := by
  constructor
  case post => exact h.post
  case cost =>
    intro x hx
    apply le_trans
    apply h.cost x hx
    apply hr

theorem HoareR_seq {c1: Ckt A B ns} {c2: Ckt B C ns}
  {Q1: SOVType ns B -> Prop} {Q2: SOVType ns C -> Prop}
  {r1 r2: SOType ns ℕ}
  (h1: HoareR P c1 Q1 r1)
  (h2: HoareR Q1 c2 Q2 r2):
    HoareR P (c1 >>c c2) Q2 (r1 + r2) := by
  constructor
  case post =>
    apply HoareT_seq h1.post h2.post
  case cost =>
    intro x hx
    simp [cost_f]
    apply add_le_add
    · apply h1.cost x hx
    · apply h2.cost (denote c1 x)
      exact (h1.post x hx).2

theorem HoareR_par {c1: Ckt A B ns} {c2: Ckt A C ns}
  {Q1: SOVType ns B -> Prop} {Q2: SOVType ns C -> Prop}
  {r1 r2: SOType ns ℕ}
  (h1: HoareR P c1 Q1 r1)
  (h2: HoareR P c2 Q2 r2):
    HoareR P (c1 &&c c2)
      (fun y => Q1 (liftO ns Prod.fst y) ∧ Q2 (liftO ns Prod.snd y))
      (r1 + r2) := by
  constructor
  case post =>
    apply HoareT_par h1.post h2.post
  case cost =>
    intro x hx
    simp [cost_f]
    apply add_le_add
    · apply h1.cost x hx
    · apply h2.cost x hx

theorem HoareR_par' {c1: Ckt A B ns} {c2: Ckt A C ns}
  {Q1: SOVType ns B -> Prop} {Q2: SOVType ns C -> Prop}
  {r1 r2: SOType ns ℕ}
  (h1: HoareR P c1 Q1 r1)
  (h2: HoareR P c2 Q2 r2):
    HoareR P (c1 &&c c2)
      (fun y => ∃ y1 y2, y = sprodO ns (y1, y2) ∧ Q1 y1 ∧ Q2 y2)
      (r1 + r2) := by
  apply HoareR_conseq_post
  apply HoareR_par h1 h2
  rintro y ⟨hy1, hy2⟩
  use liftO ns Prod.fst y, liftO ns Prod.snd y
  simp [*]
  rcases ns <;> simp
  funext _; simp
  funext _ _; simp

theorem HoareR_delay:
    HoareR (fun y => y = x) (@Ckt.delay ns A) (fun y => y = z⁻¹ x) (liftO ns VType_space x) := by
  constructor
  case post =>
    intro y hy; subst hy; simp [Terminate, denote]
  case cost =>
    intro y hy; subst hy; simp [cost_f]

theorem HoareR_id:
    HoareR (fun y => y = x) (@Ckt.id ns A) (fun y => y = x) 0 := by
  constructor
  case post =>
    intro y hy; subst hy; simp [Terminate, denote]
  case cost =>
    intro y hy; subst hy; simp [cost_f]

theorem HoareR_fst {x: SOVType ns (A×ᵥB)}:
    HoareR (fun y => y = x) (@Ckt.fst ns A B) (fun y => y = liftO ns Prod.fst x) 0 := by
  constructor
  case post =>
    intro y hy; subst hy; simp [Terminate, denote]
  case cost =>
    intro y hy; subst hy; simp [cost_f]

theorem HoareR_snd {x: SOVType ns (A×ᵥB)}:
    HoareR (fun y => y = x) (@Ckt.snd ns A B) (fun y => y = liftO ns Prod.snd x) 0 := by
  constructor
  case post =>
    intro y hy; subst hy; simp [Terminate, denote]
  case cost =>
    intro y hy; subst hy; simp [cost_f]

theorem HoareR_add {x1 x2: SOVType ns A}:
    HoareR (fun y => y = sprodO ns (x1, x2)) Ckt.add
      (fun y => y = x1 + x2) (liftO ns add_cost (sprodO ns (x1, x2)))  := by
  constructor
  case post =>
    intro y hy; subst hy; simp [Terminate, denote]
    rcases ns <;> simp
    funext _ _; simp
  case cost =>
    intro y hy; subst hy; simp [cost_f]

theorem HoareR_sub {x1 x2: SOVType ns A}:
    HoareR (fun y => y = sprodO ns (x1, x2)) Ckt.sub
      (fun y => y = x1 - x2) (liftO ns sub_cost (sprodO ns (x1, x2)))  := by
  constructor
  case post =>
    intro y hy; subst hy; simp [Terminate, denote]
    rcases ns <;> simp
    funext _; simp
    funext _ _; simp
  case cost =>
    intro y hy; subst hy; simp [cost_f]

theorem HoareR_loop {c: Ckt (A ×ᵥ B) B ns}
  {Q: SOVType ns B -> Prop}
  (ht: HoareT P (cloop c) Q)
  (hc: ∀ x y, P x -> Q y ->
    HoareR (fun z => z = sprodO ns (x, z⁻¹ y)) c (fun _ => True) r1)
  (hs: ∀ y, Q y -> liftO ns VType_space y ≤ r2):
    HoareR P (cloop c) Q (r1 + r2) := by
  constructor
  case post => exact ht
  case cost =>
    intro x hx; simp [cost_f]
    specialize ht x (by simp [hx])
    specialize hc _ _ hx ht.2
    apply add_le_add
    · apply hc.cost; rfl
    · apply hs; tauto

theorem HoareR_lifted_loop {c: Ckt (A ×ᵥ B) B 1}
  {r1 r2: SOType 1 ℕ}
  {P: SOVType 1 A -> Prop}
  {Q: SOVType 1 B -> Prop}
  (ht: HoareT P (cloop2 c) Q)
  (hc: ∀ x y, P x -> Q y ->
    HoareR (fun z => z = sprod2 (x, ↑↑z⁻¹ y)) c (fun _ => True) r1)
  (hs: ∀ y, Q y -> ↑↑↑↑VType_space y ≤ r2):
    HoareR P (cloop2 c) Q (r1 + r2) := by
  constructor
  case post => exact ht
  case cost =>
    intro x hx; simp [cost_f]
    specialize ht x (by simp [hx])
    specialize hc _ _ hx ht.2
    apply add_le_add
    · apply hc.cost; rfl
    · apply hs; tauto

theorem HoareR_lifting {c: Ckt A B 0}
  {P: ℕ -> SOVType 0 A -> Prop} {Q: ℕ -> SOVType 0 B -> Prop} {r: stream (stream ℕ)}
  (h: ∀ j, HoareR (P j) c (Q j) (r j)):
    HoareR (fun x => ∀ j, P j (x j)) (c↑ c) (fun y => ∀ j, Q j (y j)) r := by
  constructor
  case post =>
    apply HoareT_lifting
    intro j; apply (h j).post
  case cost =>
    intro x hx j; simp [cost_f]
    have hc := (h j).cost
    apply hc; tauto

open Classical in
theorem HoareR_bracket {c: Ckt A B 1}
  {P: SOVType 0 A -> Prop} {Q: SOVType 1 B -> Prop}
  (b: stream ℕ) (r1 r2: stream (stream ℕ))
  (hr: ∀ y, P y -> HoareR (fun x => x = ↑↑δ0 y) c Q r1)
  (hi: ∀ y, P y -> HoareI2 (fun x => x = ↑↑δ0 y) c (fun _ => True) b)
  (hb: ∀ z, Q z -> ZeroAfterVec z b)
  (hic: ∀ z, Q z -> ∀ i, HoareR (fun x => x = z i) (cI (ns:=0)) (fun _ => True) (r2 i)):
    HoareR P (cbracket c) (fun y => ∃ z, Q z ∧ ∀ i, y i = I (z i) (b i)) (fun i => I (r1 i + r2 i) (b i)) := by
  constructor
  case post =>
    apply HoareT_bracket <;> try tauto
    intro y hy; specialize hr y hy
    apply hr.post
  case cost =>
    intro x hx i; simp [cost_f]
    specialize hr x hx
    rcases hr with ⟨ht, hc⟩
    specialize ht _ rfl
    specialize hc _ rfl
    specialize hi x hx _ rfl
    apply le_trans; apply mono_integral_stream (b:=(b i))
    · apply Nat.find_min'; tauto
    apply (stream_le_ext _ _).1
    rw [integral_linear, integral_linear (x:= r1 i)]
    apply add_le_add
    · apply mono_integral
      apply hc
    apply mono_integral
    specialize hic _ (by tauto) i
    have hic := hic.cost _ rfl
    apply hic

lemma HoareR_sintro
  (h: ∀ v, P v -> HoareR (fun x => x = v) c Q r):
    HoareR P c Q r := by
  constructor
  case post =>
    intro x hx; specialize h x hx
    apply h.post; simp
  case cost =>
    intro x hx; specialize h x hx
    apply h.cost; simp

lemma HoareR_I:
    HoareR
      (fun y => y = x) cI (fun y => y = I x)
      (liftO ns add_cost (sprodO ns (x, z⁻¹ (I x))) + liftO ns VType_space (I x)) := by
  unfold cI
  apply HoareR_loop
  case ht =>
    rw [<- cI]; simp [HoareT]
    rcases ns <;> simp
  case hc =>
    intro a b ha hb ; subst a b
    apply HoareR_conseq_post
    apply HoareR_add; tauto
  case hs =>
    simp

lemma HoareR_D:
    HoareR
      (fun y => y = x) cD (fun y => y = D x)
      (liftO ns VType_space x + liftO ns sub_cost (sprodO ns (x, z⁻¹ x))) := by
  constructor
  case post =>
    simp [HoareT]
  case cost =>
    intro y hy; subst hy
    rcases ns <;> simp [cD, cost_f, denote]

theorem HoareR_lifted_delay (x: SOVType 1 A):
    HoareR (fun y => y = x) (c↑z⁻¹) (fun y => y = ↑↑z⁻¹ x) (↑↑↑↑VType_space x) := by
  constructor
  case post =>
    intro y hy; subst hy; simp [Terminate, denote]
  case cost =>
    intro y hy; subst hy; simp [cost_f]

theorem HoareR_lifted_I (x: SOVType 1 A):
    HoareR (fun y => y = x) (c↑I) (fun y => y = ↑↑I x)
      (liftO 1 add_cost (sprod2 (x, ↑↑z⁻¹ (↑↑I x))) + ↑↑↑↑VType_space (↑↑I x)) := by
  unfold lifted_I
  apply HoareR_lifted_loop
  case ht =>
    rw [<- lifted_I]; simp [HoareT, Terminate]
    unfold lifted_I; simp [Terminate]
  case hc =>
    intro a b ha hb; subst a b
    apply HoareR_conseq_post
    apply HoareR_add; tauto
  case hs =>
    simp

end HoareR

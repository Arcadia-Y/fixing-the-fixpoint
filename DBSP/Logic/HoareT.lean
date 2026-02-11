-- Hoare logic for total correctness
import DBSP.Logic.Hoare
import DBSP.Practical.Refine
import DBSP.Practical.Preserve
import DBSP.Practical.PushLifting
open CktBasic

section HoareT
variable {A B C: VType} {ns: Bool}

-- Non-step-indexed Hoare triple for total correctness
def HoareT (P: SOVType ns A -> Prop)
    (c: Ckt A B ns) (Q: SOVType ns B -> Prop) :=
  ∀ x, P x -> Terminate c x ∧ Q (denote c x)

variable {c: Ckt A B ns} {P: SOVType ns A -> Prop} {Q: SOVType ns B -> Prop}

-- Hoare triple to reason about IntFP1
def HoareI1 (P: SOVType ns A -> Prop)
    (c: Ckt A B ns) (Q: SOVType ns B -> Prop) (b: ℕ) : Prop :=
  ∀ x, P x -> IntFP1 c x b ∧ Q (denote c x)

-- Hoare triple to reason about IntFP2
def HoareI2 (P: SOVType 1 A -> Prop)
    (c: Ckt A B 1) (Q: SOVType 1 B -> Prop) (b: stream ℕ) : Prop :=
  ∀ x, P x -> IntFP2Vec c x b ∧ Q (denote c x)

-- HoareT theorems

theorem HoareT_conseq_pre {P': SOVType ns A -> Prop}
  (h: HoareT P' c Q)
  (hp: ∀ x, P x -> P' x):
    HoareT P c Q := by
  intro x hx
  apply h
  apply hp
  assumption

theorem HoareT_conseq_post {Q': SOVType ns B -> Prop}
  (h: HoareT P c Q)
  (hq: ∀ x, Q x -> Q' x):
    HoareT P c Q' := by
  intro x hx
  rcases h x hx with ⟨ht, hQ⟩
  constructor
  · assumption
  · apply hq; assumption

theorem HoareT_True:
    HoareT P c (fun _ => True) <-> (∀ x, P x -> Terminate c x) := by
  simp [HoareT]

theorem Hoare_to_HoareT
  (hh: Hoare (fun x _ => P x) c (fun y _ => Q y))
  (ht: HoareT P c (fun _ => True)):
    HoareT P c Q := by
  rw [HoareT_True] at ht
  intro x hx
  constructor
  · apply ht; assumption
  · specialize hh x 1 (by intro k hk; exact hx)
    exact hh 0 (by omega)

theorem Hoare_to_HoareT_indexed {P: SPred (OVType ns A)} {Q: SPred (OVType ns B)}
  (hh: Hoare P c Q)
  (ht: HoareT (fun x => ∀ i, P x i) c (fun _ => True)):
    HoareT (fun x => ∀ i, P x i) c (fun y => ∀ j, Q y j) := by
  rw [HoareT_True] at ht
  intro x hx
  constructor
  · apply ht; assumption
  · intro j
    specialize hh x (j + 1) (by intro k hk; apply hx)
    apply hh; omega

lemma fun_stream_eq_forall {T: Type} {s: stream T}:
    (fun x => x = s) = (fun x => ∀ i, x i = s i) := by
  funext k; simp
  constructor <;> intro h
  rw [h]; simp
  funext i; apply h

theorem HoareT_Sequiv_cong {c1 c2: Ckt A B ns}
  (h: c1 ≃ c2):
    HoareT P c1 Q <-> HoareT P c2 Q := by
  unfold HoareT
  apply forall_congr'; intro x
  apply imp_congr_right; intro hP
  unfold Sequiv at h; rcases h with ⟨hd, ht⟩
  rw [hd, ht]

theorem HoareT_Refine {c1 c2: Ckt A B ns}
  (h: c1 ⊑ c2) (h1: HoareT P c1 Q):
    HoareT P c2 Q := by
  unfold HoareT at h1 ⊢
  intro x hx
  specialize h1 _ hx
  specialize h x (by tauto)
  rcases h with ⟨h2, h3⟩
  rw [<- h3]; tauto

theorem HoareT_seq {c1: Ckt A B ns} {c2: Ckt B C ns}
  {Q1: SOVType ns B -> Prop} {Q2: SOVType ns C -> Prop}
  (h1: HoareT P c1 Q1) (h2: HoareT Q1 c2 Q2):
    HoareT P (c1 >>c c2) Q2 := by
  intro x hx
  rcases h1 x hx with ⟨t1, q1⟩
  rcases h2 (denote c1 x) q1 with ⟨t2, q2⟩
  constructor
  · simp [Terminate]; constructor <;> assumption
  · simp [denote]; assumption

theorem HoareT_par {c1: Ckt A B ns} {c2: Ckt A C ns}
  {Q1: SOVType ns B -> Prop} {Q2: SOVType ns C -> Prop}
  (h1: HoareT P c1 Q1) (h2: HoareT P c2 Q2):
    HoareT P (c1 &&c c2) (fun y => Q1 (liftO ns Prod.fst y) ∧ Q2 (liftO ns Prod.snd y)) := by
  intro x hx
  rcases h1 x hx with ⟨t1, q1⟩
  rcases h2 x hx with ⟨t2, q2⟩
  constructor
  · simp [Terminate]; constructor <;> assumption
  · simp [denote, liftO, sprodO]; constructor <;> rcases ns <;> assumption

theorem HoareT_conj {Q1: SOVType ns B -> Prop} {Q2: SOVType ns B -> Prop}
  (h1: HoareT P c Q1) (h2: HoareT P c Q2):
    HoareT P c (fun y => Q1 y ∧ Q2 y) := by
  intro x hx
  rcases h1 x hx with ⟨t1, q1⟩
  rcases h2 x hx with ⟨t2, q2⟩
  constructor
  · assumption
  · constructor <;> assumption

theorem HoareT_loop {c: Ckt (A ×ᵥ B) B ns}
  {P: SPred (OVType ns A)} {Q: SPred (OVType ns B)}
  (hh: Hoare P (cloop c) Q)
  (ht: ∀ x1 x2, (∀ i, P x1 i) -> (∀ i, Q x2 i) ->
    HoareT (fun x => x = sprodO ns (x1, z⁻¹ x2)) c (fun _ => True)):
    HoareT (fun x => ∀ i, P x i) (cloop c) (fun y => ∀ j, Q y j) := by
  apply Hoare_to_HoareT_indexed
  assumption
  intro x hx
  simp [Terminate]
  apply Hoare_impl_forall at hh
  specialize ht x (denote (cloop c) x) (by tauto) (by tauto)
  specialize ht _ (by rfl); tauto

theorem HoareT_lifted_loop {c: Ckt (A ×ᵥ B) B 1}
  {P: SPred (OVType 1 A)} {Q: SPred (OVType 1 B)}
  (hh: Hoare P (cloop2 c) Q)
  (ht: ∀ x1 x2, (∀ i, P x1 i) -> (∀ i, Q x2 i) ->
    HoareT (fun x => x = sprod2 (x1, ↑↑z⁻¹ x2)) c (fun _ => True)):
    HoareT (fun x => ∀ i, P x i) (cloop2 c) (fun y => ∀ j, Q y j) := by
  apply Hoare_to_HoareT_indexed
  assumption
  intro x hx
  simp [Terminate]
  apply Hoare_impl_forall at hh
  specialize ht x (denote (cloop2 c) x) (by tauto) (by tauto)
  specialize ht _ (by rfl); tauto

theorem HoareT_lifting {c: Ckt A B 0}
  {P: ℕ -> SOVType 0 A -> Prop} {Q: ℕ -> SOVType 0 B -> Prop}
  (h: ∀ j, HoareT (P j) c (Q j)):
    HoareT (fun x => ∀ j, P j (x j)) (c↑ c) (fun y => ∀ j, Q j (y j)) := by
  intro x hx
  simp [Terminate]
  rw [<- forall_and_iff]
  intro j; simp [denote]
  apply h; tauto

theorem HoareT_pushLifting {c: Ckt A B 0}
  {P: ℕ -> SOVType 0 A -> Prop} {Q: ℕ -> SOVType 0 B -> Prop}
  (h: ∀ j, HoareT (P j) c (Q j)):
    HoareT (fun x => ∀ j, P j (x j)) (pushLifting c) (fun y => ∀ j, Q j (y j)) := by
  rw [HoareT_Sequiv_cong]
  apply HoareT_lifting <;> tauto
  symm; apply pushLifting_Sequiv

-- Here's where HoareT relies on HoareI2
theorem HoareT_bracket {c: Ckt A B 1}
  {P: SOVType 0 A -> Prop} {Q: SOVType 1 B -> Prop}
  (b: stream ℕ)
  (ht: ∀ y, P y -> HoareT (fun x => x = ↑↑δ0 y) c Q)
  (hi: ∀ y, P y -> HoareI2 (fun x => x = ↑↑δ0 y) c (fun _ => True) b)
  (hb: ∀ z, Q z -> ZeroAfterVec z b):
    HoareT P (cbracket c) (fun y => ∃ z, Q z ∧ ∀ i, y i = I (z i) (b i)) := by
  intro x hx
  specialize hi x hx; specialize ht x hx
  specialize ht (↑↑δ0 x) (by tauto)
  specialize hi (↑↑δ0 x) (by tauto)
  specialize hb (denote c (↑↑δ0 x)) (by tauto)
  constructor
  · simp [Terminate, ht]
    simp at hi
    use b
  · simp; use (denote c (↑↑δ0 x))
    simp [ht]; simp at hi
    intro i; simp [denote]
    rw [streamElim_zeroAfter (pf:= hb i)]
    rw [integral_sumVals]
    simp; apply hb; omega

lemma HoareT_I {x0: SOVType ns A}:
    HoareT (fun x => x = x0) cI (fun y => y = I x0) := by
  intro x hx; subst x0
  simp; rcases ns <;> rfl

lemma HoareT_D {x0: SOVType ns A}:
    HoareT (fun x => x = x0) cD (fun y => y = D x0) := by
  intro x hx; subst x0; simp

lemma HoareT_Δ {x0: SOVType ns A} {y0: SOVType ns B}
  (h: HoareT (fun x => x = x0) c (fun y => y = y0)):
    HoareT (fun x => x = D x0) (cΔ c) (fun y => y = D y0) := by
  apply HoareT_seq; apply HoareT_seq
  apply HoareT_I
  have : I (D x0) = x0 := by
    rcases ns <;> simp
  rw [this]; apply h
  apply HoareT_D

end HoareT

-- HoareI1 theorems (for IntFP1)
section HoareI1
variable {A B C: VType} {ns: Bool}  {b1: ℕ}
variable {c: Ckt A B ns} {P: SOVType ns A -> Prop} {Q: SOVType ns B -> Prop}

theorem HoareI1_conseq_pre {P': SOVType ns A -> Prop}
  (h: HoareI1 P' c Q b1)
  (hp: ∀ x, P x -> P' x):
    HoareI1 P c Q b1 := by
  intro x hx
  apply h
  apply hp
  assumption

theorem HoareI1_conseq_post {Q': SOVType ns B -> Prop}
  (h: HoareI1 P c Q b1)
  (hq: ∀ x, Q x -> Q' x):
    HoareI1 P c Q' b1 := by
  intro x hx
  rcases h x hx with ⟨ht, hQ⟩
  constructor
  · assumption
  · apply hq; assumption

theorem HoareI1_Preserve1 {c1 c2: Ckt A B ns} {x0: SOVType ns A}
  (h: c1 ↝₁ c2) {Q'} (ht: HoareT (fun x => x = x0) c1 Q')
  (h1: HoareI1 (fun x => x = x0) c1 Q b1):
    HoareI1 (fun x => x = D x0) c2 (fun _ => True) (b1 + 1) := by
  unfold HoareI1 at h1 ⊢
  intro x hx
  specialize h1 _ (by rfl)
  specialize ht _ (by rfl)
  specialize h x0 b1 ht.1 h1.1
  rw [hx]; tauto

theorem HoareI1_mono {b1': ℕ}
  (h: HoareI1 P c Q b1) (hb: b1 <= b1'):
    HoareI1 P c Q b1' := by
  intro x hx
  rcases h x hx with ⟨ht, hQ⟩
  constructor
  · apply IntFP1_mono; assumption; assumption
  · assumption

theorem HoareI1_True:
    HoareI1 P c (fun _ => True) b1 <-> (∀ x, P x -> IntFP1 c x b1) := by
  simp [HoareI1]

theorem HoareT_to_HoareI1
  (ht: HoareT P c Q)
  (hi: HoareI1 P c (fun _ => True) b1):
    HoareI1 P c Q b1 := by
  rw [HoareI1_True] at hi
  intro x hx
  constructor
  · apply hi; assumption
  · specialize ht x hx
    tauto

theorem Hoare_to_HoareI1 {P: SPred (OVType ns A)} {Q: SPred (OVType ns B)}
  (hh: Hoare P c Q)
  (hi: HoareI1 (fun x => ∀ i, P x i) c (fun _ => True) b1):
    HoareI1 (fun x => ∀ i, P x i) c (fun y => ∀ j, Q y j) b1 := by
  rw [HoareI1_True] at hi
  intro x hx
  constructor
  · apply hi; assumption
  · intro j
    specialize hh x (j + 1) (by intro k hk; apply hx)
    apply hh; omega

theorem HoareI1_seq {c1: Ckt A B ns} {c2: Ckt B C ns}
  {Q1: SOVType ns B -> Prop} {Q2: SOVType ns C -> Prop}
  (h1: HoareI1 P c1 Q1 b1) (h2: HoareI1 Q1 c2 Q2 b1):
    HoareI1 P (c1 >>c c2) Q2 b1 := by
  intro x hx
  rcases h1 x hx with ⟨t1, q1⟩
  rcases h2 (denote c1 x) q1 with ⟨t2, q2⟩
  constructor
  · simp [IntFP1]; exact ⟨t1, t2⟩
  · simp [denote]; assumption

theorem HoareI1_par {c1: Ckt A B ns} {c2: Ckt A C ns}
  {Q1: SOVType ns B -> Prop} {Q2: SOVType ns C -> Prop}
  (h1: HoareI1 P c1 Q1 b1) (h2: HoareI1 P c2 Q2 b1):
    HoareI1 P (c1 &&c c2) (fun y => Q1 (liftO ns Prod.fst y) ∧ Q2 (liftO ns Prod.snd y)) b1 := by
  intro x hx
  rcases h1 x hx with ⟨t1, q1⟩
  rcases h2 x hx with ⟨t2, q2⟩
  constructor
  · simp [IntFP1]; exact ⟨t1, t2⟩
  · simp [denote, liftO, sprodO]; constructor <;> rcases ns <;> assumption

theorem HoareI1_conj {Q1: SOVType ns B -> Prop} {Q2: SOVType ns B -> Prop}
  (h1: HoareI1 P c Q1 b1) (h2: HoareI1 P c Q2 b1):
    HoareI1 P c (fun y => Q1 y ∧ Q2 y) b1 := by
  intro x hx
  rcases h1 x hx with ⟨t1, q1⟩
  rcases h2 x hx with ⟨t2, q2⟩
  constructor
  · assumption
  · constructor <;> assumption

theorem HoareI1_loop {c: Ckt (A ×ᵥ B) B ns}
  (hh: HoareT P (cloop c) Q)
  (hi: ∀ x1 x2, P x1 -> Q x2 ->
    HoareI1 (fun x => x = sprodO ns (x1, z⁻¹ x2)) c (fun _ => True) b1):
    HoareI1 P (cloop c) Q b1 := by
  intro x hx
  rcases hh x hx with ⟨ht, hQ⟩
  constructor
  · specialize hi x (denote (cloop c) x) hx hQ
    rcases hi (sprodO ns (x, z⁻¹ (denote (cloop c) x))) rfl with ⟨hb, _⟩
    simp [IntFP1] at *
    exact hb
  · exact hQ

-- Using `Hoare` instead of `HoareT`
theorem HoareI1_loop' {c: Ckt (A ×ᵥ B) B ns}
  {P: SPred (OVType ns A)} {Q: SPred (OVType ns B)}
  (hh: Hoare P (cloop c) Q)
  (hi: ∀ x1 x2, (∀ i, P x1 i) -> (∀ i, Q x2 i) ->
    HoareI1 (fun x => x = sprodO ns (x1, z⁻¹ x2)) c (fun _ => True) b1):
    HoareI1 (fun x => ∀ i, P x i) (cloop c) (fun y => ∀ j, Q y j) b1 := by
  apply Hoare_to_HoareI1
  assumption
  intro x hx
  apply Hoare_impl_forall at hh
  specialize hi x (denote (cloop c) x) (by tauto) (by tauto)
  specialize hi _ (by rfl)
  simp [IntFP1] at *; tauto

theorem HoareI1_lifted_loop {c: Ckt (A ×ᵥ B) B 1}
  {P: SOVType 1 A -> Prop} {Q: SOVType 1 B -> Prop}
  (hh: HoareT P (cloop2 c) Q)
  (hi: ∀ x1 x2, P x1 -> Q x2 ->
    HoareI1 (fun x => x = sprod2 (x1, ↑↑z⁻¹ x2)) c (fun _ => True) b1):
    HoareI1 P (cloop2 c) Q b1 := by
  intro x hx
  rcases hh x hx with ⟨ht, hQ⟩
  constructor
  · specialize hi x (denote (cloop2 c) x) hx hQ
    rcases hi (sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c) x))) rfl with ⟨hb, _⟩
    simp [IntFP1] at *
    exact hb
  · exact hQ

theorem HoareI1_lifted_loop' {c: Ckt (A ×ᵥ B) B 1}
  {P: SPred (OVType 1 A)} {Q: SPred (OVType 1 B)}
  (hh: Hoare P (cloop2 c) Q)
  (hi: ∀ x1 x2, (∀ i, P x1 i) -> (∀ i, Q x2 i) ->
    HoareI1 (fun x => x = sprod2 (x1, ↑↑z⁻¹ x2)) c (fun _ => True) b1):
    HoareI1 (fun x => ∀ i, P x i) (cloop2 c) (fun y => ∀ j, Q y j) b1 := by
  apply Hoare_to_HoareI1
  assumption
  intro x hx
  apply Hoare_impl_forall at hh
  specialize hi x (denote (cloop2 c) x) (by tauto) (by tauto)
  specialize hi _ (by rfl)
  simp [IntFP1] at *; tauto

theorem HoareI1_lifting {c: Ckt A B 0}
  {P: SOVType 1 A -> Prop} {Q: SOVType 1 B -> Prop}
  (h: HoareT P (c↑ c) Q)
  (hp: ∀ x, P x -> FixedAfter1 x b1):
    HoareI1 P (c↑ c) Q b1 := by
  intro x hx
  rcases h x hx with ⟨ht, hQ⟩
  simp [IntFP1, hQ]
  rw [lifted_Ckt_ExtFP1]
  tauto
  simp [lifted_Ckt, denote]

lemma HoareI1_I {s: SOVType ns A}
  (h: ZeroAfter s (b1+1)):
    HoareI1 (fun x => x = s) cI (fun y => y = I s) (b1+1) := by
  simp [HoareI1]
  constructor; swap; rcases ns <;> simp
  apply I_IntFP1
  rcases ns <;>
  rw [<- ZeroAfter_succ_I_FixedAfter1] <;> tauto

lemma HoareI1_D {s: SOVType ns A}
  (h: FixedAfter1 s b1):
    HoareI1 (fun x => x = s) cD (fun y => y = D s) (b1+1) := by
  simp [HoareI1]
  apply D_IntFP1
  rcases ns <;>
  rw [ZeroAfter_succ_D_FixedAfter1] <;> tauto

end HoareI1

-- HoareI2 theorems (for IntFP2Vec)
section HoareI2
variable {A B C: VType} {b2: stream ℕ}
variable {c: Ckt A B 1} {P: SOVType 1 A -> Prop} {Q: SOVType 1 B -> Prop}

theorem HoareI2_conseq_pre {P': SOVType 1 A -> Prop}
  (h: HoareI2 P' c Q b2)
  (hp: ∀ x, P x -> P' x):
    HoareI2 P c Q b2 := by
  intro x hx
  apply h
  apply hp
  assumption

theorem HoareI2_conseq_post {Q': SOVType 1 B -> Prop}
  (h: HoareI2 P c Q b2)
  (hq: ∀ x, Q x -> Q' x):
    HoareI2 P c Q' b2 := by
  intro x hx
  rcases h x hx with ⟨ht, hQ⟩
  constructor
  · assumption
  · apply hq; assumption

theorem HoareI2_bound_mono {b1 b2: stream ℕ}
  (h: b1 ≤ b2) (hi: HoareI2 P c Q b1):
    HoareI2 P c Q b2 := by
  intro x hx
  rcases hi x hx with ⟨ht, hQ⟩
  constructor
  · apply IntFP2Vec_mono <;> tauto
  · apply hQ

theorem HoareI2_Preserve2 {c1 c2: Ckt A B 1} {x0: SOVType 1 A}
  (h: c1 ↝₂ c2) {Q'} (ht: HoareT (fun x => x = x0) c1 Q')
  (h1: HoareI2 (fun x => x = x0) c1 Q b2):
    HoareI2 (fun x => x = D x0) c2 (fun _ => True) (fun i => max (b2 i) (z⁻¹ b2 i)) := by
  unfold HoareI2 at h1 ⊢
  intro x hx
  specialize h1 _ (by rfl)
  specialize ht _ (by rfl)
  specialize h x0 b2 ht.1 h1.1
  rw [hx]; tauto

theorem HoareI2_True:
    HoareI2 P c (fun _ => True) b2 <-> (∀ x, P x -> IntFP2Vec c x b2) := by
  simp [HoareI2]

theorem HoareT_to_HoareI2
  (ht: HoareT P c Q)
  (hi: HoareI2 P c (fun _ => True) b2):
    HoareI2 P c Q b2 := by
  rw [HoareI2_True] at hi
  intro x hx
  constructor
  · apply hi; assumption
  · specialize ht x hx
    tauto

theorem Hoare_to_HoareI2 {P: SPred (OVType 1 A)} {Q: SPred (OVType 1 B)}
  (hh: Hoare P c Q)
  (hi: HoareI2 (fun x => ∀ i, P x i) c (fun _ => True) b2):
    HoareI2 (fun x => ∀ i, P x i) c (fun y => ∀ j, Q y j) b2 := by
  rw [HoareI2_True] at hi
  intro x hx
  constructor
  · apply hi; assumption
  · intro j
    specialize hh x (j + 1) (by intro k hk; apply hx)
    apply hh; omega

theorem HoareI2_seq {c1: Ckt A B 1} {c2: Ckt B C 1}
  {Q1: SOVType 1 B -> Prop} {Q2: SOVType 1 C -> Prop}
  (h1: HoareI2 P c1 Q1 b2) (h2: HoareI2 Q1 c2 Q2 b2):
    HoareI2 P (c1 >>c c2) Q2 b2 := by
  intro x hx
  rcases h1 x hx with ⟨t1, q1⟩
  rcases h2 (denote c1 x) q1 with ⟨t2, q2⟩
  constructor
  · simp [IntFP2Vec, IntFP2]
    intro i; exact ⟨t1 i, t2 i⟩
  · simp [denote]; assumption

theorem HoareI2_par {c1: Ckt A B 1} {c2: Ckt A C 1}
  {Q1: SOVType 1 B -> Prop} {Q2: SOVType 1 C -> Prop}
  (h1: HoareI2 P c1 Q1 b2) (h2: HoareI2 P c2 Q2 b2):
    HoareI2 P (c1 &&c c2) (fun y => Q1 (↑↑↑↑Prod.fst y) ∧ Q2 (↑↑↑↑Prod.snd y)) b2 := by
  intro x hx
  rcases h1 x hx with ⟨t1, q1⟩
  rcases h2 x hx with ⟨t2, q2⟩
  constructor
  · simp [IntFP2Vec, IntFP2]
    intro i; exact ⟨t1 i, t2 i⟩
  · simp [denote, liftO, sprodO]; constructor <;> assumption

theorem HoareI2_conj {Q1: SOVType 1 B -> Prop} {Q2: SOVType 1 B -> Prop}
  (h1: HoareI2 P c Q1 b2) (h2: HoareI2 P c Q2 b2):
    HoareI2 P c (fun y => Q1 y ∧ Q2 y) b2 := by
  intro x hx
  rcases h1 x hx with ⟨t1, q1⟩
  rcases h2 x hx with ⟨t2, q2⟩
  constructor
  · assumption
  · constructor <;> assumption

theorem HoareI2_loop {c: Ckt (A ×ᵥ B) B 1}
  {P: SOVType 1 A -> Prop} {Q: SOVType 1 B -> Prop}
  (hh: HoareT P (cloop c) Q)
  (hi: ∀ x1 x2, P x1 -> Q x2 ->
    HoareI2 (fun x => x = sprod2 (x1, z⁻¹ x2)) c (fun _ => True) b2):
    HoareI2 P (cloop c) Q b2 := by
  intro x hx
  rcases hh x hx with ⟨ht, hQ⟩
  constructor
  · specialize hi x (denote (cloop c) x) hx hQ
    rcases hi (sprod2 (x, z⁻¹ (denote (cloop c) x))) rfl with ⟨hb, _⟩
    simp [IntFP2Vec] at *
    intro i; specialize hb i
    unfold IntFP2
    exact hb
  · exact hQ

theorem HoareI2_loop' {c: Ckt (A ×ᵥ B) B 1}
  {P: SPred (OVType 1 A)} {Q: SPred (OVType 1 B)}
  (hh: Hoare P (cloop c) Q)
  (hi: ∀ x1 x2, (∀ i, P x1 i) -> (∀ i, Q x2 i) ->
    HoareI2 (fun x => x = sprod2 (x1, z⁻¹ x2)) c (fun _ => True) b2):
    HoareI2 (fun x => ∀ i, P x i) (cloop c) (fun y => ∀ j, Q y j) b2 := by
  apply Hoare_to_HoareI2
  assumption
  intro x hx
  apply Hoare_impl_forall at hh
  specialize hi x (denote (cloop c) x) (by tauto) (by tauto)
  specialize hi _ (by rfl)
  simp [IntFP2Vec] at hi ⊢
  simp [IntFP2]; tauto

theorem HoareI2_lifted_loop {c: Ckt (A ×ᵥ B) B 1}
  {P: SOVType 1 A -> Prop} {Q: SOVType 1 B -> Prop}
  (hh: HoareT P (cloop2 c) Q)
  (hi: ∀ x1 x2, P x1 -> Q x2 ->
    HoareI2 (fun x => x = sprod2 (x1, ↑↑z⁻¹ x2)) c (fun _ => True) b2):
    HoareI2 P (cloop2 c) Q b2 := by
  intro x hx
  rcases hh x hx with ⟨ht, hQ⟩
  constructor
  · specialize hi x (denote (cloop2 c) x) hx hQ
    rcases hi (sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c) x))) rfl with ⟨hb, _⟩
    simp [IntFP2Vec] at *
    intro i; specialize hb i
    unfold IntFP2
    exact hb
  · exact hQ

theorem HoareI2_lifted_loop' {c: Ckt (A ×ᵥ B) B 1}
  {P: SPred (OVType 1 A)} {Q: SPred (OVType 1 B)}
  (hh: Hoare P (cloop2 c) Q)
  (hi: ∀ x1 x2, (∀ i, P x1 i) -> (∀ i, Q x2 i) ->
    HoareI2 (fun x => x = sprod2 (x1, ↑↑z⁻¹ x2)) c (fun _ => True) b2):
    HoareI2 (fun x => ∀ i, P x i) (cloop2 c) (fun y => ∀ j, Q y j) b2 := by
  apply Hoare_to_HoareI2
  assumption
  intro x hx
  apply Hoare_impl_forall at hh
  specialize hi x (denote (cloop2 c) x) (by tauto) (by tauto)
  specialize hi _ (by rfl)
  simp [IntFP2Vec] at hi ⊢
  simp [IntFP2]; tauto

theorem HoareI2_lifting {c: Ckt A B 0}
  {P: ℕ -> SOVType 0 A -> Prop} {Q: ℕ -> SOVType 0 B -> Prop}
  (h: ∀ i, HoareI1 (P i) c (Q i) (b2 i)):
    HoareI2 (fun x => ∀ i, P i (x i)) (c↑ c) (fun y => ∀ j, Q j (y j)) b2 := by
  intro x hx; simp
  constructor; swap
  · intro j
    specialize h j (x j) (by apply hx)
    simp [denote, h]
  · intro j
    specialize h j (x j) (by apply hx)
    simp [IntFP2, h]

theorem HoareI2_pushLifting {c: Ckt A B 0}
  {P: ℕ -> SOVType 0 A -> Prop} {Q: ℕ -> SOVType 0 B -> Prop}
  (h: ∀ i, HoareI1 (P i) c (Q i) (b2 i)):
    HoareI2 (fun x => ∀ i, P i (x i)) (pushLifting c) (fun y => ∀ j, Q j (y j)) b2 := by
  intro x hx; simp
  constructor
  · intro j; apply pushLifting_IntFP2
    specialize h j (x j) (by apply hx)
    tauto
  · intro j
    specialize h j (x j) (by apply hx)
    rw [<- (pushLifting_Sequiv c).1]; tauto

end HoareI2

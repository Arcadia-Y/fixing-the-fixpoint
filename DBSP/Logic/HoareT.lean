-- Hoare logic for total correctness
import DBSP.Logic.Hoare
open CktBasic

section HoareT
variable {A B C: VType} {ns: Bool}

-- Non-step-indexed Hoare triple for total correctness
def HoareT (P: SOVType ns A -> Prop)
    (c: Ckt A B ns) (Q: SOVType ns B -> Prop) :=
  ∀ x, P x -> Terminate c x ∧ Q (denote c x)

@[simp]
def IntFP (c: Ckt A B ns) (x: SOVType ns A) (b: Optstream ns ℕ): Prop :=
  match ns with
  | false => IntFP1 c x b
  | true => IntFP2Vec c x b

variable  {c: Ckt A B ns} {P: SOVType ns A -> Prop} {Q: SOVType ns B -> Prop}

-- Hoare triple to reason about IntFP
structure HoareI (P: SOVType ns A -> Prop)
    (c: Ckt A B ns) (Q: SOVType ns B -> Prop) (b: Optstream ns ℕ) where
  ht: HoareT P c Q
  hb: ∀ x, P x -> IntFP c x b

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

theorem Hoare_to_HoareT
  (hh: Hoare (fun x _ => P x) c (fun y _ => Q y))
  (ht: ∀ x, P x -> Terminate c x):
    HoareT P c Q := by
  intro x hx
  constructor
  · apply ht; assumption
  · specialize hh x 1 (by intro k hk; exact hx)
    exact hh 0 (by omega)

theorem Hoare_to_HoareT_indexed {P: SPred (OVType ns A)} {Q: SPred (OVType ns B)}
  (hh: Hoare P c Q)
  (ht: ∀ x, (∀ i, P x i) -> Terminate c x):
    HoareT (fun x => ∀ i, P x i) c (fun y => ∀ j, Q y j) := by
  intro x hx
  constructor
  · apply ht; assumption
  · intro j
    specialize hh x (j + 1) (by intro k hk; apply hx)
    apply hh; omega

theorem HoareT_True_iff:
    HoareT P c (fun _ => True) <-> (∀ x, P x -> Terminate c x) := by
  simp [HoareT]

theorem HoareT_Sequiv_cong {c1 c2: Ckt A B ns}
  (h: c1 ≃ c2):
    HoareT P c1 Q <-> HoareT P c2 Q := by
  unfold HoareT
  apply forall_congr'; intro x
  apply imp_congr_right; intro hP
  unfold Sequiv at h; rcases h with ⟨hd, ht⟩
  rw [hd]
  have : Terminate c1 x ↔ Terminate c2 x := by
    rw [Terminate_iff, Terminate_iff]
    rw [ht]
  rw [this]

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

theorem HoareT_lifting {c: Ckt A B 0}

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

-- Here's where HoareT relies on HoareI
theorem HoareT_bracket {c: Ckt A B 1}
  {P: SOVType 0 A -> Prop} {Q: SOVType 1 B -> Prop}
  (b: stream ℕ)
  (hi: ∀ y, P y -> HoareI (fun x => x = ↑↑δ0 y) c Q b)
  (hb: ∀ z, Q z -> ZeroAfterVec z b):
    HoareT P (cbracket c) (fun y => ∃ z, Q z ∧ ∀ i, y i = I (z i) (b i)) := by
  intro x hx
  specialize hi x hx
  rcases hi with ⟨ht, hi⟩
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

end HoareT

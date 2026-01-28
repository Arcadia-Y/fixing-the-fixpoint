-- Hoare logic for partial correctness
import DBSP.Circuits.Circuits_v6
import DBSP.StreamTheory.Linear
import DBSP.Logic.SProp
import DBSP.Practical.Sequiv
open CktBasic

section Transpose
variable {A: Type}

@[simp]
def transpose (s: stream (stream A)): stream (stream A) :=
  fun n m => s m n
notation "TP" => transpose

@[simp]
lemma TP_apply (s: stream (stream A)) (n m: ℕ):
  TP s n m = s m n := by rfl

variable [Zero A]

theorem TP_delay (s: stream (stream A)):
    TP (↑↑z⁻¹ s) = z⁻¹ (TP s) := by
  funext n m; simp [transpose, delay]
  split_ifs <;> simp

@[simp]
def TP_SPred (P: SPred (stream A)) :=
  fun s => P (TP s)

end Transpose

section Hoare
variable {A B C: VType} {ns: Bool} {c: Ckt A B ns}
  {P: SPred (OVType ns A)} {Q: SPred (OVType ns B)}

-- Step-indexed Hoare triple for partial correctness
-- By unfolding `Hoare` we can directly reason in the weakest-precondition style.
-- We recommend using weakest-precondition style in a "basic block" (circuits without loops and brackets)
-- and strongest-postcondition style in the higher level.
def Hoare (P: SPred (OVType ns A))
    (c: Ckt A B ns) (Q: SPred (OVType ns B)):=
  ∀ x n,
    TrueUntil n (P x) ->
    TrueUntil n (Q (denote c x))

lemma Hoare_impl_forall
  (h: Hoare P c Q):
    ∀ x, (∀ i, P x i) -> (∀ j, Q (denote c x) j) := by
  tauto

theorem Hoare_conseq_post_strong
  (Q': SPred (OVType ns B))
  (h: Hoare P c Q')
  (hy: ∀ y n, TrueUntil n (Q' y) -> TrueUntil n (Q y)):
    Hoare P c Q := by
  tauto

theorem Hoare_conseq_post
  (Q': SPred (OVType ns B))
  (h: Hoare P c Q')
  (hy: ∀ y i, Q' y i -> Q y i):
    Hoare P c Q := by
  tauto

theorem Hoare_conseq_pre_strong
  (P': SPred (OVType ns A))
  (h: Hoare P' c Q)
  (hx: ∀ x n, TrueUntil n (P x) -> TrueUntil n (P' x)):
    Hoare P c Q := by
  intro x n hp
  apply h
  apply hx; assumption

theorem Hoare_conseq_pre
  (P': SPred (OVType ns A))
  (h: Hoare P' c Q)
  (hx: ∀ x i, P x i -> P' x i):
    Hoare P c Q := by
  apply Hoare_conseq_pre_strong P' h
  intro x n hp m hm
  apply hx
  apply hp; assumption

theorem Hoare_Sequiv_cong {c1 c2: Ckt A B ns}
  (h: c1 ≃ c2):
    Hoare P c1 Q <-> Hoare P c2 Q:= by
  unfold Sequiv at h; rcases h with ⟨h1, h2⟩
  unfold Hoare; simp_rw [h1]

theorem Hoare_seq {c1: Ckt A B ns} {c2: Ckt B C ns}
  {Q1: SPred (OVType ns B)} {Q2: SPred (OVType ns C)}
  (h1: Hoare P c1 Q1) (h2: Hoare Q1 c2 Q2):
    Hoare P (c1 >>c c2) Q2 := by
  tauto

theorem Hoare_seq_ncausal {c1: Ckt A B ns} {c2: Ckt B C ns}
  {Q1: (SOVType ns B) -> Prop} {Q2: SPred (OVType ns C)}
  (h1: Hoare P c1 (fun y _ => Q1 y)) (h2: Hoare (fun x _ => Q1 x) c2 Q2):
    Hoare P (c1 >>c c2) Q2 := by
  apply Hoare_seq; apply h1
  intro y hy
  apply h2

theorem Hoare_par {c1: Ckt A B ns} {c2: Ckt A C ns}
  {Q1: SPred (OVType ns B)} {Q2: SPred (OVType ns C)}
  (h1: Hoare P c1 Q1) (h2: Hoare P c2 Q2):
    Hoare P (c1 &&c c2) (fun y =>
      Q1 (liftO ns Prod.fst y) ∧ₛ Q2 (liftO ns Prod.snd y))
    := by
  intros x n hx
  specialize h1 x n hx
  specialize h2 x n hx
  simp [TrueUntil] at *
  intro m hm
  simp [denote, liftO, sprodO]
  constructor
  · rcases ns <;> simp at * <;> apply h1 <;> assumption
  · rcases ns <;> simp at * <;> apply h2 <;> assumption

theorem Hoare_par_ncausal {c1: Ckt A B ns} {c2: Ckt A C ns}
  {Q1: (SOVType ns B) -> Prop} {Q2: (SOVType ns C) -> Prop}
  (h1: Hoare P c1 (fun y _ => Q1 y)) (h2: Hoare P c2 (fun y _ => Q2 y)):
    Hoare P (c1 &&c c2) (fun y _ => Q1 (liftO ns Prod.fst y) ∧ Q2 (liftO ns Prod.snd y)) := by
  apply Hoare_par h1 h2

-- when precondition is row-indexed
theorem Hoare_lifting_row {c: Ckt A B 0}
  {P: SPred (OVType 1 A)} {Q: SPred (OVType 0 B)}
  (h: ∀ y k, TrueUntil k (P y) -> Hoare (fun x _ => x = y k) c Q):
    Hoare P (c↑ c) (fun y i => ∀ n, Q (y i) n) := by
  intro x n hx
  simp [denote]
  intro m hm
  specialize h x m (by apply TrueUntil_mono hx; omega)
  apply Hoare_impl_forall at h
  simp at h
  apply h

-- when precondition is column-indexed
theorem Hoare_lifting_column {c: Ckt A B 0}
  {P: SPred (OVType 1 A)} {Q: SPred (OVType 0 B)}
  (h: ∀ y k, Hoare (fun x i => P y i ∧ x i = y k i) c Q):
    Hoare P (c↑ c) (fun y i => ∀ n, Q (y i) n) := by
  sorry

theorem Hoare_loop {c: Ckt (A ×ᵥ B) B ns} (I: SPred (OVType ns B))
  (h: Hoare
    (fun x =>
      P (liftO ns Prod.fst x) ∧ₛ
      (later I) (liftO ns Prod.snd x))
    c I):
    Hoare P (cloop c) I := by
  intro x n; revert x
  induction' n with n ih <;> intro x
  · specialize h (sprodO ns (x, z⁻¹ (denote (cloop c) x))) 0
    simp [TrueUntil] at h ⊢
    rw [loop_unfold]; tauto
  · intro hp
    specialize h (sprodO ns (x, z⁻¹ (denote (cloop c) x))) (n+1)
    rw [<- loop_unfold] at h; apply h
    intro m hm; simp; constructor
    · apply hp; omega
    simp [later]; intro _
    apply ih; apply TrueUntil_mono
    tauto; omega; omega

theorem Hoare_lifted_loop {c: Ckt (A ×ᵥ B) B 1}
  {P: SPred (stream (VType_interp A))}
  (I: SPred (stream (VType_interp B)))
  (h: Hoare (fun x =>
    P (↑↑↑↑Prod.fst x) ∧ₛ
    (later I) (TP (↑↑↑↑Prod.snd x)))
    c (TP_SPred I)):
    Hoare P (cloop2 c) (TP_SPred I) := by
  intro x n; revert x
  induction' n with n ih <;> intro x
  · specialize h (sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c) x))) 0
    simp [TrueUntil] at h ⊢
    rw [lifted_loop_unfold]; tauto
  · intro hp
    specialize h (sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c) x))) (n+1)
    rw [<- lifted_loop_unfold] at h; apply h
    intro m hm; constructor
    · apply hp; omega
    rcases m with _ | m
    · funext k; simp
    · simp; rw [TP_delay, <- later_delay]
      apply ih
      apply TrueUntil_mono
      tauto; omega; omega

theorem Hoare_bracket {c: Ckt A B 1}
  {P: SPred (VType_interp A)}
  {Q: SPred (stream (VType_interp B))}
  (h: ∀ y, Hoare (fun x i => P y i ∧ x i = δ0 (y i)) c Q):
    Hoare P (cbracket c) (fun y i => ∃ z, Q z i ∧ y i = ∫0 (z i)) := by
  intro x n ht; simp
  intro m hm
  use (denote c (↑↑δ0 x))
  simp [denote]
  apply h; intro k hk
  simp
  tauto; omega

theorem Hoare_conj
  {Q1: SPred (OVType ns B)} {Q2: SPred (OVType ns B)}
  (h1: Hoare P c Q1) (h2: Hoare P c Q2):
    Hoare P c (fun y => Q1 y ∧ₛ Q2 y) := by
  intro _ _ _ _ _; simp; tauto

theorem Hoare_conj_ncausal
  {Q1: (SOVType ns B) -> Prop} {Q2: (SOVType ns B) -> Prop}
  (h1: Hoare P c (fun y _ => Q1 y)) (h2: Hoare P c (fun y _ => Q2 y)):
    Hoare P c (fun y _ => Q1 y ∧ Q2 y) := by
  apply Hoare_conseq_post
  apply Hoare_conj; apply h1; apply h2
  simp

end Hoare

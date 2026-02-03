import DBSP.Circuits.Circuits
import DBSP.Practical.Sequiv
open CktBasic

-- Push the lifting operator inside to simplify a circuit
-- spec is denote (pushLifting c) = denote (c↑ c)
def pushLifting {a b} (c: Ckt a b 0): Ckt a b 1 :=
  match c with
  | Ckt.node1 f => Ckt.node1 f
  | Ckt.node2 f => Ckt.node2 f
  | Ckt.const x => Ckt.const x
  | Ckt.id => Ckt.id
  | Ckt.fst => Ckt.fst
  | Ckt.snd => Ckt.snd
  | Ckt.add => Ckt.add
  | Ckt.sub => Ckt.sub
  | Ckt.seq c1 c2 => (pushLifting c1) >>c (pushLifting c2)
  | Ckt.par c1 c2 => (pushLifting c1) &&c (pushLifting c2)
  | Ckt.delay => Ckt.lifted_delay
  | Ckt.loop c =>  Ckt.lifted_loop (pushLifting c)
  | Ckt.bracket c => c↑ (cbracket c)

theorem pushLifting_Sequiv {a b} (c: Ckt a b 0):
    (c↑ c) ≃ pushLifting c := by
  rw [Sequiv_iff_toSem_eq]
  revert c; apply Ckt_generalize_ns_0
  intro ns c hns
  induction c <;> (try subst hns) <;> dsimp
  case bracket => simp [pushLifting] -- trivial case c↑(bracket c) = c↑(bracket c)
  case node1 | node2 | const | id | fst | snd | add | sub  =>
    simp only [pushLifting]
    apply Quotient.sound
    change Sequiv _ _
    unfold Sequiv
    simp [denote, Terminate, lifting, liftO]
    try rfl
  case delay =>
    simp only [pushLifting]
    rw [<- SemCkt_lifting_lift, SemCkt_lifting_delay]
  case seq c1 c2 ih1 ih2 =>
    simp only [pushLifting]
    rw [<- SemCkt_lifting_lift, <- SemCkt_seq_lift]
    rw [SemCkt_lifting_seq]
    rw [SemCkt_lifting_lift, SemCkt_lifting_lift]
    rw [ih1 rfl, ih2 rfl]
    rw [SemCkt_seq_lift]
  case par c1 c2 ih1 ih2 =>
    simp only [pushLifting]
    rw [<- SemCkt_lifting_lift, <- SemCkt_par_lift]
    rw [SemCkt_lifting_par]
    rw [SemCkt_lifting_lift, SemCkt_lifting_lift]
    rw [ih1 rfl, ih2 rfl]
    rw [SemCkt_par_lift]
  case loop c ih =>
    simp only [pushLifting]
    rw [<- SemCkt_lifting_lift, <- SemCkt_loop_lift]
    rw [SemCkt_lifting_loop]
    rw [SemCkt_lifting_lift]
    rw [ih rfl]
    rw [SemCkt_lifted_loop_lift]

theorem pushLifting_IntFP2 {a b} (c: Ckt a b 0)
  {x m n} (h: IntFP1 c (x m) n):
    IntFP2 (pushLifting c) x m n := by
  revert c x m n
  apply Ckt_generalize_ns_0
  intro ns c hns
  induction c <;> (try subst hns) <;> simp [pushLifting]
  case node1 | node2 | const | id | fst | snd | add | sub  =>
    intro x m n h
    simp [IntFP2, IntFP1] at h ⊢
    rw [lifted_Ckt_ExtFP1 (hc := by simp)] at h
    rw [LiftedScalar_ExtFP2 (hc := by constructor)]
    exact h
  case seq c1 c2 ih1 ih2 =>
    intro x m n hfp
    simp at ih1 ih2
    simp [IntFP2, IntFP1] at hfp ⊢
    constructor
    · apply ih1
      exact hfp.1
    · apply ih2
      rw [<- (pushLifting_Sequiv c1).1]
      exact hfp.2
  case par c1 c2 ih1 ih2 =>
    intro x m n hfp
    simp at ih1 ih2
    simp [IntFP2, IntFP1] at hfp ⊢
    constructor
    · apply ih1
      exact hfp.1
    · apply ih2
      exact hfp.2
  case delay =>
    simp [IntFP2, IntFP1, ExtFP2, ExtFP1, FixedAfter2, denote]
  case loop c ih =>
    intro x m n hfp
    simp at ih
    simp [IntFP2, IntFP1, sprodO] at hfp ⊢
    apply ih
    have hse: (cloop2 (pushLifting c)) ≃ (c↑ (cloop c)) := by
      apply Sequiv_trans
      apply Sequiv_lifted_loop_congr
      symm; apply pushLifting_Sequiv
      symm; apply Sequiv_lifting_loop
    rw [hse.1]
    have :
        sprod2 (x, ↑↑z⁻¹ (denote (c↑ (cloop c)) x)) m =
        sprod (x m, z⁻¹ (denote (cloop c) (x m))) := by
      funext j; simp [denote]
    rw [this]; exact hfp
  case bracket c _ =>
    intro x m n hfp
    simp [IntFP2, IntFP1] at hfp ⊢
    exact hfp

theorem pushLifting_IntFP2Vec {a b} (c: Ckt a b 0)
  {x b} (h: IntFP2Vec (c↑ c) x b):
    IntFP2Vec (pushLifting c) x b := by
  intro i
  apply pushLifting_IntFP2
  simp [IntFP2Vec, IntFP2] at h
  exact h i

import DBSP.StreamTheory.Stream
import DBSP.StreamTheory.Linear
import DBSP.Circuits.Circuits_v6
import DBSP.Circuits.CktProp
import DBSP.Termination.Spec
import DBSP.Termination.FPProp
import DBSP.Logic.SProp
open CktBasic

section Sequiv
variable {n: ℕ} {A B C: VType} {ns: Bool}

-- semantic equivalence for Ckts
-- termination is preserved row-wise
def Sequiv (c1 c2: Ckt A B ns): Prop :=
   denote c1 = denote c2 ∧ TerminateRow c1 = TerminateRow c2
infix:30 " ≃ " => Sequiv

-- equivalence relation
@[refl]
theorem Sequiv_rfl (c: Ckt A B ns): c ≃ c := by unfold Sequiv; simp

@[symm]
theorem Sequiv_symm {c1 c2: Ckt A B ns}: c1 ≃ c2 → c2 ≃ c1 := by
  unfold Sequiv; rintro ⟨h1, h2⟩; constructor <;> symm <;> assumption

@[trans]
theorem Sequiv_trans {c1 c2 c3: Ckt A B ns}: c1 ≃ c2 → c2 ≃ c3 → c1 ≃ c3 := by
  unfold Sequiv; rintro ⟨h1, h2⟩ ⟨h3, h4⟩; constructor
  · trans <;> assumption
  · trans <;> assumption

instance SetoidSequiv : Setoid (Ckt A B ns) where
  r := Sequiv
  iseqv := ⟨Sequiv_rfl, Sequiv_symm, Sequiv_trans⟩

-- congruence properties
theorem Sequiv_seq_cong {c1 c3: Ckt A B ns} {c2 c4: Ckt B C ns}
  (h1: c1 ≃ c3) (h2: c2 ≃ c4):
    c1 >>c c2 ≃ c3 >>c c4 := by
  unfold Sequiv at *; rcases h1 with ⟨d1, t1⟩; rcases h2 with ⟨d2, t2⟩
  constructor
  · funext x; simp [denote]; rw [d1, d2]
  · funext x; simp [TerminateRow]; rw [t1, d1, t2]

theorem Sequiv_seq_assoc {D: VType} {c1: Ckt A B ns}
  {c2: Ckt B C ns} {c3: Ckt C D ns}:
    c1 >>c c2 >>c c3 ≃ c1 >>c (c2 >>c c3) := by
  unfold Sequiv; constructor <;> funext x i
  · simp [denote]
  · simp [TerminateRow, denote]; tauto

theorem Sequiv_par_cong {c1 c3: Ckt A B ns} {c2 c4: Ckt A C ns}
  (h1: c1 ≃ c3) (h2: c2 ≃ c4):
    c1 &&c c2 ≃ c3 &&c c4 := by
  unfold Sequiv at *; rcases h1 with ⟨d1, t1⟩; rcases h2 with ⟨d2, t2⟩
  constructor
  · funext x; simp [denote, d1, d2]
  · funext x; simp [TerminateRow, t1, t2]

theorem Sequiv_lifting_congr {c1 c2: Ckt A B 0} (h: c1 ≃ c2):
    (c↑ c1) ≃ (c↑ c2) := by
  unfold Sequiv at *; rcases h with ⟨d1, t1⟩
  constructor
  · funext x; funext n; simp [denote, lifting]
    rw [d1]
  · funext x i; simp [TerminateRow]
    apply forall_congr'; intro n
    rw [t1]

theorem Sequiv_loop_congr {c1 c2: Ckt (A ×ᵥ B) B ns} (h: c1 ≃ c2):
    (cloop c1) ≃ (cloop c2) := by
  unfold Sequiv at *; rcases h with ⟨d1, t1⟩
  have d_loop : denote (cloop c1) = denote (cloop c2) := by
    funext x; simp [denote]
    apply congr; simp
    funext s; rw [d1]
  constructor
  · exact d_loop
  · funext x; simp [TerminateRow]
    rw [t1]
    have := congr_fun d_loop
    rw [this]

theorem Sequiv_loop_lifted_congr {c1 c2: Ckt (A ×ᵥ B) B 1} (h: c1 ≃ c2):
    (cloop2 c1) ≃ (cloop2 c2) := by
  unfold Sequiv at *; rcases h with ⟨d1, t1⟩
  have d_loop : denote (cloop2 c1) = denote (cloop2 c2) := by
    funext x; simp [denote]
    apply congr; simp
    funext s; rw [d1]
  constructor
  · exact d_loop
  · funext x i
    simp [TerminateRow]
    rw [d_loop, t1]

-- incrementalize lemmas
@[simp]
theorem Sequiv_incr_chain (c1: Ckt A B ns) (c2: Ckt B C ns):
    cΔ (c1 >>c c2) ≃ (cΔ c1 >>c cΔ c2) := by
  unfold Sequiv; constructor
  · funext x; simp [denote]
    rw [chain_incremental]; simp
  · funext x i; unfold cΔ cI cD; simp [TerminateRow]
    rw [<- cI, <- cI, <- cD]; intro _
    simp [denote]

@[simp]
theorem Sequiv_incr_par (c1: Ckt A B ns) (c2: Ckt A C ns):
    cΔ (c1 &&c c2) ≃ (cΔ c1 &&c cΔ c2) := by
  unfold Sequiv; constructor
  · funext x; simp [denote]; rcases ns
    · funext n; simp [incremental, D, delay]
      rcases n <;> simp
    · funext m n; simp [incremental, D, delay]
      rcases m <;> simp
  · funext x i; unfold cΔ cI cD; simp [TerminateRow]

@[simp]
theorem Sequiv_incr_loop {c: Ckt (A ×ᵥ B) B ns}:
    cΔ (cloop c) ≃ cloop (cΔ c) := by
  have h_denote: denote (cΔ (cloop c)) = denote (cloop (cΔ c)) := by
    funext x; apply congr
    swap; simp
    simp [denote]
    rcases ns <;> simp
    · trans; apply (cycle_incremental (fun a s => denote c (sprod (a, s))))
      rw [uncurryOp_sprod_eq]
      apply causalO_is_causal; apply ckt_causalO
      funext a; apply congr; simp
      funext s; rw [incremental_sprod]
    · trans; apply (cycle_incremental (fun a s => denote c (sprod2 (a, s))))
      · unfold uncurryOp; simp
        apply causal_comp
        · intro s1 s2 t ht
          funext n; simp [sprod2]
          rw [ht] <;> tauto
        · apply causalO_is_causal; apply ckt_causalO
      · funext a; simp [incremental2, incremental]
        apply congr; tauto
        funext s; rw [integral_sprod2]
  unfold Sequiv; constructor
  · exact h_denote
  · funext x i; unfold cΔ cI cD; simp [TerminateRow]
    rw [<- cI, <- cI, <- cD, <- eq_iff_iff]
    congr
    simp_rw [cI_denote]
    unfold cΔ at h_denote; rw [<- h_denote]
    rcases ns <;> simp
    · rw [integral_sprod]; rw [sprod_eq_iff]
      rw [integral_timeInvariant]; simp [denote]
    · rw [integral_sprod2]; rw [sprod2_eq_iff]
      rw [integral_timeInvariant]; simp [denote]

@[simp]
theorem Sequiv_incr_loop2 {c: Ckt (A ×ᵥ B) B 1}:
    cΔ (cloop2 c) ≃ cloop2 (cΔ c) := by
  have h_denote: denote (cΔ (cloop2 c)) = denote (cloop2 (cΔ c)) := by
    funext x; apply congr
    swap; simp
    simp [denote]
    trans; apply (cycle2_incremental (fun a s => denote c (sprod2 (a, s))))
    · intro s; rw [<- causalO_true]
      apply causalO_comp; apply ckt_causalO
      apply causalO_sprodO; tauto
      apply causalO_id
    · funext a; simp [incremental2, incremental]
      apply congr; tauto
      funext s; rw [integral_sprod2]
  unfold Sequiv; constructor
  · exact h_denote
  · funext x i; unfold cΔ cI cD; simp [TerminateRow]
    rw [<- cI, <- cI, <- cD, <- eq_iff_iff]
    congr
    simp_rw [cI_denote]
    unfold cΔ at h_denote; rw [<- h_denote]
    rw [integral_sprod2]; rw [sprod2_eq_iff]; simp
    rw [integral_lift_comm]; simp [denote]
    apply delay_linear

@[simp]
theorem Sequiv_I_bracket {c: Ckt A B 1}:
    cI >>c (cbracket c) ≃ cbracket (cI >>c c) := by
  unfold Sequiv; constructor
  · funext x; simp [denote]
    apply congr; simp
    apply congr; simp
    funext m n; simp
    simp_rw [integral_sumVals]
    induction m <;> try simp
    rename_i m ih
    rcases n <;> simp at * <;> tauto
  · funext x i
    simp only [TerminateRow]
    simp [denote, IntFP2]
    rw [integral_lift_comm]; swap
    · apply delta_linear
    simp; intro _
    constructor <;> rintro ⟨b, ⟨hi, hz⟩⟩
    swap; tauto
    use (b+1)
    constructor; constructor
    · apply IntFP2_mono
      apply IntFP2_cI; simp
    · apply IntFP2_mono; tauto; simp
    · apply ZeroAfter_ge; tauto; simp

-- lifting lemmas
@[simp]
theorem Sequiv_lifting_seq {c1: Ckt A B 0} {c2: Ckt B C 0}:
    (c↑ (c1 >>c c2)) ≃ (c↑ c1) >>c (c↑ c2) := by
  unfold Sequiv; constructor
  · funext x; simp [denote, lifting]
    rw [lifting_distributivity]; simp
  · funext x i; simp [TerminateRow]
    apply Iff.intro
    · intro h; constructor <;> intro i <;> have := h i <;> tauto
    · intro h i; constructor <;> have := h.1 i <;> have := h.2 i <;> tauto

@[simp]
theorem Sequiv_lifting_par {c1: Ckt A B 0} {c2: Ckt A C 0}:
    c↑ (c1 &&c c2) ≃ (c↑ c1 &&c c↑ c2) := by
  unfold Sequiv; constructor
  · funext x; simp [denote, lifting, sprodO]
    funext m n; simp
  · funext x i; simp [TerminateRow]
    apply Iff.intro
    · intro h; constructor <;> intro i <;> have := h i <;> tauto
    · intro h i; constructor <;> have := h.1 i <;> have := h.2 i <;> tauto

@[simp]
theorem Sequiv_lifting_loop {c: Ckt (A ×ᵥ B) B 0}:
    c↑ (cloop c) ≃ cloop2 (c↑ c) := by
  have eq_denote: denote c↑ (cloop c) = denote (cloop2 c↑ c) := by
    funext x; simp [denote, sprodO]
    rw [lifting_cycle (fun a s => denote c (sprod (a, s)))]
    · apply congr; tauto
      funext s m n; simp
      congr
    · rw [uncurryOp_sprod_eq]
      apply causalO_is_causal; apply ckt_causalO
  unfold Sequiv; constructor
  · assumption
  funext x i; simp [TerminateRow]
  simp [sprodO]; rw [<- eq_denote]
  have : sprod (x i, z⁻¹ (denote (cloop c) (x i))) =
      sprod2 (x, ↑↑z⁻¹ (denote (c↑ (cloop c)) x)) i := by
    funext j
    simp [denote]
  rw [this]

-- Partial semantic equivalence
-- the output is equivalent only if both circuits terminate
def Pequiv (c1 c2: Ckt A B ns): Prop :=
  ∀ x, Terminate c1 x -> Terminate c2 x -> denote c1 x = denote c2 x
infix:30 " ≃ₚ " => Pequiv

theorem Sequiv_to_Pequiv {c1 c2: Ckt A B ns}:
    c1 ≃ c2 -> c1 ≃ₚ c2 := by
  unfold Sequiv Pequiv; tauto

theorem Pequiv_bracket_congr
  {c1 c2: Ckt (A ×ᵥ B) B 1} (h: c1 ≃ₚ c2) :
    (cbracket c1) ≃ₚ (cbracket c2) := by
  unfold Pequiv at *
  intro x ht1 ht2
  simp [Terminate] at ht1 ht2
  funext k; simp [denote]
  apply congr; simp
  rw [h] <;> tauto

lemma streamElim_D_comm
  {a : Type} [AddCommGroup a] (x: stream (stream a))
  (b: stream ℕ) (h: ZeroAfterVec x b):
    D (↑↑∫0 x) = ↑↑∫0 (D x) := by
  funext i; simp [D]
  have := streamElim_linear (x i) (- z⁻¹ x i)
  rcases i with _ | i; simp
  simp at this ⊢
  have hz1 := h (i+1)
  have hz2 := ZeroAfter_neg.2 (h i)
  specialize this _ hz1 _ hz2
  rw [<- sub_eq_add_neg] at this
  rw [this, streamElim_neg, sub_eq_add_neg]

theorem Pequiv_bracket_D {c: Ckt A B 1}:
    (cbracket c) >>c cD ≃ₚ cbracket (c >>c cD) := by
  unfold Pequiv
  intro x h1 h2
  simp [denote]
  simp [Terminate] at h1
  rcases h1 with ⟨⟨_, ⟨_, _⟩⟩, _⟩
  rw [streamElim_D_comm] <;> tauto

end Sequiv

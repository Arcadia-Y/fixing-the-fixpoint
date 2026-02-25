import DBSP.Practical.Sequiv
import DBSP.Logic.SProp
open CktBasic

section Refine
variable {A B C: VType} {ns: Bool}
-- `c1` is refined by `c2`
-- `c1` terminates implies that `c2` terminates and they have the same output
def Refine (c1 c2: Ckt A B ns): Prop :=
  ∀ x, Terminate c1 x -> Terminate c2 x ∧ denote c1 x = denote c2 x

infix:30 " ⊑ " => Refine

@[refl]
lemma Refine_rfl (c: Ckt A B ns): c ⊑ c := by
  unfold Refine; simp

@[trans]
lemma Refine_trans (c1 c2 c3: Ckt A B ns)
    (h1: c1 ⊑ c2) (h2: c2 ⊑ c3) : c1 ⊑ c3 := by
  intro x hx
  specialize h1 x; specialize h2 x
  simp[*]

lemma Sequiv_to_Refine {c1 c2: Ckt A B ns}:
    c1 ≃ c2 -> c1 ⊑ c2 := by
  intros h x hx
  rcases h with ⟨hd, ht⟩
  simp [hd]
  rw [<- ht]; tauto

-- Refinement congruence lemmas

lemma Refine_seq
    {c1 c2: Ckt A B ns} {d1 d2: Ckt B C ns}
    (hc: c1 ⊑ c2) (hd: d1 ⊑ d2):
      (c1 >>c d1) ⊑ (c2 >>c d2) := by
  unfold Refine
  intro x ht
  simp [Terminate] at ht ⊢
  rcases ht with ⟨htc1, htd1⟩
  specialize hc x htc1
  rcases hc with ⟨htc2, hdc⟩
  specialize hd (denote c1 x) htd1
  rcases hd with ⟨htd2, hdd⟩
  constructor
  · constructor
    · exact htc2
    · rw [← hdc]; exact htd2
  · simp [denote]
    rw [← hdc, hdd]

lemma Refine_par
  {c1 c2: Ckt A B ns} {d1 d2: Ckt A C ns}
  (hc: c1 ⊑ c2) (hd: d1 ⊑ d2):
    (c1 &&c d1) ⊑ (c2 &&c d2) := by
  unfold Refine
  intro x ht
  simp [Terminate] at ht ⊢
  rcases ht with ⟨htc1, htd1⟩
  specialize hc x htc1
  rcases hc with ⟨htc2, hdc⟩
  specialize hd x htd1
  rcases hd with ⟨htd2, hdd⟩
  constructor
  · constructor
    · exact htc2
    · exact htd2
  · simp [denote]
    rw [← hdc, ← hdd]

lemma Refine_cΔ {c1 c2: Ckt A B ns} (h: c1 ⊑ c2):
    (cΔ c1) ⊑ (cΔ c2) := by
  unfold cΔ
  apply Refine_seq
  apply Refine_seq
  rfl; tauto; rfl

lemma Refine_lifting {c1 c2: Ckt A B 0} (h: c1 ⊑ c2):
    (c↑ c1) ⊑ (c↑ c2) := by
  unfold Refine
  intro x ht
  simp [Terminate] at ht ⊢
  constructor
  · intro j; specialize h (x j) (ht j)
    rcases h with ⟨htj, hdj⟩; tauto
  · funext i j; simp [denote]
    specialize h (x i) (ht i)
    rw [h.2]

-- This is essentially a step-indexed proof
lemma Refine_loop {c1 c2: Ckt (A ×ᵥ B) B ns} (h: c1 ⊑ c2) :
    (cloop c1) ⊑ (cloop c2) := by
  unfold Refine; simp [Terminate]
  intro x ht
  set input1 := sprodO ns (x, z⁻¹ (denote (cloop c1) x))
  specialize h input1 ht
  have hd: denote (cloop c1) x = denote (cloop c2) x := by
    funext i; revert i
    rw [TrueUntil_forall]
    intro n; induction' n with n ih <;> simp [TrueUntil]
    · rw [loop_unfold c1, loop_unfold c2]
      rw [ckt_causal (s':= input1)]
      rw [ckt_causal c2 (s':= input1)]
      tauto
      all_goals (
        simp [input1];
        rw [sprodO_causal];
        constructor <;> simp [agreeUpto]
      )
    · intro m hm
      by_cases heq: m = n+1
      case neg =>
        apply ih; omega
      subst heq; clear hm
      rw [loop_unfold c1, loop_unfold c2]
      rw [ckt_causal (s':= input1)]
      rw [ckt_causal c2 (s':= input1)]
      tauto
      all_goals (
        simp [input1];
        rw [sprodO_causal];
        constructor <;> (try rfl) <;>
        rw [agreeUpto_delay_succ] <;>
        symm <;> apply ih
      )
  simp [hd]
  rw [<- hd]; tauto


lemma Refine_lifted_loop {c1 c2: Ckt (A ×ᵥ B) B 1} (h: c1 ⊑ c2) :
    (cloop2 c1) ⊑ (cloop2 c2) := by
  unfold Refine; simp [Terminate]
  intro x ht
  set input1 := sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c1) x))
  specialize h input1 ht
  have hd: denote (cloop2 c1) x = denote (cloop2 c2) x := by
    funext i j; revert i; revert j
    rw [TrueUntil_forall]
    intro n; induction' n with n ih <;> simp [TrueUntil]
    · rw [lifted_loop_unfold c1, lifted_loop_unfold c2]
      intro i
      rw [ckt_CausalNested (s':= input1)]
      rw [ckt_CausalNested c2 (s':= input1)]
      tauto
      all_goals (
        simp [input1, AgreeNested]
      )
    · intro m hm
      by_cases heq: m = n+1
      case neg =>
        apply ih; omega
      subst heq; clear hm
      rw [lifted_loop_unfold c1, lifted_loop_unfold c2]
      intro i
      rw [ckt_CausalNested c1 (s':= input1)]
      rw [ckt_CausalNested c2 (s':= input1)]
      tauto
      all_goals simp [input1, AgreeNested]
      intro m hm;
      rw [<- agreeUpto];
      rw [agreeUpto_delay_succ];
      symm; intro _ _; apply ih; omega
  simp [hd]
  rw [<- hd]; tauto

lemma Refine_incr_loop {c1 c2: Ckt (A ×ᵥ B) B ns} (hr: (cΔ c1) ⊑ c2):
    cΔ (cloop c1) ⊑ (cloop c2) := by
  apply Refine_trans
  apply Sequiv_to_Refine
  apply Sequiv_incr_loop
  apply Refine_loop hr

lemma Refine_incr_loop2 {c1 c2: Ckt (A ×ᵥ B) B 1} (hr: (cΔ c1) ⊑ c2):
    cΔ (cloop2 c1) ⊑ (cloop2 c2) := by
  apply Refine_trans
  apply Sequiv_to_Refine
  apply Sequiv_incr_loop2
  apply Refine_lifted_loop hr

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

lemma Refine_bracket_D {c: Ckt A B 1}:
    (cbracket c) >>c cD ⊑ cbracket (c >>c cD) := by
  intro x ht
  simp [Terminate] at ht ⊢
  rcases ht with ⟨ht, ⟨b, ⟨hif, hz⟩⟩⟩
  simp [ht]
  have hif': IntFP2Vec (c >>c cD) (↑↑δ0 x) (fun i => max (b i) (z⁻¹ b i)):= by
    intro m
    simp [IntFP2]
    constructor
    · apply IntFP2_mono
      apply hif; omega
    · apply D_IntFP2Vec
      apply ZeroAfterVec_impl_FixAfter2Vec
      tauto
  have hz': ZeroAfterVec (denote (c >>c cD) (↑↑δ0 x)) (fun i => max (b i) (z⁻¹ b i)) := by
    simp [denote]
    apply ZeroAfterVec_D
    tauto
  constructor; tauto
  simp [denote, D]
  funext k; simp
  nth_rw 2 [sub_eq_add_neg]
  rw [streamElim_linear]
  rw [<- streamElim_timeInvariant]; simp
  rw [sub_eq_add_neg]; simp
  rw [streamElim_neg]
  swap; apply hz
  swap; rw [ZeroAfter_neg]
  apply ZeroAfterVec_delay.1
  tauto

lemma Refine_incr_bracket {c: Ckt A B 1}:
    cΔ (cbracket c) ⊑ cbracket (cΔ c) := by
  unfold cΔ
  apply Refine_trans
  · apply Sequiv_to_Refine
    apply Sequiv_seq_cong
    apply Sequiv_I_bracket
    rfl
  apply Refine_bracket_D

end Refine

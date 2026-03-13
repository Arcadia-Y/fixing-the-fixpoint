import DBSP.Practical.Sequiv
import DBSP.Logic.SProp
open CktBasic

variable {A B C: VType} {ns: Bool}

-- Convergence equivalence with output agreement on converging inputs.
structure ConvEq (c1 c2: Ckt A B ns) where
  conv: Converge c1 = Converge c2
  denote: ∀ x, Converge c1 x -> denote c1 x = denote c2 x

-- Preferred notation.
infix:30 " ≋ " => ConvEq

@[refl]
lemma ConvEq_rfl (c: Ckt A B ns): c ≋ c := by
  exact ⟨rfl, by intro _ _; rfl⟩

@[symm]
lemma ConvEq_symm {c1 c2: Ckt A B ns} (h: c1 ≋ c2): c2 ≋ c1 := by
  refine ⟨h.conv.symm, ?_⟩
  intro x hx
  have hx' : Converge c1 x := by simpa [h.conv] using hx
  have hd := h.denote x hx'
  exact hd.symm

@[trans]
lemma ConvEq_trans {c1 c2 c3: Ckt A B ns}
  (h12: c1 ≋ c2) (h23: c2 ≋ c3): c1 ≋ c3 := by
  refine ⟨h12.conv.trans h23.conv, ?_⟩
  intro x hx
  calc
    denote c1 x = denote c2 x := h12.denote x hx
    _ = denote c3 x := h23.denote x (by simpa [h12.conv] using hx)

lemma Sequiv_to_ConvEq {c1 c2: Ckt A B ns} (h: c1 ≃ c2): c1 ≋ c2 := by
  rcases h with ⟨hd, _, hc⟩
  exact ⟨hc, by intro _ _; simp [hd]⟩

lemma ConvEq_denote_eq_of_terminate {c1 c2: Ckt A B ns}
  (h: c1 ≋ c2) {x} (ht: Terminate c1 x):
  denote c1 x = denote c2 x := by
  exact h.denote x (Terminate_impl_Converge ht)

lemma Converge_cΔ_of_Converge {A B ns} {c: Ckt A B ns} {x: SOVType ns A}
  (h: Converge c x):
  Converge (cΔ c) (D x) := by
  simp [cΔ, Converge, h, derivative_integral]

lemma denote_cΔ_D {A B ns} (c: Ckt A B ns) (x: SOVType ns A):
  denote (cΔ c) (D x) = D (denote c x) := by
  simp [cΔ, denote, derivative_integral]

lemma ConvEq_seq
    {c1 c2: Ckt A B ns} {d1 d2: Ckt B C ns}
    (hc: c1 ≋ c2) (hd: d1 ≋ d2):
      (c1 >>c d1) ≋ (c2 >>c d2) := by
  have hforward : ∀ x, Converge (c1 >>c d1) x -> Converge (c2 >>c d2) x := by
    intro x hx
    simp [Converge] at hx ⊢
    rcases hx with ⟨hc1x, hd1x⟩
    have hc2x : Converge c2 x := by simpa [hc.conv] using hc1x
    have hdc : denote c1 x = denote c2 x := hc.denote x hc1x
    have hd1x' : Converge d1 (denote c2 x) := by simpa [hdc] using hd1x
    have hd2x : Converge d2 (denote c2 x) := by simpa [hd.conv] using hd1x'
    exact ⟨hc2x, hd2x⟩
  have hbackward : ∀ x, Converge (c2 >>c d2) x -> Converge (c1 >>c d1) x := by
    intro x hx
    have hc' : c2 ≋ c1 := ConvEq_symm hc
    have hd' : d2 ≋ d1 := ConvEq_symm hd
    simp [Converge] at hx ⊢
    rcases hx with ⟨hc2x, hd2x⟩
    have hc1x : Converge c1 x := by simpa [hc'.conv] using hc2x
    have hdc : denote c2 x = denote c1 x := hc'.denote x hc2x
    have hd2x' : Converge d2 (denote c1 x) := by simpa [hdc] using hd2x
    have hd1x : Converge d1 (denote c1 x) := by simpa [hd'.conv] using hd2x'
    exact ⟨hc1x, hd1x⟩
  refine ⟨?_, ?_⟩
  · funext x
    apply propext
    exact ⟨hforward x, hbackward x⟩
  · intro x hx
    simp [Converge] at hx
    rcases hx with ⟨hc1x, hd1x⟩
    have hdc : denote c1 x = denote c2 x := hc.denote x hc1x
    have hdd : denote d1 (denote c1 x) = denote d2 (denote c1 x) :=
      hd.denote (denote c1 x) hd1x
    simp [denote]
    calc
      denote d1 (denote c1 x) = denote d2 (denote c1 x) := hdd
      _ = denote d2 (denote c2 x) := by simp [hdc]

lemma ConvEq_par
  {c1 c2: Ckt A B ns} {d1 d2: Ckt A C ns}
  (hc: c1 ≋ c2) (hd: d1 ≋ d2):
    (c1 &&c d1) ≋ (c2 &&c d2) := by
  refine ⟨?_, ?_⟩
  · funext x
    apply propext
    constructor
    · intro hx
      simp [Converge] at hx ⊢
      rcases hx with ⟨hc1x, hd1x⟩
      have hc2x : Converge c2 x := by simpa [hc.conv] using hc1x
      have hd2x : Converge d2 x := by simpa [hd.conv] using hd1x
      exact ⟨hc2x, hd2x⟩
    · intro hx
      simp [Converge] at hx ⊢
      rcases hx with ⟨hc2x, hd2x⟩
      have hc1x : Converge c1 x := by simpa [ConvEq_symm hc |>.conv] using hc2x
      have hd1x : Converge d1 x := by simpa [ConvEq_symm hd |>.conv] using hd2x
      exact ⟨hc1x, hd1x⟩
  · intro x hx
    simp [Converge] at hx
    rcases hx with ⟨hc1x, hd1x⟩
    have hdc : denote c1 x = denote c2 x := hc.denote x hc1x
    have hdd : denote d1 x = denote d2 x := hd.denote x hd1x
    simp [denote, hdc, hdd]

lemma ConvEq_cΔ {c1 c2: Ckt A B ns} (h: c1 ≋ c2):
    (cΔ c1) ≋ (cΔ c2) := by
  unfold cΔ
  apply ConvEq_seq
  apply ConvEq_seq
  rfl; tauto; rfl

lemma ConvEq_lifting {c1 c2: Ckt A B 0} (h: c1 ≋ c2):
    (c↑ c1) ≋ (c↑ c2) := by
  refine ⟨?_, ?_⟩
  · funext x
    apply propext
    constructor
    · intro hx
      simp [Converge] at hx ⊢
      intro j
      have hxj : Converge c1 (x j) := hx j
      exact (by simpa [h.conv] using hxj)
    · intro hx
      simp [Converge] at hx ⊢
      intro j
      have hxj : Converge c2 (x j) := hx j
      exact (by simpa [ConvEq_symm h |>.conv] using hxj)
  · intro x hx
    simp [Converge] at hx
    funext i j
    simp [denote]
    exact congrFun (h.denote (x i) (hx i)) j

-- This is essentially a step-indexed proof
lemma ConvEq_loop {c1 c2: Ckt (A ×ᵥ B) B ns} (h: c1 ≋ c2) :
    (cloop c1) ≋ (cloop c2) := by
  have hforward_gen : ∀ {cL cR: Ckt (A ×ᵥ B) B ns},
      cL ≋ cR -> ∀ x,
      Converge (cloop cL) x ->
      Converge (cloop cR) x ∧ denote (cloop cL) x = denote (cloop cR) x := by
    intro cL cR hLR x ht
    simp [Converge] at ht
    set input1 := sprodO ns (x, z⁻¹ (denote (cloop cL) x))
    have hcv : Converge cR input1 := by simpa [hLR.conv] using ht
    have hden_lr : denote cL input1 = denote cR input1 :=
      hLR.denote input1 ht
    have hd : denote (cloop cL) x = denote (cloop cR) x := by
      funext i; revert i
      rw [TrueUntil_forall]
      intro n; induction' n with n ih <;> simp [TrueUntil]
      · rw [loop_unfold cL, loop_unfold cR]
        rw [ckt_causal (s':= input1)]
        rw [ckt_causal cR (s':= input1)]
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
        rw [loop_unfold cL, loop_unfold cR]
        rw [ckt_causal (s':= input1)]
        rw [ckt_causal cR (s':= input1)]
        tauto
        all_goals (
          simp [input1];
          rw [sprodO_causal];
          constructor <;> (try rfl) <;>
          rw [agreeUpto_delay_succ] <;>
          symm <;> apply ih
        )
    have hloop : Converge (cloop cR) x := by
      simp [Converge]
      have hinput : input1 = sprodO ns (x, z⁻¹ (denote (cloop cR) x)) := by
        simp [input1, hd]
      simpa [hinput] using hcv
    exact ⟨hloop, hd⟩
  refine ⟨?_, ?_⟩
  · funext x
    apply propext
    constructor
    · intro hx
      exact (hforward_gen h x hx).1
    · intro hx
      exact (hforward_gen (ConvEq_symm h) x hx).1
  · intro x hx
    exact (hforward_gen h x hx).2


lemma ConvEq_lifted_loop {c1 c2: Ckt (A ×ᵥ B) B 1} (h: c1 ≋ c2) :
    (cloop2 c1) ≋ (cloop2 c2) := by
  have hforward_gen : ∀ {cL cR: Ckt (A ×ᵥ B) B 1},
      cL ≋ cR -> ∀ x,
      Converge (cloop2 cL) x ->
      Converge (cloop2 cR) x ∧ denote (cloop2 cL) x = denote (cloop2 cR) x := by
    intro cL cR hLR x ht
    simp [Converge] at ht
    set input1 := sprod2 (x, ↑↑z⁻¹ (denote (cloop2 cL) x))
    have hcv : Converge cR input1 := by simpa [hLR.conv] using ht
    have hden_lr : denote cL input1 = denote cR input1 :=
      hLR.denote input1 ht
    have hd : denote (cloop2 cL) x = denote (cloop2 cR) x := by
      funext i j; revert i; revert j
      rw [TrueUntil_forall]
      intro n; induction' n with n ih <;> simp [TrueUntil]
      · rw [lifted_loop_unfold cL, lifted_loop_unfold cR]
        intro i
        rw [ckt_CausalNested (s':= input1)]
        rw [ckt_CausalNested cR (s':= input1)]
        tauto
        all_goals (
          simp [input1, AgreeNested]
        )
      · intro m hm
        by_cases heq: m = n+1
        case neg =>
          apply ih; omega
        subst heq; clear hm
        rw [lifted_loop_unfold cL, lifted_loop_unfold cR]
        intro i
        rw [ckt_CausalNested cL (s':= input1)]
        rw [ckt_CausalNested cR (s':= input1)]
        tauto
        all_goals simp [input1, AgreeNested]
        intro m hm;
        rw [<- agreeUpto];
        rw [agreeUpto_delay_succ];
        symm; intro _ _; apply ih; omega
    have hloop : Converge (cloop2 cR) x := by
      simp [Converge]
      have hinput : input1 = sprod2 (x, ↑↑z⁻¹ (denote (cloop2 cR) x)) := by
        simp [input1, hd]
      simpa [hinput] using hcv
    exact ⟨hloop, hd⟩
  refine ⟨?_, ?_⟩
  · funext x
    apply propext
    constructor
    · intro hx
      exact (hforward_gen h x hx).1
    · intro hx
      exact (hforward_gen (ConvEq_symm h) x hx).1
  · intro x hx
    exact (hforward_gen h x hx).2

lemma ConvEq_incr_loop {c1 c2: Ckt (A ×ᵥ B) B ns} (hr: (cΔ c1) ≋ c2):
    cΔ (cloop c1) ≋ (cloop c2) := by
  apply ConvEq_trans
  apply Sequiv_to_ConvEq
  apply Sequiv_incr_loop
  apply ConvEq_loop hr

lemma ConvEq_incr_loop2 {c1 c2: Ckt (A ×ᵥ B) B 1} (hr: (cΔ c1) ≋ c2):
    cΔ (cloop2 c1) ≋ (cloop2 c2) := by
  apply ConvEq_trans
  apply Sequiv_to_ConvEq
  apply Sequiv_incr_loop2
  apply ConvEq_lifted_loop hr

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

lemma ConvEq_bracket_D {c: Ckt A B 1}:
    (cbracket c) >>c cD ≋ cbracket (c >>c cD) := by
  refine ⟨?_, ?_⟩
  · funext x; simp [Converge]
    intro _; simp [denote]
    constructor
    · rintro ⟨b, h⟩
      use (fun i => max (b i) (z⁻¹ b i))
      apply ZeroAfterVec_D; tauto
    · rintro ⟨b, h⟩
      rw [<- derivative_integral (denote c (↑↑δ0 x))]
      use (I b)
      apply ZeroAfterVec_I; tauto
  · intro x ht
    simp [Converge] at ht
    rcases ht with ⟨ht, hb⟩
    rcases hb with ⟨b, hz⟩
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
    exact hz

lemma ConvEq_incr_bracket {c: Ckt A B 1}:
    cΔ (cbracket c) ≋ cbracket (cΔ c) := by
  unfold cΔ
  apply ConvEq_trans
  · apply Sequiv_to_ConvEq
    apply Sequiv_seq_cong
    apply Sequiv_I_bracket
    rfl
  apply ConvEq_bracket_D

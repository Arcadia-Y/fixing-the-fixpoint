import DBSP.Circuits.Circuits_v6
import DBSP.Circuits.CktProp
import DBSP.Termination.Spec
import DBSP.Termination.FPProp
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

theorem Sequiv_lifted_loop_congr {c1 c2: Ckt (A ×ᵥ B) B 1} (h: c1 ≃ c2):
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

abbrev SemCkt (A B: VType) (ns: Bool) := Quotient (SetoidSequiv (A:=A) (B:=B) (ns:=ns))

abbrev toSem {A B ns} (c: Ckt A B ns): SemCkt A B ns := Quotient.mk (SetoidSequiv) c

theorem Sequiv_iff_toSem_eq {c1 c2 : Ckt A B ns}:
    c1 ≃ c2 ↔ toSem c1 = toSem c2 := Iff.symm (@Quotient.eq _ SetoidSequiv c1 c2)

def SemCkt.seq {A B C ns} (c1: SemCkt A B ns) (c2: SemCkt B C ns): SemCkt A C ns :=
  Quotient.liftOn₂ c1 c2 (fun c1 c2 => toSem (c1 >>c c2)) (fun _ _ _ _ h1 h2 => Quotient.sound (s := SetoidSequiv) (Sequiv_seq_cong h1 h2))

infixl:60 " >>s "  => SemCkt.seq

@[simp]
theorem SemCkt_seq_lift (c1: Ckt A B ns) (c2: Ckt B C ns):
    (toSem c1 >>s toSem c2) = toSem (c1 >>c c2) := rfl

def SemCkt.par {A B C ns} (c1: SemCkt A B ns) (c2: SemCkt A C ns): SemCkt A (B ×ᵥ C) ns :=
  Quotient.liftOn₂ c1 c2 (fun c1 c2 => toSem (c1 &&c c2)) (fun _ _ _ _ h1 h2 => Quotient.sound (s := SetoidSequiv) (Sequiv_par_cong h1 h2))

infixl:50 " &&s " => SemCkt.par

@[simp]
theorem SemCkt_par_lift (c1: Ckt A B ns) (c2: Ckt A C ns):
    (toSem c1 &&s toSem c2) = toSem (c1 &&c c2) := rfl

def SemCkt.lifting {A B} (c: SemCkt A B 0): SemCkt A B 1 :=
  Quotient.liftOn c (fun c => toSem (Ckt.lifting c)) (fun _ _ h => Quotient.sound (s := SetoidSequiv) (Sequiv_lifting_congr h))

notation:max "s↑ " c:max => SemCkt.lifting c

@[simp]
theorem SemCkt_lifting_lift (c: Ckt A B 0):
    (s↑ (toSem c)) = toSem (c↑ c) := rfl

def SemCkt.loop {A B ns} (c: SemCkt (A ×ᵥ B) B ns): SemCkt A B ns :=
  Quotient.liftOn c (fun c => toSem (cloop c)) (fun _ _ h => Quotient.sound (s := SetoidSequiv) (Sequiv_loop_congr h))

notation "sloop " c:max => SemCkt.loop c

@[simp]
theorem SemCkt_loop_lift (c: Ckt (A ×ᵥ B) B ns):
    (sloop (toSem c)) = toSem (cloop c) := rfl

def SemCkt.lifted_loop {A B} (c: SemCkt (A ×ᵥ B) B 1): SemCkt A B 1 :=
  Quotient.liftOn c (fun c => toSem (cloop2 c)) (fun _ _ h => Quotient.sound (s := SetoidSequiv) (Sequiv_lifted_loop_congr h))

notation "sloop2 " c:max => SemCkt.lifted_loop c

@[simp]
theorem SemCkt_lifted_loop_lift (c: Ckt (A ×ᵥ B) B 1):
    (sloop2 (toSem c)) = toSem (cloop2 c) := rfl

-- incrementalize lemmas
lemma DenoteLiftedScalar_Sequiv_incr {ns} {a b} (c: Ckt a b ns)
  (ht: ∀ x, Terminate c x)
  {f: VType_interp a -> VType_interp b}
  (hf: DenoteLiftedScalar c f)
  (hfl: ∀ x y, f (x + y) = f x + f y):
   (cΔ c) ≃ c := by
  have ht: ∀ x n, TerminateRow c x n := by
    intro x n
    specialize ht x
    rw [Terminate_iff] at ht
    tauto
  simp [Sequiv]; constructor; swap
  · simp [cΔ, TerminateRow]
    funext x i
    rw [eq_iff_iff]
    tauto
  rw [lti_incremental]
  rw [hf]
  rcases ns <;> simp [liftO] <;> apply lifting_lti
  · simp [hfl]
  intro x y; funext t
  simp [hfl]

theorem Sequiv_incr_id:
    cΔ cid ≃ (@Ckt.id ns A) := by
  apply DenoteLiftedScalar_Sequiv_incr (f := id)
  · intro; simp [Terminate]
  · rfl
  · intros; rfl

theorem Sequiv_incr_fst:
    cΔ c1st ≃ (@Ckt.fst ns A B) := by
  apply DenoteLiftedScalar_Sequiv_incr (f := Prod.fst)
  case ht => intro; simp [Terminate]
  case hf => rfl
  case hfl => intros; rfl

theorem Sequiv_incr_snd:
    cΔ c2nd ≃ (@Ckt.snd ns A B) := by
  apply DenoteLiftedScalar_Sequiv_incr (f := Prod.snd)
  case ht => intro; simp [Terminate]
  case hf => rfl
  case hfl => intros; rfl

theorem Sequiv_incr_add:
    cΔ cadd ≃ (@Ckt.add ns A) := by
  apply DenoteLiftedScalar_Sequiv_incr (f := fun (x : VType_interp (A ×ᵥ A)) => x.1 + x.2)
  · intro; simp [Terminate]
  · rfl
  · intros x y; simp; abel

theorem Sequiv_incr_sub:
    cΔ csub ≃ (@Ckt.sub ns A) := by
  apply DenoteLiftedScalar_Sequiv_incr (f := fun (x : VType_interp (A ×ᵥ A)) => x.1 - x.2)
  · intro; simp [Terminate]
  · rfl
  · intros x y; simp [sub_eq_add_neg]; abel

theorem Sequiv_incr_const x:
    cΔ (cconst x) ≃ (@Ckt.const ns A B x) >>c cD := by
  simp [Sequiv]
  constructor
  · -- denote part
    funext s; simp [denote, cΔ, cI, cD]
    rcases ns <;> simp [incremental, I, D, liftO, delay]
    · funext t; rcases t <;> simp
    · funext m n; rcases m <;> simp
  · -- TerminateRow part
    funext y i; simp [TerminateRow, cΔ, cI, cD, denote]

theorem Sequiv_incr_delay:
    cΔ cz⁻¹ ≃ (@Ckt.delay ns A) := by
  simp [Sequiv]; constructor
  · simp [denote]
    rcases ns <;>
    apply delay_incremental
  · simp [cΔ, TerminateRow]

theorem Sequiv_incr_lifted_delay:
    cΔ c↑z⁻¹ ≃ (@Ckt.lifted_delay A) := by
  simp [Sequiv]; constructor
  · simp [denote]
    apply lti_incremental
    apply lifting_lti
    apply delay_linear
  · simp [cΔ, TerminateRow]

theorem Sequiv_incr_seq (c1: Ckt A B ns) (c2: Ckt B C ns):
    cΔ (c1 >>c c2) ≃ (cΔ c1 >>c cΔ c2) := by
  unfold Sequiv; constructor
  · funext x; simp [denote]
    rw [chain_incremental]; simp
  · funext x i; unfold cΔ cI cD; simp [TerminateRow]
    rw [<- cI, <- cI, <- cD]; intro _
    simp [denote]

theorem Sequiv_incr_par (c1: Ckt A B ns) (c2: Ckt A C ns):
    cΔ (c1 &&c c2) ≃ (cΔ c1 &&c cΔ c2) := by
  unfold Sequiv; constructor
  · funext x; simp [denote]; rcases ns
    · funext n; simp [incremental, D, delay]
      rcases n <;> simp
    · funext m n; simp [incremental, D, delay]
      rcases m <;> simp
  · funext x i; unfold cΔ cI cD; simp [TerminateRow]

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
      apply I_IntFP2_delta; simp
    · apply IntFP2_mono; tauto; simp
    · apply ZeroAfter_ge; tauto; simp

-- lifting lemmas
theorem Sequiv_lifting_delay:
    c↑ (@Ckt.delay 0 A) ≃ Ckt.lifted_delay := by
  unfold Sequiv; constructor
  · funext x; simp [denote, lifting, liftO, delay]
  · funext x i; simp [TerminateRow]

theorem Sequiv_lifting_seq {c1: Ckt A B 0} {c2: Ckt B C 0}:
    (c↑ (c1 >>c c2)) ≃ (c↑ c1) >>c (c↑ c2) := by
  unfold Sequiv; constructor
  · funext x; simp [denote, lifting]
    rw [lifting_distributivity]; simp
  · funext x i; simp [TerminateRow]
    apply Iff.intro
    · intro h; constructor <;> intro i <;> have := h i <;> tauto
    · intro h i; constructor <;> have := h.1 i <;> have := h.2 i <;> tauto

theorem Sequiv_lifting_par {c1: Ckt A B 0} {c2: Ckt A C 0}:
    c↑ (c1 &&c c2) ≃ (c↑ c1 &&c c↑ c2) := by
  unfold Sequiv; constructor
  · funext x; simp [denote, lifting, sprodO]
    funext m n; simp
  · funext x i; simp [TerminateRow]
    apply Iff.intro
    · intro h; constructor <;> intro i <;> have := h i <;> tauto
    · intro h i; constructor <;> have := h.1 i <;> have := h.2 i <;> tauto

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

-- SemCkt lemmas for incrementalization


-- SemCkt lemmas for lifting
@[simp]
theorem SemCkt_lifting_delay {A: VType}:
    s↑ (toSem (@Ckt.delay 0 A)) = toSem Ckt.lifted_delay := by
  rw [SemCkt_lifting_lift]
  apply Quotient.sound
  apply Sequiv_lifting_delay

@[simp]
theorem SemCkt_lifting_seq (c1: SemCkt A B 0) (c2: SemCkt B C 0):
    (s↑ (c1 >>s c2)) = (s↑ c1) >>s (s↑ c2) := by
  induction c1 using Quotient.inductionOn
  induction c2 using Quotient.inductionOn
  rw [SemCkt_seq_lift, SemCkt_lifting_lift, SemCkt_lifting_lift, SemCkt_lifting_lift, SemCkt_seq_lift]
  apply Quotient.sound
  apply Sequiv_lifting_seq

@[simp]
theorem SemCkt_lifting_par (c1: SemCkt A B 0) (c2: SemCkt A C 0):
    s↑ (c1 &&s c2) = (s↑ c1 &&s s↑ c2) := by
  induction c1 using Quotient.inductionOn
  induction c2 using Quotient.inductionOn
  rw [SemCkt_par_lift, SemCkt_lifting_lift, SemCkt_lifting_lift, SemCkt_lifting_lift, SemCkt_par_lift]
  apply Quotient.sound
  apply Sequiv_lifting_par

@[simp]
theorem SemCkt_lifting_loop {A B : VType} (c : SemCkt (A ×ᵥ B) B 0) :
    s↑ (sloop c) = sloop2 (s↑ c) := by
  induction c using Quotient.inductionOn
  rw [SemCkt_loop_lift, SemCkt_lifting_lift, SemCkt_lifting_lift, SemCkt_lifted_loop_lift]
  apply Quotient.sound
  apply Sequiv_lifting_loop

end Sequiv

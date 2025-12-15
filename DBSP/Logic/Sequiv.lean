import DBSP.StreamTheory.Stream
import DBSP.StreamTheory.Linear
import DBSP.Circuits.Circuits_v3
import DBSP.Logic.SProp
open CktBasic

section Sequiv
variable {n: ℕ} {A B C: VType} {ns: Bool}

-- semantic equivalence for Ckts
def Sequiv (c1 c2: Ckt ns A B): Prop :=
   denote c1 = denote c2
infix:30 " ≃ " => Sequiv

-- equivalence relation
@[refl]
theorem Sequiv_rfl (c: Ckt ns A B): c ≃ c := by funext x; rfl

@[symm]
theorem Sequiv_symm {c1 c2: Ckt ns A B}: c1 ≃ c2 → c2 ≃ c1 := by
  intro h; funext x; symm; tauto

@[trans]
theorem Sequiv_trans {c1 c2 c3: Ckt ns A B}: c1 ≃ c2 → c2 ≃ c3 → c1 ≃ c3 := by
  intro h1 h2; funext x; rw [h1, h2]

instance SetoidSequiv : Setoid (Ckt ns A B) where
  r := Sequiv
  iseqv := ⟨Sequiv_rfl, Sequiv_symm, Sequiv_trans⟩

-- congruence properties
theorem Sequiv_seq_cong {c1 c3: Ckt ns A B} {c2 c4: Ckt ns B C}
  (h1: c1 ≃ c3) (h2: c2 ≃ c4):
    c1 >>c c2 ≃ c3 >>c c4 := by
  funext x; simp [denote, h1, h2]
  rw [h1, h2]

theorem Sequiv_seq_assoc {D: VType} {c1: Ckt ns A B}
  {c2: Ckt ns B C} {c3: Ckt ns C D}:
    c1 >>c c2 >>c c3 ≃ c1 >>c (c2 >>c c3) := by
  funext x; simp [denote]

theorem Sequiv_par_cong {c1 c3: Ckt ns A B} {c2 c4: Ckt ns A C}
  (h1: c1 ≃ c3) (h2: c2 ≃ c4):
    c1 &&c c2 ≃ c3 &&c c4 := by
  funext x; simp [denote, h1, h2]
  rw [h1, h2]

theorem Sequiv_lifting_congr {c1 c2: Ckt false A B} (h: c1 ≃ c2):
    (c↑ c1) ≃ (c↑ c2) := by
  funext x; funext n; simp [denote, lifting]
  rw [h]

theorem Sequiv_loop_congr {c1 c2: Ckt ns (A ×ᵥ B) B} (h: c1 ≃ c2):
    (cloop c1) ≃ (cloop c2) := by
  funext x; simp [denote]
  apply congr; simp
  funext s; rw [h]

theorem Sequiv_loop_lifted_congr {c1 c2: Ckt true (A ×ᵥ B) B} (h: c1 ≃ c2):
    (cloop2 c1) ≃ (cloop2 c2) := by
  funext x; simp [denote]
  apply congr; simp
  funext s; rw [h]

theorem Sequiv_bracket_congr {c1 c2: Ckt true A B} {fc1 fc2}
  (h: c1 ≃ c2) :
    (cbracket c1 fc1) ≃ (cbracket c2 fc2) := by
  funext x; simp [denote]
  apply congr; simp
  rw [h]

-- incrementalize lemmas
@[simp]
theorem Sequiv_incr_chain (c1: Ckt ns A B) (c2: Ckt ns B C):
    cΔ (c1 >>c c2) ≃ (cΔ c1 >>c cΔ c2) := by
  funext x; simp [denote]
  rw [chain_incremental]; simp

@[simp]
theorem Sequiv_incr_par (c1: Ckt ns A B) (c2: Ckt ns A C):
    cΔ (c1 &&c c2) ≃ (cΔ c1 &&c cΔ c2) := by
  funext x; simp [denote]; rcases ns
  · funext n; simp [incremental, D, delay]
    rcases n <;> simp
  · funext m n; simp [incremental, D, delay]
    rcases m <;> simp

@[simp]
theorem Sequiv_incr_loop {c: Ckt ns (A ×ᵥ B) B}:
    cΔ (cloop c) ≃ cloop (cΔ c) := by
  funext x; apply congr
  swap; simp
  simp [denote]
  rcases ns <;> simp
  · trans; apply (cycle_incremental (fun a s => denote c (sprod (a, s))))
    rw [uncurryOp_sprod_eq]
    apply causalO_is_causal; apply causalO_ckt
    funext a; apply congr; simp
    funext s; rw [incremental_sprod]
  · trans; apply (cycle_incremental (fun a s => denote c (sprod2 (a, s))))
    · unfold uncurryOp; simp
      apply causal_comp
      · intro s1 s2 t ht
        funext n; simp [sprod2]
        rw [ht] <;> tauto
      · apply causalO_is_causal; apply causalO_ckt
    · funext a; simp [incremental2, incremental]
      apply congr; tauto
      funext s; rw [integral_sprod2]

@[simp]
theorem Sequiv_incr_loop2 {c: Ckt true (A ×ᵥ B) B}:
    cΔ (cloop2 c) ≃ cloop2 (cΔ c) := by
  funext x; apply congr
  swap; simp
  simp [denote]
  trans; apply (cycle2_incremental (fun a s => denote c (sprod2 (a, s))))
  · intro s; rw [<- causalO_true]
    apply causalO_comp; apply causalO_ckt
    apply causalO_sprodO; tauto
    apply causalO_id
  · funext a; simp [incremental2, incremental]
    apply congr; tauto
    funext s; rw [integral_sprod2]

@[simp]
theorem Sequiv_I_bracket {c: Ckt true A B} {fc}:
    cI >>c (cbracket c fc) ≃ cbracket (cI >>c c) fc := by
  funext x; simp [denote]
  apply congr; simp
  apply congr; simp
  funext m n; simp
  simp_rw [integral_sumVals]
  induction m <;> try simp
  rename_i m ih
  rcases n <;> simp at * <;> tauto

-- lifting lemmas
@[simp]
theorem Sequiv_lifting_seq {c1: Ckt false A B} {c2: Ckt false B C}:
    (c↑ (c1 >>c c2)) ≃ (c↑ c1) >>c (c↑ c2) := by
  funext x; simp [denote, lifting]
  rw [lifting_distributivity]; simp

@[simp]
theorem Sequiv_lifting_par {c1: Ckt false A B} {c2: Ckt false A C}:
    c↑ (c1 &&c c2) ≃ (c↑ c1 &&c c↑ c2) := by
  funext x; simp [denote, lifting, sprodO]
  funext m n; simp

@[simp]
theorem Sequiv_lifting_loop {c: Ckt false (A ×ᵥ B) B}:
    c↑ (cloop c) ≃ cloop2 (c↑ c) := by
  funext x; simp [denote, sprodO]
  rw [lifting_cycle (fun a s => denote c (sprod (a, s)))]
  · apply congr; tauto
    funext s m n; simp
    congr
  · rw [uncurryOp_sprod_eq]
    apply causalO_is_causal; apply causalO_ckt

-- Sequiv on certain input
-- used to deal with equivalence only when convergence
def SequivOn (P: SPred (OVType ns A)) (c1 c2: Ckt ns A B)  :=
  ∀ x n, true_until n (P x) -> denote c1 x =[n]= denote c2 x

notation:30 c1 " ≃[" P "] " c2 => SequivOn P c1 c2

variable {P: Operator (OVType ns A) Prop}

@[refl]
theorem SequivOn_rfl {c: Ckt ns A B}:
  c ≃[ P ] c := by
  intro x n h; rfl

@[symm]
theorem SequivOn_symm {c1 c2: Ckt ns A B}:
  (c1 ≃[ P ] c2) -> c2 ≃[ P ] c1 := by
  intro h x n hp; symm; tauto

theorem SequivOn_to_Sequiv {c1 c2: Ckt ns A B}
  (h: ∀ x n, true_until n (P x))
  (heq: c1 ≃[ P ] c2):
    c1 ≃ c2 := by
  funext x; apply funext; intro n
  apply heq x n (h x n); omega

-- Spred for iteration bound
-- it specifies that if `x` go through the circuit `↑δ0 -> c`
-- then `b` should be an upperbound for the iteration rounds
def IterBound (c: Ckt true A B) (b: stream ℕ): SPred (VType_interp A) :=
  fun x i => ZeroAfter (denote c (↑↑δ0 x) i) (b i)

theorem Sequiv_bracket_D (c: Ckt true A B) {fc} (b: stream ℕ):
    (cbracket c fc >>c cD) ≃[IterBound c b] (cbracket (c >>c cD) fc) := by
  intro x n hp i hi; simp [denote, D]
  have hsl := streamElim_linear (denote c (↑↑δ0 x) i) (- z⁻¹ (denote c (↑↑δ0 x)) i)
  specialize hsl (b i) (hp i hi)
  specialize hsl (b (i-1)) (by
    simp [ZeroAfter]; intros t ht
    simp [delay]; rcases i <;> simp
    rename_i i
    simp at ht
    apply hp <;> omega
  )
  abel_nf at hsl; abel_nf
  rw [hsl]; simp; clear hsl
  rw [<- streamElim_timeInvariant]; simp
  simp [delay]
  split_ifs; simp
  iterate 2 rw [streamElim_zeroAfter _ (b (i-1))]
  simp
  · intro m hm; simp
    apply hp <;> omega
  · apply hp; omega

theorem Sequiv_SequivOn_congr {c1 c2 c3 c4: Ckt ns A B}
  (h1: c1 ≃ c3) (h2: c2 ≃ c4) (h: c1 ≃[P] c2):
    c3 ≃[P] c4 := by
  intro x n hp i hi; simp [denote]
  rw [<- h1, <- h2]; apply h <;> tauto

theorem Sequiv_incr_bracket {c: Ckt true A B} {fc} (b: stream ℕ):
    cΔ (cbracket c fc) ≃[IterBound (cI >>c c) b] (cbracket (cΔ c) fc) := by
  simp [cΔ]
  have : cI >>c cbracket c fc >>c cD ≃ cbracket (cI >>c c) fc >>c cD := by
    apply Sequiv_seq_cong
    apply Sequiv_I_bracket; rfl
  apply Sequiv_SequivOn_congr
  symm; apply this; rfl
  apply Sequiv_bracket_D

end Sequiv

import DBSP.Practical.Refine
open CktBasic

section Preserve
variable {A B C: VType} {ns: Bool}
-- These two definitions are almost merely for incremnetalization proofs

-- This asserts that the `IntFP1` of `c1` is preserved when
-- we transform it into `c2` (which is supposed to be its incremental version)
def Preserve1 {ns A B} (c1 c2: Ckt A B ns) : Prop :=
  ∀ x n, Terminate c1 x -> IntFP1 c1 x n -> IntFP1 c2 (D x) (n+1)
infix:30 " ↝₁ " => Preserve1
-- This asserts that the `IntFP2` of `c1` is preserved when
-- we transform it into `c2` (which is supposed to be its incremental version)
def Preserve2 {A B} (c1 c2: Ckt A B 1) : Prop :=
    ∀ x b, Terminate c1 x -> IntFP2Vec c1 x b ->
      IntFP2Vec c2 (D x) (fun i => max (b i) (z⁻¹ b i))
infix:30 " ↝₂ " => Preserve2

macro "solve_FixAfter1_D" h1:ident : tactic => `(tactic| (
  rw [<- ZeroAfter_succ_D_FixAfter1] at $h1:ident
  apply ZeroAfter_impl_FixAfter1
  assumption
))

-- Tactic macro for basic lifted scalar refinement proofs
macro "solve_preserve1_basic" : tactic => `(tactic| (
  simp [Preserve1, IntFP1]
  rintro x n ht ⟨h1, h2⟩
  rw [lifted_Ckt_ExtFP1]
  · solve_FixAfter1_D h1
  · simp
))

lemma Preserve1_node1_self {A B: Type}
  [BaseType A] [BaseType B] (un: UnaryNode A B):
    (Ckt.node1 (ns:=ns) un) ↝₁ (Ckt.node1 un) := by
  solve_preserve1_basic

lemma Preserve1_node2_self {A B C: Type}
  [BaseType A] [BaseType B] [BaseType C] (bn: BinaryNode A B C):
    (Ckt.node2 (ns:=ns) bn) ↝₁ (Ckt.node2 bn) := by
  solve_preserve1_basic

lemma Preserve1_node2_bilinear {A B C: Type}
  [BaseType A] [BaseType B] [BaseType C] (bn: BinaryNode A B C):
    (Ckt.node2 (ns:=ns) bn) ↝₁ (bilinear_opt (c₂ bn)) := by
  simp [Preserve1, IntFP1]
  rintro x n ht ⟨hx, _⟩
  simp [bilinear_opt, IntFP1, denote]
  have eqx := unfold_sprodO x
  set a := liftO ns Prod.fst x
  set b := liftO ns Prod.snd x
  rw [eqx] at ht hx ⊢; simp [D_sprodO]
  have hab := FixAfter1_sprodO.1 hx
  rcases hab with ⟨ha, hb⟩
  rw [<- ZeroAfter_succ_D_FixAfter1] at hx
  simp [D_sprodO] at hx; apply ZeroAfter_impl_FixAfter1 at hx
  have hda := ZeroAfter_succ_D_FixAfter1.2 ha
  have hdb := ZeroAfter_succ_D_FixAfter1.2 hb
  have ha' := FixAfter1_mono (n2:=n+1) ha (by simp)
  have hb' := FixAfter1_mono (n2:=n+1) hb (by simp)
  have hdaf := ZeroAfter_impl_FixAfter1 hda
  have hdbf := ZeroAfter_impl_FixAfter1 hdb
  have hzb := FixAfter1_delay_succ.2 hb
  have hj1 := FixAfter1_sprodO.2 ⟨ha', hdbf⟩
  have hj2 := FixAfter1_sprodO.2 ⟨hdaf, hzb⟩
  have hadd1 := FixAfter1_liftO (f:= bn.f) hj1
  have hadd2 := FixAfter1_liftO (f:= bn.f) hj2
  have haddi := FixAfter1_sprodO.2 ⟨hadd1, hadd2⟩
  have haddo := FixAfter1_liftO (f:= fun a => a.1+ a.2) haddi
  simp [ExtFP1, *, denote]
  constructor <;> apply I_IntFP1 <;>
  rcases ns <;> simp [*]

lemma Preserve1_id:
    cid ↝₁ (@Ckt.id ns A) := by
  solve_preserve1_basic

lemma Preserve1_fst:
    c1st ↝₁ (@Ckt.fst ns A B) := by
  solve_preserve1_basic

lemma Preserve1_snd:
    c2nd ↝₁ (@Ckt.snd ns A B) := by
  solve_preserve1_basic

lemma Preserve1_add:
    cadd ↝₁ (@Ckt.add ns A) := by
  solve_preserve1_basic

lemma Preserve1_sub:
    csub ↝₁ (@Ckt.sub ns A) := by
  solve_preserve1_basic

lemma Preserve1_const k:
    (cconst k) ↝₁ (@Ckt.const ns A B k) >>c cD := by
  simp [Preserve1, IntFP1]
  rintro x n ht ⟨h1, _⟩
  constructor
  · rw [lifted_Ckt_ExtFP1]
    solve_FixAfter1_D h1
    simp
  · apply D_IntFP1
    rcases ns <;> rw [ZeroAfter_succ_D_FixAfter1] <;>
    intro m _ <;> simp [denote]
    funext t; simp

lemma Preserve1_delay:
    cz⁻¹ ↝₁ (@Ckt.delay ns A) := by
  simp [Preserve1, IntFP1]
  rintro x n ht ⟨h1, h2⟩
  simp [denote] at h2
  constructor
  · solve_FixAfter1_D h1
  · simp [denote]
    rcases ns <;>
    rw [<- derivative_timeInvariant] <;>
    solve_FixAfter1_D h2

lemma Preserve1_lifted_delay:
    c↑z⁻¹ ↝₁ (@Ckt.lifted_delay A) := by
  solve_preserve1_basic

lemma Preserve1_incr {c: Ckt A B ns}:
    c ↝₁ cΔ c := by
  simp [Preserve1]
  intro x n ht hi
  have he := IntFP1_impl_ExtFP1 _ _ _ hi
  rcases he with ⟨h1, h2⟩
  simp [cΔ, IntFP1]
  constructor; constructor
  · apply I_IntFP1
    rcases ns <;> simp [h1]
  · apply IntFP1_mono; tauto; omega
  · simp [denote]
    apply D_IntFP1
    rcases ns <;>
    rw [ZeroAfter_succ_D_FixAfter1] <;>
    tauto

lemma Preserve1_seq {c1 c3: Ckt A B ns} {c2 c4: Ckt B C ns}
  (h1: c1 ↝₁ c3) (h2: c2 ↝₁ c4) (hr: (cΔ c1) ⊑ c3):
    (c1 >>c c2) ↝₁ (c3 >>c c4) := by
  simp [Preserve1, IntFP1]
  rintro x n ⟨ht1, ht2⟩ hi1 hi2
  constructor
  · apply h1 <;> tauto
  specialize hr (D x) (Terminate_cΔ ht1)
  rcases hr with ⟨ht3, hd⟩
  simp [cΔ, denote] at hd
  rw [<- hd]
  apply h2 <;> tauto

lemma Preserve1_par {c1 c3: Ckt A B ns} {c2 c4: Ckt A C ns}
  (h1: c1 ↝₁ c3) (h2: c2 ↝₁ c4):
    (c1 &&c c2) ↝₁ (c3 &&c c4) := by
  simp [Preserve1, IntFP1]
  rintro x n ⟨ht1, ht2⟩ hi1 hi2
  constructor
  · apply h1 <;> tauto
  · apply h2 <;> tauto

lemma Preserve1_loop {c1 c2: Ckt (A ×ᵥ B) B ns}
  (h: c1 ↝₁ c2) (hr: (cΔ c1) ⊑ c2):
    (cloop c1) ↝₁ (cloop c2) := by
  intro x n ht
  simp [IntFP1]; intro hi
  have hrl := Refine_incr_loop hr
  have htd := Terminate_cΔ ht
  specialize hrl _ htd
  rcases hrl with ⟨_, hd⟩
  have : denote (cΔ (cloop c1)) (D x) = D (denote (cloop c1) x) := by
    simp [cΔ, denote]
  rw [this] at hd; rw [<- hd]
  have : sprodO ns (D x, z⁻¹ (D (denote (cloop c1) x))) =
         D (sprodO ns (x, z⁻¹ (denote (cloop c1) x))) := by
    rcases ns <;> rw [<- derivative_timeInvariant] <;>
    rw [D_sprodO]
  simp [Terminate] at ht
  rw [this]
  apply h <;> tauto

-- The proof is almost identical to the above
lemma Preserve1_lifted_loop {c1 c2: Ckt (A ×ᵥ B) B 1}
  (h: c1 ↝₁ c2) (hr: (cΔ c1) ⊑ c2):
    (cloop2 c1) ↝₁ (cloop2 c2) := by
  intro x n ht
  simp [IntFP1]; intro hi
  have hrl := Refine_incr_loop2 hr
  have htd := Terminate_cΔ ht
  specialize hrl _ htd
  rcases hrl with ⟨_, hd⟩
  have : denote (cΔ (cloop2 c1)) (D x) = D (denote (cloop2 c1) x) := by
    simp [cΔ, denote]
  rw [this] at hd; rw [<- hd]
  have : sprod2 (D x, ↑↑z⁻¹ (D (denote (cloop2 c1) x))) =
         D (sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c1) x))) := by
    rw [D_sprod2 (a := VType_interp A) (b := VType_interp B)]
    rw [← D_lifting_delay_comm]
  simp [Terminate] at ht
  rw [this]
  apply h <;> tauto

macro "solve_preserve2_basic" : tactic => `(tactic| (
  simp [Preserve2, IntFP2Vec, IntFP2]
  intro x b ht hef i
  rw [LiftedScalar_ExtFP2 (hc:= by constructor)]
  apply FixAfter2Vec_D
  rw [<- ExtFP2Vec, ExtFP2Vec_iff] at hef
  tauto
))

lemma Preserve2_node1_self {A B: Type}
  [BaseType A] [BaseType B] (un: UnaryNode A B):
    (Ckt.node1 un) ↝₂ (Ckt.node1 un) := by
  solve_preserve2_basic

lemma Preserve2_node2_self {A B C: Type}
  [BaseType A] [BaseType B] [BaseType C] (bn: BinaryNode A B C):
    (Ckt.node2 bn) ↝₂ (Ckt.node2 bn) := by
  solve_preserve2_basic

lemma Preserve2_node2_bilinear {A B C: Type}
  [BaseType A] [BaseType B] [BaseType C] (bn: BinaryNode A B C):
    (Ckt.node2 bn) ↝₂ (bilinear_opt (c₂ bn)) := by
  simp [Preserve2, IntFP2]
  rintro x r ht hix
  have eqx := unfold_sprodO x; simp at eqx
  set a := ↑↑↑↑Prod.fst x
  set b := ↑↑↑↑Prod.snd x
  rw [eqx] at ht hix ⊢; simp [D_sprod2]
  intro i; simp [bilinear_opt, denote, IntFP2]
  simp [IntFP2Vec, IntFP2, ExtFP2] at hix
  rw [forall_and_iff] at hix; rcases hix with ⟨hx, _⟩
  rw [<- FixAfter2Vec] at hx
  have hdx := FixAfter2Vec_D hx
  rw [D_sprod2] at hdx
  have hx' := FixAfter2Vec_sprod2.1 hdx
  rw [FixAfter2Vec_sprod2] at hx; rcases hx with ⟨ha, hb⟩
  rcases hx' with ⟨hda, hdb⟩
  set r' := fun i => max (r i) (z⁻¹ r i)
  have ha' := FixAfter2Vec_mono (b2:= r') ha (by intro i; simp [r'])
  have hb' := FixAfter2Vec_mono (b2:= r') hb (by intro i; simp [r'])
  have hzb := FixAfter2Vec_delay.1 hb
  have hzb' := FixAfter2Vec_mono (b2:= r') hzb (by intro i; simp [r'])
  have hj1 := FixAfter2Vec_sprod2.2 ⟨ha', hdb⟩
  have hj2 := FixAfter2Vec_sprod2.2 ⟨hda, hzb'⟩
  have hadd1 := FixAfter2Vec_lifting (f:= bn.f) hj1
  have hadd2 := FixAfter2Vec_lifting (f:= bn.f) hj2
  have haddi := FixAfter2Vec_sprod2.2 ⟨hadd1, hadd2⟩
  have haddo := FixAfter2Vec_lifting (f:= fun a => a.1+ a.2) haddi
  unfold r' at *
  specialize hdx i
  specialize hda i
  specialize hdb i
  specialize ha' i
  specialize hb' i
  specialize hzb i
  specialize hzb' i
  specialize hj1 i
  specialize hj2 i
  specialize hadd1 i
  specialize hadd2 i
  specialize haddi i
  specialize haddo i
  simp at *
  simp [ExtFP2, *, denote]
  constructor <;> apply I_IntFP2Vec <;> tauto

lemma Preserve2_id:
    cid ↝₂ (@Ckt.id 1 A) := by
  solve_preserve2_basic

lemma Preserve2_fst:
    c1st ↝₂ (@Ckt.fst 1 A B) := by
  solve_preserve2_basic

lemma Preserve2_snd:
    c2nd ↝₂ (@Ckt.snd 1 A B) := by
  solve_preserve2_basic

lemma Preserve2_add:
    cadd ↝₂ (@Ckt.add 1 A) := by
  solve_preserve2_basic

lemma Preserve2_sub:
    csub ↝₂ (@Ckt.sub 1 A) := by
  solve_preserve2_basic

lemma Preserve2_const k:
    (cconst k) ↝₂ (@Ckt.const 1 A B k) >>c cD := by
  simp [Preserve2, IntFP2Vec, IntFP2]
  intro x b ht hef i
  constructor
  · rw [LiftedScalar_ExtFP2 (hc:= by constructor)]
    apply FixAfter2Vec_D
    rw [<- ExtFP2Vec, ExtFP2Vec_iff] at hef
    tauto
  · apply D_IntFP2Vec
    intro i _ _
    simp [denote, liftO]

lemma Preserve2_delay:
    cz⁻¹ ↝₂ (@Ckt.delay 1 A) := by
  simp [Preserve2, IntFP2Vec, IntFP2]
  rintro x b ht hef i
  simp [ExtFP2, denote] at hef
  rw [forall_and_iff] at hef
  constructor
  · apply FixAfter2Vec_D
    tauto
  · simp [denote]
    rw [<- derivative_timeInvariant]
    apply FixAfter2Vec_D
    tauto

lemma Preserve2_lifted_delay:
    c↑z⁻¹ ↝₂ (@Ckt.lifted_delay A) := by
  simp [Preserve2, IntFP2Vec, IntFP2]
  intro x b ht hef i
  simp [ExtFP2, denote] at hef
  rw [forall_and_iff] at hef
  constructor
  · apply FixAfter2Vec_D
    tauto
  · simp [denote]
    have : ↑↑z⁻¹ (D x) = D (↑↑z⁻¹ x) := by
      funext t1 t2; simp [D, delay]
      rcases t1 <;> rcases t2 <;>simp
    rw [this]
    apply FixAfter2Vec_D
    tauto

lemma Preserve2_incr {c: Ckt A B 1}:
    c ↝₂ cΔ c := by
  simp [Preserve2]
  intro x n ht hi m
  have he := IntFP2Vec_impl_ExtFP2Vec hi
  apply ExtFP2Vec_iff.1 at he
  simp [cΔ, IntFP2]
  constructor; constructor
  · apply I_IntFP2Vec; tauto
  · apply IntFP2_mono; tauto; omega
  · simp [denote]
    apply D_IntFP2Vec; tauto

lemma Preserve2_seq {c1 c3: Ckt A B 1} {c2 c4: Ckt B C 1}
    (h1: c1 ↝₂ c3) (h2: c2 ↝₂ c4) (hr: (cΔ c1) ⊑ c3):
    (c1 >>c c2) ↝₂ (c3 >>c c4) := by
  simp [Preserve2]
  rintro x n ⟨ht1, ht2⟩ hi
  rw [IntFP2Vec_seq] at hi ⊢
  constructor
  · apply h1 <;> tauto
  specialize hr (D x) (Terminate_cΔ ht1)
  rcases hr with ⟨ht3, hd⟩
  simp [cΔ, denote] at hd
  rw [<- hd]
  apply h2 <;> tauto

lemma Preserve2_par {c1 c3: Ckt A B 1} {c2 c4: Ckt A C 1}
  (h1: c1 ↝₂ c3) (h2: c2 ↝₂ c4):
    (c1 &&c c2) ↝₂ (c3 &&c c4) := by
  simp [Preserve2]
  rintro x b ⟨ht1, ht2⟩ hi
  rw [IntFP2Vec_par] at hi ⊢
  constructor
  · apply h1 <;> tauto
  · apply h2 <;> tauto

-- The proof is almost identical to Preserve1_loop
lemma Preserve2_loop {c1 c2: Ckt (A ×ᵥ B) B 1}
  (h: c1 ↝₂ c2) (hr: (cΔ c1) ⊑ c2):
    (cloop c1) ↝₂ (cloop c2) := by
  intro x b ht
  simp [IntFP2Vec]; intro hi m; simp [IntFP2]
  have hrl := Refine_incr_loop hr
  have htd := Terminate_cΔ ht
  specialize hrl _ htd
  rcases hrl with ⟨_, hd⟩
  have : denote (cΔ (cloop c1)) (D x) = D (denote (cloop c1) x) := by
    simp [cΔ, denote]
  rw [this] at hd; rw [<- hd]
  have : sprod2 (D x, z⁻¹ (D (denote (cloop c1) x))) =
         D (sprod2 (x, z⁻¹ (denote (cloop c1) x))) := by
    rw [<- derivative_timeInvariant]; rw [D_sprod2]
  simp [Terminate] at ht
  rw [this]
  simp [IntFP2] at hi
  apply h <;> tauto

-- The proof is almost identical to Preserve1_lifted_loop
lemma Preserve2_lifted_loop {c1 c2: Ckt (A ×ᵥ B) B 1}
  (h: c1 ↝₂ c2) (hr: (cΔ c1) ⊑ c2):
    (cloop2 c1) ↝₂ (cloop2 c2) := by
  intro x b ht
  simp [IntFP2Vec]; intro hi m; simp [IntFP2]
  have hrl := Refine_incr_loop2 hr
  have htd := Terminate_cΔ ht
  specialize hrl _ htd
  rcases hrl with ⟨_, hd⟩
  have : denote (cΔ (cloop2 c1)) (D x) = D (denote (cloop2 c1) x) := by
    simp [cΔ, denote]
  rw [this] at hd; rw [<- hd]
  have : sprod2 (D x, ↑↑z⁻¹ (D (denote (cloop2 c1) x))) =
         D (sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c1) x))) := by
    rw [D_sprod2]
    rw [<- D_lifting_delay_comm]
  simp [Terminate] at ht
  rw [this]
  simp [IntFP2] at hi
  apply h <;> tauto

lemma Refine_incOpt_bracket {c1 c2: Ckt A B 1}
  (hr: (cΔ c1) ⊑ c2) (hp: c1 ↝₂ c2):
    cΔ (cbracket c1) ⊑ (cbracket c2) := by
  apply Refine_trans
  apply Refine_incr_bracket
  intro x; simp [Terminate]
  intro ht b hif hz
  specialize hr _ ht
  rcases hr with ⟨htc, hd⟩
  simp [htc]
  simp [denote] at hd ⊢
  rw [hd]; simp
  use (fun i => max (b i) (z⁻¹ b i))
  constructor
  · rw [<- integral_derivative (s:= ↑↑δ0 x)]
    apply hp
    · simp [cΔ, Terminate] at ht; assumption
    · simp [IntFP2Vec, cΔ, IntFP2] at hif
      intro i; specialize hif i; tauto
  · rw [<- hd]
    apply ZeroAfterVec_mono
    tauto; omega

lemma Preserve1_bracket {c1 c2: Ckt A B 1} (hp: c1 ↝₁ c2):
    (cbracket c1) ↝₁ (cbracket c2) := by
  simp [Preserve1, IntFP1]
  rintro x n ht hi
  rw [<- D_lifting_delta_comm]
  apply hp
  · simp [Terminate] at ht; tauto
  · tauto

end Preserve

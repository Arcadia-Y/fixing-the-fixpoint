import DBSP.Practical.ConvEq
open CktBasic

section Preserve
variable {A B C: VType} {ns: Bool}
-- These definitions are almost merely for incremnetalization proofs

-- This asserts that the `IntFP1` of `c1` is preserved when
-- we transform it into `c2` (which is supposed to be its incremental version)
def Preserve1 {ns A B} (c1 c2: Ckt A B ns) : Prop :=
  ∀ x n, ExtConv c1 x -> IntFP1 c1 x n -> IntFP1 c2 (D x) (n+1)
infix:30 " ↝₁ " => Preserve1
-- This asserts that the `IntFP2` of `c1` is preserved when
-- we transform it into `c2` (which is supposed to be its incremental version)
def Preserve2 {A B} (c1 c2: Ckt A B 1) : Prop :=
    ∀ x b, ExtConv c1 x -> IntFP2Vec c1 x b ->
      IntFP2Vec c2 (D x) (fun i => max (b i) (z⁻¹ b i))
infix:30 " ↝₂ " => Preserve2

-- D-shifted termination preservation relation used in incrementalization proofs.
def PreserveIC (c1 c2: Ckt A B ns): Prop :=
  ∀ x, IntConv c1 x -> IntConv c2 (D x)

infix:30 " ↝c " => PreserveIC

lemma PreserveIC_incr (c: Ckt A B ns): c ↝c cΔ c := by
  intro x hx
  exact IntConv_cΔ hx

lemma Sequiv_to_PreserveIC {c1 c2: Ckt A B ns}:
  cΔ c1 ≃ c2 -> c1 ↝c c2 := by
  intro h
  rcases h with ⟨_, ht, _⟩
  intro x hx
  have hxΔ : IntConv (cΔ c1) (D x) := IntConv_cΔ hx
  simpa [ht] using hxΔ

lemma PreserveIC_par
  {c1 c2: Ckt A B ns} {d1 d2: Ckt A C ns}
  (hc: c1 ↝c c2) (hd: d1 ↝c d2):
  (c1 &&c d1) ↝c (c2 &&c d2) := by
  intro x hx
  simp [IntConv] at hx ⊢
  rcases hx with ⟨hcx, hdx⟩
  exact ⟨hc x hcx, hd x hdx⟩

lemma PreserveIC_seq
  {c1 c2: Ckt A B ns} {d1 d2: Ckt B C ns}
  (hc: c1 ↝c c2) (hd: d1 ↝c d2) (heq: cΔ c1 ≋ c2):
  (c1 >>c d1) ↝c (c2 >>c d2) := by
  intro x hx
  simp [IntConv] at hx ⊢
  rcases hx with ⟨htc1, htd1⟩
  have htc2 : IntConv c2 (D x) := hc x htc1
  have hΔ : IntConv (cΔ c1) (D x) := IntConv_cΔ htc1
  have hconvΔ : ExtConv (cΔ c1) (D x) := IntConv_impl_ExtConv hΔ
  have hden : denote c2 (D x) = D (denote c1 x) := by
    calc
      denote c2 (D x) = denote (cΔ c1) (D x) := (heq.denote (D x) hconvΔ).symm
      _ = D (denote c1 x) := by simp [cΔ, denote, derivative_integral]
  have htd2_at_c1 : IntConv d2 (D (denote c1 x)) := hd (denote c1 x) htd1
  have htd2 : IntConv d2 (denote c2 (D x)) := by
    simpa [hden] using htd2_at_c1
  exact ⟨htc2, htd2⟩

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
  (h1: c1 ↝₁ c3) (h2: c2 ↝₁ c4) (hr: (cΔ c1) ≋ c3):
    (c1 >>c c2) ↝₁ (c3 >>c c4) := by
  simp [Preserve1, IntFP1]
  rintro x n ⟨ht1, ht2⟩ hi1 hi2
  constructor
  · apply h1 <;> tauto
  have hd : denote c3 (D x) = D (denote c1 x) := by
    calc
      denote c3 (D x) = denote (cΔ c1) (D x) :=
        (hr.denote (D x) (ExtConv_cΔ_of_ExtConv ht1)).symm
      _ = D (denote c1 x) := by simp [cΔ, denote, derivative_integral]
  rw [hd]
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
  (h: c1 ↝₁ c2) (hr: cΔ (cloop c1) ≋ (cloop c2)):
    (cloop c1) ↝₁ (cloop c2) := by
  intro x n ht
  simp [IntFP1]; intro hi
  have hd : denote (cloop c2) (D x) = D (denote (cloop c1) x) := by
    calc
      denote (cloop c2) (D x) = denote (cΔ (cloop c1)) (D x) :=
        (hr.denote (D x) (ExtConv_cΔ_of_ExtConv ht)).symm
      _ = D (denote (cloop c1) x) := by simp [cΔ, denote, derivative_integral]
  rw [hd]
  have : sprodO ns (D x, z⁻¹ (D (denote (cloop c1) x))) =
         D (sprodO ns (x, z⁻¹ (denote (cloop c1) x))) := by
    rcases ns <;> rw [<- derivative_timeInvariant] <;>
    rw [D_sprodO]
  rw [this]
  apply h <;> tauto

-- The proof is almost identical to the above
lemma Preserve1_lifted_loop {c1 c2: Ckt (A ×ᵥ B) B 1}
  (h: c1 ↝₁ c2) (hr: cΔ (cloop2 c1) ≋ (cloop2 c2)):
    (cloop2 c1) ↝₁ (cloop2 c2) := by
  intro x n ht
  simp [IntFP1]; intro hi
  have hd : denote (cloop2 c2) (D x) = D (denote (cloop2 c1) x) := by
    calc
      denote (cloop2 c2) (D x) = denote (cΔ (cloop2 c1)) (D x) :=
        (hr.denote (D x) (ExtConv_cΔ_of_ExtConv ht)).symm
      _ = D (denote (cloop2 c1) x) := by simp [cΔ, denote, derivative_integral]
  rw [hd]
  have : sprod2 (D x, ↑↑z⁻¹ (D (denote (cloop2 c1) x))) =
         D (sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c1) x))) := by
    rw [D_sprod2 (a := VType_interp A) (b := VType_interp B)]
    rw [← D_lifting_delay_comm]
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
  (h1: c1 ↝₂ c3) (h2: c2 ↝₂ c4) (hr: (cΔ c1) ≋ c3):
    (c1 >>c c2) ↝₂ (c3 >>c c4) := by
  simp [Preserve2]
  rintro x n ⟨ht1, ht2⟩ hi
  rw [IntFP2Vec_seq] at hi ⊢
  constructor
  · apply h1 <;> tauto
  have hd : denote c3 (D x) = D (denote c1 x) := by
    calc
      denote c3 (D x) = denote (cΔ c1) (D x) :=
        (hr.denote (D x) (ExtConv_cΔ_of_ExtConv ht1)).symm
      _ = D (denote c1 x) := by simp [cΔ, denote, derivative_integral]
  rw [hd]
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
  (h: c1 ↝₂ c2) (hr: cΔ (cloop c1) ≋ (cloop c2)):
    (cloop c1) ↝₂ (cloop c2) := by
  intro x b ht
  simp [IntFP2Vec]; intro hi m; simp [IntFP2]
  have hd : denote (cloop c2) (D x) = D (denote (cloop c1) x) := by
    calc
      denote (cloop c2) (D x) = denote (cΔ (cloop c1)) (D x) :=
        (hr.denote (D x) (ExtConv_cΔ_of_ExtConv ht)).symm
      _ = D (denote (cloop c1) x) := by simp [cΔ, denote, derivative_integral]
  rw [hd]
  have : sprod2 (D x, z⁻¹ (D (denote (cloop c1) x))) =
         D (sprod2 (x, z⁻¹ (denote (cloop c1) x))) := by
    rw [<- derivative_timeInvariant]; rw [D_sprod2]
  rw [this]
  simp [IntFP2] at hi
  apply h <;> tauto

-- The proof is almost identical to Preserve1_lifted_loop
lemma Preserve2_lifted_loop {c1 c2: Ckt (A ×ᵥ B) B 1}
  (h: c1 ↝₂ c2) (hr: cΔ (cloop2 c1) ≋ (cloop2 c2)):
    (cloop2 c1) ↝₂ (cloop2 c2) := by
  intro x b ht
  simp [IntFP2Vec]; intro hi m; simp [IntFP2]
  have hd : denote (cloop2 c2) (D x) = D (denote (cloop2 c1) x) := by
    calc
      denote (cloop2 c2) (D x) = denote (cΔ (cloop2 c1)) (D x) :=
        (hr.denote (D x) (ExtConv_cΔ_of_ExtConv ht)).symm
      _ = D (denote (cloop2 c1) x) := by simp [cΔ, denote, derivative_integral]
  rw [hd]
  have : sprod2 (D x, ↑↑z⁻¹ (D (denote (cloop2 c1) x))) =
         D (sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c1) x))) := by
    rw [D_sprod2]
    rw [<- D_lifting_delay_comm]
  rw [this]
  simp [IntFP2] at hi
  apply h <;> tauto

lemma Preserve1_bracket {c1 c2: Ckt A B 1} (hp: c1 ↝₁ c2):
    (cbracket c1) ↝₁ (cbracket c2) := by
  simp [Preserve1, IntFP1]
  rintro x n ht hi
  rw [<- D_lifting_delta_comm]
  apply hp
  · simp [ExtConv] at ht; tauto
  · tauto

lemma ConvEq_incOpt_bracket {c1 c2: Ckt A B 1}
  (hr: (cΔ c1) ≋ c2) (hp: c1 ↝₂ c2):
    cΔ (cbracket c1) ≋ (cbracket c2) := by
  have _ := hp
  apply ConvEq_trans
  apply ConvEq_incr_bracket
  refine ⟨?_, ?_⟩
  · funext x
    apply propext
    constructor
    · intro hx
      simp [ExtConv] at hx ⊢
      rcases hx with ⟨hcx, hb⟩
      have hcy : ExtConv c2 (↑↑δ0 x) := by simpa [hr.conv] using hcx
      have hd : denote (cΔ c1) (↑↑δ0 x) = denote c2 (↑↑δ0 x) := hr.denote _ hcx
      rcases hb with ⟨b, hz⟩
      have hz' : ZeroAfterVec (denote c2 (↑↑δ0 x)) b := by
        rw [← hd]
        exact hz
      refine ⟨hcy, ⟨b, ?_⟩⟩
      exact hz'
    · intro hy
      simp [ExtConv] at hy ⊢
      rcases hy with ⟨hcy, hb⟩
      have hcx : ExtConv (cΔ c1) (↑↑δ0 x) := by simpa [hr.conv] using hcy
      have hd : denote c2 (↑↑δ0 x) = denote (cΔ c1) (↑↑δ0 x) := (hr.denote _ hcx).symm
      rcases hb with ⟨b, hz⟩
      have hz' : ZeroAfterVec (denote (cΔ c1) (↑↑δ0 x)) b := by
        rw [← hd]
        exact hz
      refine ⟨hcx, ⟨b, ?_⟩⟩
      exact hz'
  · intro x hx
    simp [ExtConv] at hx
    rcases hx with ⟨hcx, _⟩
    have hd : denote (cΔ c1) (↑↑δ0 x) = denote c2 (↑↑δ0 x) := hr.denote _ hcx
    simpa [denote] using congrArg (fun s => (↑↑∫0) s) hd

lemma PreserveIC_loop
  {c1 c2: Ckt (A ×ᵥ B) B ns}
  (hr: c1 ↝c c2)
  (hc: cΔ (cloop c1) ≋ (cloop c2)):
  cloop c1 ↝c cloop c2 := by
  intro x hx
  set inp := sprodO ns (x, z⁻¹ (denote (cloop c1) x))
  have hinner : IntConv c1 inp := by
    simpa [IntConv, inp] using hx
  have href : IntConv c2 (D inp) := hr inp hinner
  have hconvΔ : ExtConv (cΔ (cloop c1)) (D x) := by
    exact IntConv_impl_ExtConv (IntConv_cΔ hx)
  have hden : denote (cloop c2) (D x) = D (denote (cloop c1) x) := by
    calc
      denote (cloop c2) (D x) = denote (cΔ (cloop c1)) (D x) :=
        (hc.denote (D x) hconvΔ).symm
      _ = D (denote (cloop c1) x) := by simp [cΔ, denote, derivative_integral]
  have hDinp : D inp = sprodO ns (D x, z⁻¹ (denote (cloop c2) (D x))) := by
    calc
      D inp = sprodO ns (D x, z⁻¹ (D (denote (cloop c1) x))) := by
        have htmp : sprodO ns (D x, z⁻¹ (D (denote (cloop c1) x))) = D inp := by
          unfold inp
          rcases ns <;>
          rw [← derivative_timeInvariant] <;>
          rw [D_sprodO]
        exact htmp.symm
      _ = sprodO ns (D x, z⁻¹ (denote (cloop c2) (D x))) := by
        simp [hden]
  simpa [IntConv, hDinp] using href

lemma PreserveIC_lifted_loop
  {c1 c2: Ckt (A ×ᵥ B) B 1}
  (hr: c1 ↝c c2)
  (hc: cΔ (cloop2 c1) ≋ (cloop2 c2)):
  cloop2 c1 ↝c cloop2 c2 := by
  intro x hx
  set inp := sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c1) x))
  have hinner : IntConv c1 inp := by
    simpa [IntConv, inp] using hx
  have href : IntConv c2 (D inp) := hr inp hinner
  have hconvΔ : ExtConv (cΔ (cloop2 c1)) (D x) := by
    exact IntConv_impl_ExtConv (IntConv_cΔ hx)
  have hden : denote (cloop2 c2) (D x) = D (denote (cloop2 c1) x) := by
    calc
      denote (cloop2 c2) (D x) = denote (cΔ (cloop2 c1)) (D x) :=
        (hc.denote (D x) hconvΔ).symm
      _ = D (denote (cloop2 c1) x) := by simp [cΔ, denote, derivative_integral]
  have hDinp : D inp = sprod2 (D x, ↑↑z⁻¹ (denote (cloop2 c2) (D x))) := by
    calc
      D inp = sprod2 (D x, ↑↑z⁻¹ (D (denote (cloop2 c1) x))) := by
        have htmp : sprod2 (D x, ↑↑z⁻¹ (D (denote (cloop2 c1) x))) = D inp := by
          unfold inp
          rw [D_sprod2]
          rw [← D_lifting_delay_comm]
        exact htmp.symm
      _ = sprod2 (D x, ↑↑z⁻¹ (denote (cloop2 c2) (D x))) := by
        simp [hden]
  simpa [IntConv, hDinp] using href

lemma PreserveIC_bracket
  {c1 c2: Ckt A B 1}
  (hr: c1 ↝c c2)
  (hc: cΔ c1 ≋ c2)
  (hp: c1 ↝₂ c2):
  cbracket c1 ↝c cbracket c2 := by
  intro x hx
  simp [IntConv] at hx ⊢
  rcases hx with ⟨htc, ⟨b, hif, hz⟩⟩
  have htc2 : IntConv c2 (D (↑↑δ0 x)) := hr (↑↑δ0 x) htc
  have hconv : ExtConv c1 (↑↑δ0 x) := IntConv_impl_ExtConv htc
  have hif2 : IntFP2Vec c2 (D (↑↑δ0 x)) (fun i => max (b i) (z⁻¹ b i)) :=
    hp (↑↑δ0 x) b hconv hif
  have hconvΔ : ExtConv (cΔ c1) (D (↑↑δ0 x)) := ExtConv_cΔ_of_ExtConv hconv
  have hden : denote c2 (D (↑↑δ0 x)) = D (denote c1 (↑↑δ0 x)) := by
    calc
      denote c2 (D (↑↑δ0 x)) = denote (cΔ c1) (D (↑↑δ0 x)) :=
        (hc.denote (D (↑↑δ0 x)) hconvΔ).symm
      _ = D (denote c1 (↑↑δ0 x)) := by simp [cΔ, denote, derivative_integral]
  have hz2 : ZeroAfterVec (denote c2 (D (↑↑δ0 x))) (fun i => max (b i) (z⁻¹ b i)) := by
    rw [hden]
    exact ZeroAfterVec_D hz
  have hdelta : D (↑↑δ0 x) = ↑↑δ0 (D x) := by
    rw [D_lifting_delta_comm]
  refine ⟨?_, ?_⟩
  · simpa [hdelta] using htc2
  · refine ⟨fun i => max (b i) (z⁻¹ b i), ?_⟩
    constructor
    · simpa [hdelta] using hif2
    · simpa [hdelta] using hz2

end Preserve

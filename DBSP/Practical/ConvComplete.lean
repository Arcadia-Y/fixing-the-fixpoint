import DBSP.Convergence.Spec
import DBSP.Circuits.LiftedScalar
import DBSP.Practical.RegularCkt
import DBSP.Practical.PushLifting
open CktBasic

-- Fixpoint-complete (FP-complete) circuits are those good circuits whose ExtFP implies IntFP for externally converging input. This means for them ExtFP coincides with IntFP.
structure FPComplete {ns} {A B: VType} (c: Ckt A B ns) where
  FP1 : ∀ x n, ExtConv c x -> ExtFP1 c x n -> ∃ n', IntFP1 c x n'
  FP2: match ns, c with
       | 0, _ => True
       | 1, c => ∀ x b, ExtConv c x -> ExtFP2Vec c x b -> ∃ b', IntFP2Vec c x b'

-- IntConv-complete circuits are those good circuits whose IntConv implies ExtConv. This means for them ExtConv coincides with IntConv, so we can safely use them without worrying about the FPD problem.
-- Its relation with `FPComplete` is just like that between `IntConv` and `IntFP`.
def ConvComplete {ns} {A B: VType} (c: Ckt A B ns): Prop :=
  ∀ x, ExtConv c x → IntConv c x

theorem ConvComplete_IntConv_iff_ExtConv {A B ns}
  {c: Ckt A B ns} (h: ConvComplete c):
    IntConv c = ExtConv c := by
  funext x; simp; constructor
  apply IntConv_impl_ExtConv
  apply h

-- We show `FPComplete` and `ConvComplete`'s algebraic rules

-- `FPComplete` is closed under all cicrcuit construct except `bracket` and `seq`

-- `IsNode c` means c is an individual node
inductive IsNode : ∀ {a b ns}, Ckt a b ns -> Prop
  | node1 {ns A B} [BaseType A] [BaseType B] (f: UnaryNode A B):
    IsNode (Ckt.node1 (ns:=ns) f)
  | node2 {ns A B C} [BaseType A] [BaseType B] [BaseType C] (f: BinaryNode A B C):
    IsNode (Ckt.node2 (ns:=ns) f)
  | const {ns a b} (x: VType_interp b):
    IsNode (Ckt.const (ns:=ns) (a:=a) x)
  | id {ns a}:
    IsNode (Ckt.id (ns:=ns) (a:=a))
  | fst {ns a b}:
    IsNode (Ckt.fst (ns:=ns) (a:=a) (b:=b))
  | snd {ns a b}:
    IsNode (Ckt.snd (ns:=ns) (a:=a) (b:=b))
  | add {ns a}:
    IsNode (Ckt.add (ns:=ns) (a:=a))
  | sub {ns a}:
    IsNode (Ckt.sub (ns:=ns) (a:=a))
  | delay {ns a}:
    IsNode (Ckt.delay (ns:=ns) (a:=a))
  | lifted_delay {a}:
    IsNode (Ckt.lifted_delay (a:=a))

-- All nodes are FPComplete
theorem FPComplete_IsNode {A B ns} {c: Ckt A B ns} (hc: IsNode c):
    FPComplete c := by
  cases hc
  all_goals
    constructor
    case FP1 =>
      intro _ _ _
      simp [IntFP1]
      tauto
    case FP2 =>
      (try rcases ns <;> simp)
      intro x b _ h
      refine ⟨b, ?_⟩
      simpa [IntFP2Vec, IntFP2] using h

-- FPComplete circuits are closed under `par`
theorem FPComplete_par {ns} {A B C: VType}
  {c1: Ckt A B ns} {c2: Ckt A C ns}
  (h1: FPComplete c1) (h2: FPComplete c2):
    FPComplete (c1 &&c c2) := by
  constructor
  case FP1 =>
    intro x n hconv h
    simp [ExtConv] at hconv
    simp [IntFP1]
    simp [ExtFP1, denote] at h
    rw [FixAfter1_sprodO] at h
    have hc1 := h1.FP1 x n hconv.1 (by tauto)
    have hc2 := h2.FP1 x n hconv.2 (by tauto)
    rcases hc1 with ⟨n1, hc1⟩
    rcases hc2 with ⟨n2, hc2⟩
    use (max n1 n2)
    constructor <;> apply IntFP1_mono <;> try tauto
    all_goals omega
  case FP2 =>
    rcases ns <;> simp
    intro x b hconv h
    simp [ExtConv] at hconv
    simp [IntFP2Vec, IntFP2]
    simp [ExtFP2Vec, ExtFP2, denote] at h
    have h' : ∀ i, FixAfter2 (denote c1 x) i (b i) ∧ FixAfter2 (denote c2 x) i (b i) := by
      intro i; specialize h i
      rw [FixAfter2_sprod2_iff] at h
      tauto
    have h1 := h1.FP2; simp at h1
    specialize h1 x b hconv.1 (by
      simp [ExtFP2Vec]; intro i; specialize h' i; specialize h i; tauto)
    have h2 := h2.FP2; simp at h2
    specialize h2 x b hconv.2 (by
      simp [ExtFP2Vec]; intro i; specialize h' i; specialize h i; tauto)
    rcases h1 with ⟨b1, hc1⟩
    rcases h2 with ⟨b2, hc2⟩
    use (fun i => max (b1 i) (b2 i))
    intro i; constructor <;> apply IntFP2_mono <;> try tauto
    all_goals simp

-- FPComplete circuits are closed under `loop`
theorem FPComplete_loop {ns} {A B: VType}
  {c: Ckt (A ×ᵥ B) B ns} (h: FPComplete c):
    FPComplete (cloop c) := by
  constructor
  case FP1 =>
    intro x n hconv hx
    simp [ExtConv] at hconv
    have hx' : ExtFP1 c (sprodO ns (x, z⁻¹ (denote (cloop c) x))) (n+1) := by
      exact ExtFP1_loop c x n hx
    have hc := h.FP1 (sprodO ns (x, z⁻¹ (denote (cloop c) x))) (n+1) hconv hx'
    rcases hc with ⟨n', hn'⟩
    refine ⟨n', ?_⟩
    simpa [IntFP1]
  case FP2 =>
    rcases ns <;> simp
    intro x b hconv hb
    simp [ExtConv] at hconv
    let y : SOVType 1 (A ×ᵥ B) := sprod2 (x, z⁻¹ (denote (cloop c) x))
    let b' : stream ℕ := fun i => max (b i) (z⁻¹ b i)
    have hfixx : FixAfter2Vec x b := by
      intro i
      exact (hb i).1
    have hfixo : FixAfter2Vec (denote (cloop c) x) b := by
      intro i
      exact (hb i).2
    have hfixx' : FixAfter2Vec x b' := by
      apply FixAfter2Vec_mono hfixx
      intro i; simp [b']
    have hfixd : FixAfter2Vec (z⁻¹ (denote (cloop c) x)) (z⁻¹ b) := by
      apply FixAfter2Vec_delay.1
      exact hfixo
    have hfixd' : FixAfter2Vec (z⁻¹ (denote (cloop c) x)) b' := by
      apply FixAfter2Vec_mono hfixd
      intro i
      rcases i with _ | i
      · simp [b']
      · simp [b']
    have hy_in : FixAfter2Vec y b' := by
      rw [FixAfter2Vec_sprod2]
      constructor <;> assumption
    have hy_out : FixAfter2Vec (denote c y) b' := by
      have hfixo' : FixAfter2Vec (denote (cloop c) x) b' := by
        apply FixAfter2Vec_mono hfixo
        intro i; simp [b']
      have hloop : denote c y = denote (cloop c) x := by
        unfold y
        simpa using (loop_unfold (c:=c) (x:=x)).symm
      rw [hloop]
      exact hfixo'
    have hy : ExtFP2Vec c y b' := by
      intro i
      exact ⟨hy_in i, hy_out i⟩
    have hc := h.FP2
    simp at hc
    specialize hc y b' hconv hy
    rcases hc with ⟨b2, hb2⟩
    refine ⟨b2, ?_⟩
    intro i
    simpa [IntFP2, y] using hb2 i

-- FPComplete circuits are closed under `lifting`
theorem FPComplete_lifting {A B: VType}
  {c: Ckt A B 0} (h: FPComplete c):
    FPComplete (c↑ c) := by
  constructor
  case FP1 =>
    intro x n _ hx
    refine ⟨n, ?_⟩
    simpa [IntFP1] using hx
  case FP2 =>
    intro x b hconv hb
    simp [ExtConv] at hconv
    have hrow : ∀ i, ∃ n', IntFP1 c (x i) n' := by
      intro i
      have hei : ExtFP1 c (x i) (b i) := by
        simpa [ExtFP2, FixAfter2, ExtFP1, denote] using (hb i)
      exact h.FP1 (x i) (b i) (hconv i) hei
    choose b' hb' using hrow
    refine ⟨b', ?_⟩
    intro i
    simpa [IntFP2] using hb' i

-- FPComplete circuits are closed under `lifted_loop`
theorem FPComplete_lifted_loop {A B: VType}
  {c: Ckt (A ×ᵥ B) B 1} (h: FPComplete c):
    FPComplete (cloop2 c) := by
  constructor
  case FP1 =>
    intro x n hconv hx
    simp [ExtConv] at hconv
    let y : SOVType 1 (A ×ᵥ B) := sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c) x))
    have hx' : ExtFP1 c y n := by
      simp [ExtFP1] at hx ⊢
      rcases hx with ⟨hx1, hx2⟩
      constructor
      · rw [FixAfter1_sprod2]
        constructor
        · exact hx1
        · intro m hm
          specialize hx2 m hm
          simpa [lifting] using congrArg (fun t => z⁻¹ t) hx2
      · have hloop : denote c y = denote (cloop2 c) x := by
          unfold y
          simpa using (lifted_loop_unfold (c:=c) (x:=x)).symm
        rw [hloop]
        exact hx2
    rcases h.FP1 y n hconv hx' with ⟨n', hn'⟩
    exact ⟨n', by simpa [IntFP1] using hn'⟩
  case FP2 =>
    intro x b hconv hb
    simp [ExtConv] at hconv
    let y : SOVType 1 (A ×ᵥ B) := sprod2 (x, ↑↑z⁻¹ (denote (cloop2 c) x))
    have hy : ExtFP2Vec c y (fun i => b i + 1) := by
      intro i
      have h0 : ExtFP2 (cloop2 c) x i (b i) := hb i
      have h1 : ExtFP2 (cloop2 c) x i (b i + 1) := by
        exact ExtFP2_mono h0 (by omega)
      have hxfix : FixAfter2 x i (b i + 1) := h1.1
      have hloop0 : FixAfter2 (denote (cloop2 c) x) i (b i) := h0.2
      have hloop1 : FixAfter2 (denote (cloop2 c) x) i (b i + 1) := h1.2
      constructor
      · simp [ExtFP2]
        rw [FixAfter2_sprod2_iff]
        constructor
        · exact hxfix
        · simp [FixAfter2] at hloop0 ⊢
          rw [FixAfter1_delay_succ]
          exact hloop0
      · simp [ExtFP2]
        have hloop : denote c y = denote (cloop2 c) x := by
          unfold y
          simpa using (lifted_loop_unfold (c:=c) (x:=x)).symm
        rw [hloop]
        exact hloop1
    have hc := h.FP2
    simp at hc
    rcases hc y (fun i => b i + 1) hconv hy with ⟨b', hb'⟩
    exact ⟨b', by intro i; simpa [IntFP2, y] using hb' i⟩

lemma FPComplete_cI {A ns}:
    FPComplete (@cI A ns) := by
  apply FPComplete_loop
  apply FPComplete_IsNode
  exact IsNode.add

lemma FPComplete_cD {A ns}:
    FPComplete (@cD A ns) := by
  constructor
  case FP1 =>
    intro x n _ hx
    refine ⟨n + 1, ?_⟩
    have hz : ZeroAfter (D x) (n + 1) := by
      intro m hm
      simp [D, delay]
      split_ifs with h0
      · omega
      · have hxm : x m = x n := hx.1 m (by omega)
        have hxm1 : x (m - 1) = x n := hx.1 (m - 1) (by omega)
        rw [hxm, hxm1]
        rcases ns <;> simp
    apply D_IntFP1
    exact hz
  case FP2 =>
    rcases ns <;> simp
    intro x b hx
    have hfix : FixAfter2Vec x b := by
      intro i
      exact (hx i).1
    refine ⟨fun i => max (b i) (z⁻¹ b i), ?_⟩
    exact D_IntFP2Vec hfix

-- FPComplete circuits are NOT closed under `seq`
namespace FPComplete_not_closed_seq
private abbrev Z := Int

private instance : BaseType Z where
  has_group := inferInstance
  size := fun _ => 0
  add_cost := fun _ => 0
  sub_cost := fun _ => 0

private def ones : SOVType 0 [Z]v := fun _ => (1 : Z)

private lemma not_ZeroAfter_ones (n: ℕ):
    ¬ ZeroAfter ones (n+1) := by
  intro hz
  have h := hz (n+1) (by omega)
  simp [ones] at h

private lemma not_FixAfter1_I_ones (n: ℕ):
    ¬ FixAfter1 (I ones) n := by
  intro h
  have hz : ZeroAfter ones (n+1) := by
    rw [ZeroAfter_succ_I_FixAfter1]
    exact h
  exact not_ZeroAfter_ones n hz

theorem seq_counterexample :
    FPComplete (@cI [Z]v 0) ∧
    FPComplete (@cD [Z]v 0) ∧
    ¬ FPComplete ((@cI [Z]v 0) >>c (@cD [Z]v 0)) := by
  constructor
  · exact FPComplete_cI
  constructor
  · exact FPComplete_cD
  · intro hseq
    let x : SOVType 0 [Z]v := ones
    have hfixx : FixAfter1 x 0 := by
      intro m hm
      rfl
    have hden : denote ((@cI [Z]v 0) >>c (@cD [Z]v 0)) x = x := by
      simp [denote, cI_denote, cD_denote, integral_derivative]
    have hext : ExtFP1 ((@cI [Z]v 0) >>c (@cD [Z]v 0)) x 0 := by
      constructor
      · exact hfixx
      · rw [hden]
        exact hfixx
    have hconv : ExtConv ((@cI [Z]v 0) >>c (@cD [Z]v 0)) x := by
      simp [ExtConv]
    rcases hseq.FP1 x 0 hconv hext with ⟨n, hint⟩
    have hseq' := hint
    simp [IntFP1] at hseq'
    rcases hseq' with ⟨_, hd⟩
    have hExtD : ExtFP1 (@cD [Z]v 0) (denote (@cI [Z]v 0) x) n := by
      exact IntFP1_impl_ExtFP1 (@cD [Z]v 0) (denote (@cI [Z]v 0) x) n hd
    have hFixI : FixAfter1 (I x) n := by
      simpa [denote, cI_denote] using hExtD.1
    have : ¬ FixAfter1 (I ones) n := not_FixAfter1_I_ones n
    apply this
    simpa [x] using hFixI

end FPComplete_not_closed_seq

macro "solve_good" : tactic => `(tactic| (
  intro x hc
  simp [ExtConv] at hc
  simp [IntConv]; tauto
))

-- IntConv-complete circuits are closed under all circuit constructs except `bracket`
theorem ConvComplete_IsNode {A B ns} {c: Ckt A B ns} (hc: IsNode c):
    ConvComplete c := by
  cases hc
  all_goals simp [ConvComplete, IntConv]

theorem ConvComplete_seq {ns} {A B C: VType}
  {c1: Ckt A B ns} {c2: Ckt B C ns}
  (h1: ConvComplete c1) (h2: ConvComplete c2):
    ConvComplete (c1 >>c c2) := by
  solve_good

theorem ConvComplete_par {ns} {A B C: VType}
  {c1: Ckt A B ns} {c2: Ckt A C ns}
  (h1: ConvComplete c1) (h2: ConvComplete c2):
    ConvComplete (c1 &&c c2) := by
  solve_good

theorem ConvComplete_loop {ns} {A B: VType}
  {c: Ckt (A ×ᵥ B) B ns} (h: ConvComplete c):
    ConvComplete (cloop c) ↔ ConvComplete c := by
  constructor
  · intro _
    tauto
  · intro _
    solve_good

theorem ConvComplete_lifting {A B: VType}
  {c: Ckt A B 0} (h: ConvComplete c):
    ConvComplete (c↑ c) ↔ ConvComplete c := by
  constructor
  · intro _
    tauto
  · intro _
    solve_good

theorem ConvComplete_lifted_loop {A B: VType}
  {c: Ckt (A ×ᵥ B) B 1} (h: ConvComplete c):
    ConvComplete (cloop2 c) ↔ ConvComplete c := by
  constructor
  · intro _
    tauto
  · intro _
    solve_good

-- For `bracket`, we need `c` to be not only `ConvComplete` but also `FPComplete`
theorem ConvComplete_bracket {A B: VType} {c: Ckt A B 1}
  (hcc: ConvComplete c) (hfc: FPComplete c):
    ConvComplete (cbracket c) := by
  intro x hx
  simp [ExtConv] at hx
  rcases hx with ⟨hext, ⟨b0, hz0⟩⟩
  have hinner : IntConv c (↑↑δ0 x) := hcc (↑↑δ0 x) hext
  have hExt2 : ExtFP2Vec c (↑↑δ0 x) (fun i => b0 i + 1) := by
    intro i
    apply delta_ZeroAfter_impl_ExtFP2
    exact hz0 i
  have hfp2 := hfc.FP2
  simp at hfp2
  rcases hfp2 (↑↑δ0 x) (fun i => b0 i + 1) hext hExt2 with ⟨b1, hInt1⟩
  let b : stream ℕ := fun i => max (b1 i) (b0 i + 1)
  have hInt : IntFP2Vec c (↑↑δ0 x) b := by
    apply IntFP2Vec_mono (b1:=b1)
    · intro i; simp [b]
    · exact hInt1
  have hz1 : ZeroAfterVec (denote c (↑↑δ0 x)) (fun i => b0 i + 1) := by
    apply ZeroAfterVec_mono hz0
    intro i; omega
  have hz : ZeroAfterVec (denote c (↑↑δ0 x)) b := by
    apply ZeroAfterVec_mono hz1
    intro i; simp [b]
  simp [IntConv]
  exact ⟨hinner, ⟨b, hInt, hz⟩⟩

  -- Every bracketed sub-circuit has FPComplete inner circuit.
  def BracketSubFPComplete {ns} {A B: VType} (c: Ckt A B ns): Prop :=
    match c with
    | Ckt.bracket c0 => FPComplete c0 ∧ BracketSubFPComplete c0
    | Ckt.seq c1 c2 => BracketSubFPComplete c1 ∧ BracketSubFPComplete c2
    | Ckt.par c1 c2 => BracketSubFPComplete c1 ∧ BracketSubFPComplete c2
    | Ckt.lifting c0 => BracketSubFPComplete c0
    | Ckt.loop c0 => BracketSubFPComplete c0
    | Ckt.lifted_loop c0 => BracketSubFPComplete c0
    | _ => True

  -- If every sub-circuit of form `cbracket c0` has FPComplete inner circuit, then `c` is ConvComplete.
  theorem BracketSubFPComplete_impl_ConvComplete {ns} {A B: VType}
    (c: Ckt A B ns) (hfp: BracketSubFPComplete c):
    ConvComplete c := by
    induction c with
    | node1 =>
      apply ConvComplete_IsNode
      exact IsNode.node1 _
    | node2 =>
      apply ConvComplete_IsNode
      exact IsNode.node2 _
    | const =>
      apply ConvComplete_IsNode
      exact IsNode.const _
    | id =>
      apply ConvComplete_IsNode
      exact IsNode.id
    | fst =>
      apply ConvComplete_IsNode
      exact IsNode.fst
    | snd =>
      apply ConvComplete_IsNode
      exact IsNode.snd
    | add =>
      apply ConvComplete_IsNode
      exact IsNode.add
    | sub =>
      apply ConvComplete_IsNode
      exact IsNode.sub
    | delay =>
      apply ConvComplete_IsNode
      exact IsNode.delay
    | lifted_delay =>
      apply ConvComplete_IsNode
      exact IsNode.lifted_delay
    | seq c1 c2 ih1 ih2 =>
      rcases hfp with ⟨h1, h2⟩
      exact ConvComplete_seq (ih1 h1) (ih2 h2)
    | par c1 c2 ih1 ih2 =>
      rcases hfp with ⟨h1, h2⟩
      exact ConvComplete_par (ih1 h1) (ih2 h2)
    | lifting c0 ih =>
      exact (ConvComplete_lifting (h:=ih hfp)).2 (ih hfp)
    | loop c0 ih =>
      exact (ConvComplete_loop (h:=ih hfp)).2 (ih hfp)
    | lifted_loop c0 ih =>
      exact (ConvComplete_lifted_loop (h:=ih hfp)).2 (ih hfp)
    | bracket c0 ih =>
      rcases hfp with ⟨hfc0, hsub⟩
      exact ConvComplete_bracket (ih hsub) hfc0

-- Following are important results showing that
-- Practical circuits are ConvComplete

-- LiftedScalar Circuits are FPComplete and ConvComplete
theorem LiftedScalar_is_FPComplete {A B: VType} {c: Ckt A B 0} (h: LiftedScalar c):
    FPComplete c := by
  constructor
  case FP1 =>
    intro x n _ h1
    use n
    apply LiftedScalar_ExtFP1_IntFP1 <;> tauto
  case FP2 =>
    simp

theorem LiftedScalar_is_ConvComplete {A B: VType} {c: Ckt A B 0} (h: LiftedScalar c):
    ConvComplete c := by
  intro x hc
  apply IntConv_LiftedScalar; tauto

-- Regular circuits are FPComplete and ConvComplete
theorem RegularCkt_is_FPComplete {A B: VType}
  {c: Ckt A B 0} (hr: RegularCkt c):
    FPComplete c := by
  constructor
  case FP1 =>
    intro x n _ h1
    use n
    apply RegularCkt_ExtFP1_IntFP1 <;> tauto
  case FP2 => simp

theorem RegularCkt_is_ConvComplete {A B: VType}
  {c: Ckt A B 0} (hr: RegularCkt c):
    ConvComplete c := by
  apply RegularCkt_IntConv hr

-- FPComplete and ConvComplete are closed under `pushLifting`
theorem pushLifting_FPComplete {A B}
  (c: Ckt A B 0) (h: FPComplete c):
    FPComplete (pushLifting c) := by
  constructor
  case FP2 =>
    simp
    intro x b hc hf
    rw [pushLifting_ExtConv_iff] at hc
    have h1 := h.FP1
    have hf' : ∀ i, ExtFP1 c (x i) (b i) := by
      intro i
      have hfi := hf i
      simp [ExtFP2, FixAfter2] at hfi
      rcases hfi with ⟨hxin, hxout⟩
      have hrow : (denote (pushLifting c) x) i = denote c (x i) := by
        have hdenx : denote (c↑ c) x = denote (pushLifting c) x :=
          congrArg (fun f => f x) (pushLifting_Sequiv c).denote
        have hdeni : denote (c↑ c) x i = denote (pushLifting c) x i :=
          congrArg (fun s => s i) hdenx
        simpa [denote, lifting] using hdeni.symm
      refine ⟨hxin, ?_⟩
      simpa [hrow] using hxout
    have hrow : ∀ i, ∃ n', IntFP1 c (x i) n' := by
      intro i
      exact h1 (x i) (b i) (hc i) (hf' i)
    classical
    choose b' hb' using hrow
    refine ⟨b', ?_⟩
    intro i
    exact pushLifting_IntFP2 (c:=c) (x:=x) (m:=i) (n:=b' i) (hb' i)
  case FP1 =>
    intro x n _ _
    use n; apply pushLifting_ExtFP1_IntFP1; tauto

theorem pushLifting_ConvComplete {A B}
  (c: Ckt A B 0):
    ConvComplete (pushLifting c) ↔ ConvComplete c := by
  simp [ConvComplete]
  constructor
  · intro h x hc
    specialize h (fun _ => x)
    rw [pushLifting_ExtConv_iff, pushLifting_IntConv_iff] at h
    simp at h; tauto
  · intro h x hc
    rw [pushLifting_IntConv_iff]; intro i
    apply h
    rw [pushLifting_ExtConv_iff] at hc; tauto

-- ConvComplete is closed under `incOpt`
theorem incOpt_ConvComplete {A B ns}
  (c: Ckt A B ns) [IncCkt c] (h: ConvComplete c):
    ConvComplete (incOpt c) := by
  simp [ConvComplete] at *
  intro x hc
  rw [<- integral_derivative x]
  apply incOpt_IntConv
  apply h
  rw [incOpt_ExtConv_iff]
  simp [hc]

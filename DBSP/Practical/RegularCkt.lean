import DBSP.Practical.Expressiveness
open CktBasic

inductive RegularCkt : ∀ {a b}, Ckt a b 0 -> Type 1
  | lifted_scalar {a b} (c: Ckt a b 0) (h: LiftedScalar c): RegularCkt c
  | seq {a b c} (c1: Ckt a b 0) (c2: Ckt b c 0)
      (h1: RegularCkt c1) (h2: RegularCkt c2): RegularCkt (c1 >>c c2)
  | par {a b} (c1: Ckt a b 0) (c2: Ckt a b 0)
      (h1: RegularCkt c1) (h2: RegularCkt c2): RegularCkt (c1 &&c c2)
  | whileloop {a} (c: Ckt a a 0) (h: RegularCkt c):
      RegularCkt (WhileLoop.query c)
  | datalog {a b} (c: Ckt (a ×ᵥ b) b 0) (h: RegularCkt c):
      RegularCkt (Datalog.query c)

-- extract the scalar function from a lifted operator
def extractScalar {a b: Type} (S: Operator a b): a -> b :=
  fun a => S (fun _ => a) 0

lemma extractScalar_correct {a b: Type}
  (S: Operator a b) (h: ∃ f, S = ↑↑f):
    S = ↑↑ (extractScalar S) := by
  rcases h with ⟨f, hf⟩
  rw [hf]
  funext x i; simp [extractScalar]

def ConvergeInput {a b: VType} {c: Ckt a b 0} (hr: RegularCkt c) (x: SOVType 0 a): Prop :=
  match hr with
  | RegularCkt.lifted_scalar _ _ => True
  | RegularCkt.seq c1 c2 h1 h2 => ConvergeInput h1 x ∧ ConvergeInput h2 (denote c1 x)
  | RegularCkt.par _ _ h1 h2 => ConvergeInput h1 x ∧ ConvergeInput h2 x
  | RegularCkt.whileloop c h => let f := extractScalar (denote c)
      (∃ b, FixedAtVec f x b) ∧ (∀ i, ConvergeInput h (funcIterStream f (x i)))
  | RegularCkt.datalog c h => let R := extractScalar (denote c)
      (∃ (b: stream ℕ), ∀ j, FixedAt (Datalog.f R (x j)) 0 (b j)) ∧
      (∀ j, ConvergeInput h ((Datalog.c0_input R (x j))))

theorem RegularCkt_denote {a b: VType} {c: Ckt a b 0} (hr: RegularCkt c):
    DenoteLiftedScalar c (extractScalar (denote c)) := by
  induction hr <;> apply extractScalar_correct
  case lifted_scalar c h =>
    apply LiftedScalar_Denote; assumption
  case seq c1 c2 h1 h2 ih1 ih2=>
    simp [denote]
    rw [ih1, ih2]; simp [liftO]
    use (fun x => extractScalar (denote c2) (extractScalar (denote c1) x))
    funext _ _; simp
  case par c1 c2 h1 h2 ih1 ih2 =>
    simp [denote]
    rw [ih1, ih2]; simp [liftO]
    use (fun x => (extractScalar (denote c1) x, extractScalar (denote c2) x))
    funext _ _; simp
  case whileloop c h _ =>
    simp [WhileLoop.query, denote]
    use (∫0 ∘ (denote (WhileLoop.body c)) ∘ δ0)
    funext _ _; simp
  case datalog c h _ =>
    simp [Datalog.query, denote]
    use (∫0 ∘ (denote (Datalog.body c)) ∘ δ0)
    funext _ _; simp

theorem RegularCkt_ExtFP1_IntFP1 {A B: VType}
  {c: Ckt A B 0} (hr: RegularCkt c)
  (x: SOVType 0 A) (n: ℕ) (he: ExtFP1 c x n):
    IntFP1 c x n := by
  induction hr
  case lifted_scalar c h =>
    apply LiftedScalar_ExtFP1_IntFP1 <;> tauto
  case seq c1 _ h1 _ _ _=>
    simp [IntFP1]
    simp [ExtFP1, denote] at he
    rcases he with ⟨hf1, hf2⟩
    have hf3 := FixedAfter1_lifting (f:= extractScalar (denote c1)) hf1
    apply RegularCkt_denote at h1
    simp [DenoteLiftedScalar, liftO] at h1
    rw [<- h1] at hf3
    tauto
  case par =>
    simp [IntFP1]
    simp [ExtFP1, denote] at he
    rw [FixedAfter1_sprod] at he
    tauto
  case whileloop =>
    apply WhileLoop.query_ExtFP1_IntFP1; tauto
  case datalog =>
    apply Datalog.query_ExtFP1_IntFP1; tauto

theorem RegularCkt_Terminate {A B: VType}
  {c: Ckt A B 0} (hr: RegularCkt c) (x: SOVType 0 A)
  (hc: ConvergeInput hr x):
    Terminate c x := by
  induction hr
  case lifted_scalar =>
    apply Terminate_LiftedScalar; tauto
  case seq =>
    simp [Terminate]
    simp [ConvergeInput] at hc
    tauto
  case par =>
    simp [Terminate]
    simp [ConvergeInput] at hc
    tauto
  case whileloop c h _ =>
    simp [ConvergeInput] at hc
    rcases hc with ⟨⟨b, hf⟩, hc⟩
    have := RegularCkt_denote h
    have := RegularCkt_ExtFP1_IntFP1 h
    apply WhileLoop.query_Terminate <;> tauto
  case datalog c h _ =>
    simp [ConvergeInput] at hc
    rcases hc with ⟨⟨b, hf⟩, hc⟩
    have := RegularCkt_denote h
    have := RegularCkt_ExtFP1_IntFP1 h
    apply Datalog.query_Terminate <;> tauto

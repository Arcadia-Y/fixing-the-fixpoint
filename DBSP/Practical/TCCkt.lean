import DBSP.Termination.Spec
import DBSP.Practical.RegularCkt
import DBSP.Practical.PushLifting
open CktBasic

-- Termination-complete circuits are those good circuits whose convergence implies termination. This means for them termination coincides with convergence, so we can safely use them without worrying about the FPD problem.
def TCCkt {ns} {A B: VType} (c: Ckt A B ns): Prop :=
  ∀ x, Converge c x → Terminate c x

theorem TCCkt_Terminate_iff_Converge {A B ns}
  {c: Ckt A B ns} (h: TCCkt c):
    Terminate c = Converge c := by
  funext x; simp; constructor
  apply Terminate_impl_Converge
  apply h

-- Regular circuits are Termination-complete circuits
theorem RegularCkt_is_TCCkt {A B: VType}
  {c: Ckt A B 0} (hr: RegularCkt c):
    TCCkt c := by
  apply RegularCkt_Terminate hr

macro "solve_good" : tactic => `(tactic| (
  intro x hc
  simp [Converge] at hc
  simp [Terminate]; tauto
))

-- Termination-complete circuits are closed under all circuit constructs except `bracket`
theorem TCCkt_seq {ns} {A B C: VType}
  {c1: Ckt A B ns} {c2: Ckt B C ns}
  (h1: TCCkt c1) (h2: TCCkt c2):
    TCCkt (c1 >>c c2) := by
  solve_good

theorem TCCkt_par {ns} {A B C: VType}
  {c1: Ckt A B ns} {c2: Ckt A C ns}
  (h1: TCCkt c1) (h2: TCCkt c2):
    TCCkt (c1 &&c c2) := by
  solve_good

theorem TCCkt_loop {ns} {A B: VType}
  {c: Ckt (A ×ᵥ B) B ns} (h: TCCkt c):
    TCCkt (cloop c) ↔ TCCkt c := by
  constructor
  · intro _
    tauto
  · intro _
    solve_good

theorem TCCkt_lifting {A B: VType}
  {c: Ckt A B 0} (h: TCCkt c):
    TCCkt (c↑ c) ↔ TCCkt c := by
  constructor
  · intro _
    tauto
  · intro _
    solve_good

theorem TCCkt_lifted_loop {A B: VType}
  {c: Ckt (A ×ᵥ B) B 1} (h: TCCkt c):
    TCCkt (cloop2 c) ↔ TCCkt c := by
  constructor
  · intro _
    tauto
  · intro _
    solve_good

-- Good Circuits are closed under `pushLifting` and `incOpt`
theorem pushLifting_TCCkt {A B}
  (c: Ckt A B 0):
    TCCkt (pushLifting c) ↔ TCCkt c := by
  simp [TCCkt]
  constructor
  · intro h x hc
    specialize h (fun _ => x)
    rw [pushLifting_Converge_iff, pushLifting_Terminate_iff] at h
    simp at h; tauto
  · intro h x hc
    rw [pushLifting_Terminate_iff]; intro i
    apply h
    rw [pushLifting_Converge_iff] at hc; tauto

theorem incOpt_TCCkt {A B ns}
  (c: Ckt A B ns) [IncCkt c] (h: TCCkt c):
    TCCkt (incOpt c) := by
  simp [TCCkt] at *
  intro x hc
  rw [<- integral_derivative x]
  apply incOpt_Terminate
  apply h
  rw [incOpt_Converge_iff]
  simp [hc]

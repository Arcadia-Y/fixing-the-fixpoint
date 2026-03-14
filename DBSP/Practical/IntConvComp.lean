import DBSP.Convergence.Spec
import DBSP.Practical.RegularCkt
import DBSP.Practical.PushLifting
open CktBasic

-- IntConv-complete circuits are those good circuits whose convergence implies termination. This means for them termination coincides with convergence, so we can safely use them without worrying about the FPD problem.
def IntConvComp {ns} {A B: VType} (c: Ckt A B ns): Prop :=
  ∀ x, ExtConv c x → IntConv c x

theorem IntConvComp_IntConv_iff_ExtConv {A B ns}
  {c: Ckt A B ns} (h: IntConvComp c):
    IntConv c = ExtConv c := by
  funext x; simp; constructor
  apply IntConv_impl_ExtConv
  apply h

-- Regular circuits are IntConv-complete circuits
theorem RegularCkt_is_IntConvComp {A B: VType}
  {c: Ckt A B 0} (hr: RegularCkt c):
    IntConvComp c := by
  apply RegularCkt_IntConv hr

macro "solve_good" : tactic => `(tactic| (
  intro x hc
  simp [ExtConv] at hc
  simp [IntConv]; tauto
))

-- IntConv-complete circuits are closed under all circuit constructs except `bracket`
theorem IntConvComp_seq {ns} {A B C: VType}
  {c1: Ckt A B ns} {c2: Ckt B C ns}
  (h1: IntConvComp c1) (h2: IntConvComp c2):
    IntConvComp (c1 >>c c2) := by
  solve_good

theorem IntConvComp_par {ns} {A B C: VType}
  {c1: Ckt A B ns} {c2: Ckt A C ns}
  (h1: IntConvComp c1) (h2: IntConvComp c2):
    IntConvComp (c1 &&c c2) := by
  solve_good

theorem IntConvComp_loop {ns} {A B: VType}
  {c: Ckt (A ×ᵥ B) B ns} (h: IntConvComp c):
    IntConvComp (cloop c) ↔ IntConvComp c := by
  constructor
  · intro _
    tauto
  · intro _
    solve_good

theorem IntConvComp_lifting {A B: VType}
  {c: Ckt A B 0} (h: IntConvComp c):
    IntConvComp (c↑ c) ↔ IntConvComp c := by
  constructor
  · intro _
    tauto
  · intro _
    solve_good

theorem IntConvComp_lifted_loop {A B: VType}
  {c: Ckt (A ×ᵥ B) B 1} (h: IntConvComp c):
    IntConvComp (cloop2 c) ↔ IntConvComp c := by
  constructor
  · intro _
    tauto
  · intro _
    solve_good

-- Good Circuits are closed under `pushLifting` and `incOpt`
theorem pushLifting_IntConvComp {A B}
  (c: Ckt A B 0):
    IntConvComp (pushLifting c) ↔ IntConvComp c := by
  simp [IntConvComp]
  constructor
  · intro h x hc
    specialize h (fun _ => x)
    rw [pushLifting_ExtConv_iff, pushLifting_IntConv_iff] at h
    simp at h; tauto
  · intro h x hc
    rw [pushLifting_IntConv_iff]; intro i
    apply h
    rw [pushLifting_ExtConv_iff] at hc; tauto

theorem incOpt_IntConvComp {A B ns}
  (c: Ckt A B ns) [IncCkt c] (h: IntConvComp c):
    IntConvComp (incOpt c) := by
  simp [IntConvComp] at *
  intro x hc
  rw [<- integral_derivative x]
  apply incOpt_IntConv
  apply h
  rw [incOpt_ExtConv_iff]
  simp [hc]

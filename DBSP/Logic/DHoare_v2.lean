import DBSP.Circuits
import DBSP.Circuits.ProdType
import DBSP.StreamTheory.Linear
import Mathlib.Algebra.Group.Defs
import DBSP.Dominate
open CktBasic

section DHoare

variable {A B: VType} (c: Ckt A B)

def SizeBound (size_bound: Operator (VType_Nat A) (VType_Nat B)) : Prop :=
  MonoDom size_bound ∧
  ∀ (input: (stream (VType_interp A))),
     letI i_size := (↑↑VType_size) input
     letI o_size := (↑↑VType_size) (denote c input)
     o_size << size_bound i_size

def CostBound (cost_bound: Operator (VType_Nat A) ℕ) : Prop :=
  MonoDom cost_bound ∧
  ∀ (input: (stream (VType_interp A))),
     letI i_size := (↑↑VType_size) input
     letI cost := cost_f c input
     cost << cost_bound i_size

def DHoare {A B: VType} (c: Ckt A B)
  (size_bound: Operator (VType_Nat A) (VType_Nat B))
  (cost_bound: Operator (VType_Nat A) ℕ) : Prop :=
  SizeBound c size_bound ∧ CostBound c cost_bound

lemma VType_Nat_le_add (x1 y1 x2 y2: VType_Nat A)
  (h1: x1 ≤ y1) (h2: x2 ≤ y2):
    x1 + x2 ≤ y1 + y2 := by
  induction A
  · apply Nat.add_le_add <;> tauto
  · rcases h1 with ⟨h11,h12⟩; rcases h2 with ⟨h21,h22⟩
    constructor <;> try tauto

lemma VType_Nat_le_mul (x y: VType_Nat A) (k: ℕ)
  (h: x ≤ y):
    k • x ≤ k • y := by
  induction k; simp
  rw [add_nsmul]; rw [add_nsmul]; simp
  apply VType_Nat_le_add <;> tauto

lemma s_VType_Nat_le_add (x1 y1 x2 y2: stream (VType_Nat A))
  (h1: x1 ≤ y1) (h2: x2 ≤ y2):
    x1 + x2 ≤ y1 + y2 := by
  intro t; simp
  specialize h1 t; specialize h2 t
  apply VType_Nat_le_add <;> tauto

lemma s_VType_Nat_le_mul (x y: stream (VType_Nat A)) (k: ℕ)
  (h: x ≤ y):
    k • x ≤ k • y := by
  intro t; simp
  specialize h t
  apply VType_Nat_le_mul; tauto

syntax "sV_linear" : tactic
macro_rules
| `(tactic| sV_linear) =>
    `(tactic| apply s_VType_Nat_le_add; swap; try trivial; apply s_VType_Nat_le_mul <;> try tauto
    )

--- SizeBound Rules
theorem SizeBound_weaken sb {sb'}
  (h: SizeBound c sb) (h1: sb =O sb'):
    SizeBound c sb' := by
  rcases h1
  constructor; tauto
  intros input
  rcases h with ⟨hm, hl⟩
  apply dom_trans; apply hl
  tauto

theorem SizeBound_seq {C: VType} (c1: Ckt A B) (c2: Ckt B C)
  sb1 sb2
  (H1: SizeBound c1 sb1) (H2: SizeBound c2 sb2) :
    SizeBound (c1 >>c c2) (sb2 ∘ sb1) := by
  rcases H1 with ⟨Hm1, H1⟩
  rcases H2 with ⟨Hm2, H2⟩
  constructor
  apply MonoDom.comp <;> tauto
  intros input
  simp [denote]
  specialize H1 input
  specialize H2 (denote c1 input)
  specialize Hm2 H1
  apply dom_trans <;> tauto

lemma stream_smul_par_comm {A B: VType}
  (s1: stream (VType_Nat A)) (s2: stream (VType_Nat B)) (k: ℕ):
    k • (fun n => (s1 n, s2 n)) = fun n => (k • s1 n, k • s2 n) := by
  ext n <;> simp

lemma dominate_pair {A B: VType} (s1 s2: stream (VType_Nat (A ×ᵥ B)))
  (h1: ↑↑Prod.fst s1 << ↑↑Prod.fst s2) (h2: ↑↑Prod.snd s1 << ↑↑Prod.snd s2) :
    s1 << s2 := by
  rcases h1 with ⟨k1, h1⟩
  rcases h2 with ⟨k2, h2⟩
  use (k1 + k2); rw [stream_smul_par_comm]
  intro n; simp; constructor
  · apply le_trans; apply h1
    rw [add_smul]; simp
  · apply le_trans; apply h2
    simp; rw [add_smul]; simp

theorem SizeBound_par {C: VType} (c1: Ckt A B) (c2: Ckt A C)
  sb1 sb2
  (H1: SizeBound c1 sb1) (H2: SizeBound c2 sb2) :
    SizeBound (c1 &&c c2) (fun is => (sb1 is, sb2 is)) := by
  rcases H1 with ⟨Hm1, H1⟩
  rcases H2 with ⟨Hm2, H2⟩
  simp; constructor
  · intro s1 s2 h
    apply dominate_pair
    apply Hm1 h; apply Hm2 h
  · intros input
    specialize H1 input
    specialize H2 input
    simp [denote]
    apply dominate_pair
    apply H1; apply H2

lemma VType_size_delay (f: stream (VType_interp A)) t:
    VType_size (z⁻¹ f t) = z⁻¹ ((↑↑VType_size) f ) t := by
  have := @VType_size_Timeinvariant A
  simp [TimeInvariant] at this
  specialize this f
  rw [<- this]; simp

lemma le_delay {A: Type} [Zero A] [PartialOrder A]
  (f g: stream A) (h: f ≤ g):
    z⁻¹ f ≤ z⁻¹ g := by
  intro t; simp [delay]; split_ifs <;> tauto

-- theorem SizeBound_loop (c: Ckt (A ×ᵥ B) B) sb
--   (sb': Operator (VType_Nat A) (VType_Nat B)) (H: SizeBound c sb)
--   (hmono: MonoDom sb')
--   (sb_ind: ∀ x, sb (x, z⁻¹ (sb' x)) << sb' x) :
--     SizeBound (cloop c) sb' := by
--   constructor; tauto
--   intros input
--   set o := denote (cloop c) input
--   simp [o, denote]; rw [stream_le_ext]; simp [fix]
--   set nthf := nth (fun s ↦ denote c (sprod (input, z⁻¹ s)))
--   suffices
--   ∀ (t : ℕ), (↑↑VType_size) (nthf t) ≤ sb' i_bound by
--     intro t; apply this
--   intro t; induction t
--   · specialize H (sprod (input, 0)) (i_bound, z⁻¹ (sb' i_bound)); simp at H
--     specialize H (by
--       intro t; simp; constructor <;> try tauto
--       apply PType_Nat_0_min
--       )
--     apply le_trans; simp [nthf]; apply H; apply sb_ind
--   · rename_i n ih
--     simp [nthf]
--     specialize H (sprod (input, z⁻¹ (nthf n))) (sprod (i_bound, z⁻¹ (sb' i_bound)))
--     specialize H (by
--       intro t; simp; constructor <;> try tauto
--       rw [VType_size_delay]; apply le_delay; tauto
--       )
--     apply le_trans; apply H
--     apply sb_ind

theorem SizeBound_delay:
    SizeBound (@Ckt.delay A) id := by
  constructor; apply MonoDom_id
  intros input
  simp [denote]; apply

theorem SizeBound_id:
    SizeBound (@Ckt.id A) id := by
  intros input i_bound hi
  simp [denote]; tauto

theorem SizeBound_fst:
    SizeBound (@Ckt.fst A B) (↑↑Prod.fst) := by
  intros input i_bound hi
  simp [denote]; intro t; simp
  specialize hi t
  rcases hi; tauto

theorem SizeBound_snd:
    SizeBound (@Ckt.snd A B) (↑↑Prod.snd) := by
  intros input i_bound hi
  simp [denote]; intro t; simp
  specialize hi t
  rcases hi; tauto

--- CostBound Rules
theorem CostBound_weaken cb {cb'}
  (H: CostBound c cb)
  (Hs: cb ≤ cb'):
    CostBound c cb' := by
  intros input i_bound; intro hi
  specialize H input i_bound hi
  eapply le_trans
  swap; apply Hs
  tauto

theorem CostBound_seq {C: VType} (c1: Ckt A B) (c2: Ckt B C)
  sb1 cb1 cb2 (H1s: SizeBound c1 sb1)
  (H1c: CostBound c1 cb1) (H2c: CostBound c2 cb2) :
    CostBound (c1 >>c c2) (fun is => cb1 is + cb2 (sb1 is)) := by
  intros input i_bound hi
  specialize H1s input i_bound hi
  specialize H1c input i_bound hi
  specialize H2c (denote c1 input) (sb1 i_bound) H1s
  simp [cost_f]; intro t; simp
  specialize H1c t; specialize H2c t
  apply Nat.add_le_add <;> tauto

theorem CostBound_par {C: VType} (c1: Ckt A B) (c2: Ckt A C)
  cb1 cb2 (H1c: CostBound c1 cb1) (H2c: CostBound c2 cb2) :
    CostBound (c1 &&c c2) (fun is => cb1 is + cb2 is) := by
  intros input i_bound hi
  specialize H1c input i_bound hi
  specialize H2c input i_bound hi
  simp [cost_f]; intro t; simp
  specialize H1c t; specialize H2c t
  apply Nat.add_le_add <;> tauto

theorem CostBound_loop (c: Ckt (A ×ᵥ B) B) cb sb'
  (Hc: CostBound c cb) (Hs: SizeBound (cloop c) sb') :
    CostBound
      (cloop c)
      (fun x => cb (x, z⁻¹ (sb' x)) + (↑↑PType_sum) (sb' x)) := by
  intros input i_bound hi
  set o := denote (cloop c) input
  simp [cost_f]; intro t; simp
  specialize Hc (input, z⁻¹ o) (i_bound, z⁻¹ (sb' i_bound)); simp at Hc
  specialize Hc (by
    intro t; simp; constructor <;> try tauto
    rw [VType_size_delay]; apply le_delay; tauto
    )
  specialize Hc t
  specialize Hs input i_bound hi
  specialize Hs t; simp at Hs
  have := PType_sum_Nat_mono _ _ Hs
  apply Nat.add_le_add <;> tauto

theorem CostBound_delay:
    CostBound (@Ckt.delay A) (↑↑PType_sum) := by
  intros input i_bound hi
  simp [cost_f]; intro t; simp
  apply PType_sum_Nat_mono; tauto

theorem CostBound_id:
    CostBound (@Ckt.id A) 0 := by
  intros input i_bound hi
  intro t; simp; simp [cost_f]

theorem CostBound_fst:
    CostBound (@Ckt.fst A B) 0 := by
  intros input i_bound hi
  intro t; simp; simp [cost_f]

theorem CostBound_snd:
    CostBound (@Ckt.snd A B) 0 := by
  intros input i_bound hi
  intro t; simp; simp [cost_f]

--- DHoare Rules
theorem DHoare_weaken_size sb {cb sb'}
  (H: DHoare c sb cb)
  (Hs: sb ≤ sb'):
    DHoare c sb' cb := by
  simp [DHoare] at *
  constructor <;> try tauto
  apply SizeBound_weaken <;> tauto

theorem DHoare_weaken_cost cb {sb cb'}
  (H: DHoare c sb cb)
  (Hs: cb ≤ cb'):
    DHoare c sb cb' := by
  simp [DHoare] at *
  constructor <;> try tauto
  apply CostBound_weaken <;> tauto

theorem DHoare_weaken sb cb {sb' cb'}
  (H: DHoare c sb cb)
  (Hs: sb ≤ sb') (Hc: cb ≤ cb'):
    DHoare c sb' cb' := by
  apply DHoare_weaken_size _ sb <;> try tauto
  apply DHoare_weaken_cost _ cb <;> tauto

theorem DHoare_seq {C: VType} (c1: Ckt A B) (c2: Ckt B C)
  sb1 sb2 cb1 cb2
  (H1: DHoare c1 sb1 cb1) (H2: DHoare c2 sb2 cb2) :
    DHoare (c1 >>c c2) (sb2 ∘ sb1) (fun is => cb1 is + cb2 (sb1 is)) := by
  simp [DHoare] at *; constructor
  · apply SizeBound_seq <;> tauto
  · apply CostBound_seq <;> tauto

theorem DHoare_par {C: VType} (c1: Ckt A B) (c2: Ckt A C)
  sb1 sb2 cb1 cb2
  (H1: DHoare c1 sb1 cb1) (H2: DHoare c2 sb2 cb2) :
    DHoare (c1 &&c c2)
           (fun is => (sb1 is, sb2 is))
           (fun is => cb1 is + cb2 is) := by
  simp [DHoare] at *; constructor
  · apply SizeBound_par <;> tauto
  · apply CostBound_par <;> tauto

theorem DHoare_loop
  (c: Ckt (A ×ᵥ B) B) sb cb (sb': Operator (VType_Nat A) (VType_Nat B))
  (H: DHoare c sb cb)
  (sb_ind: ∀ x, sb (x, z⁻¹ (sb' x)) ≤ sb' x) :
    DHoare (cloop c)
            sb'
           (fun x => cb (x, z⁻¹ (sb' x)) + (↑↑PType_sum) (sb' x)) := by
  simp [DHoare] at *
  have := SizeBound_loop c sb sb' (by tauto) sb_ind
  constructor <;> try tauto
  apply CostBound_loop <;> tauto

theorem DHoare_delay:
    DHoare (@Ckt.delay A) z⁻¹ (↑↑PType_sum) := by
  simp [DHoare]; constructor
  apply SizeBound_delay; apply CostBound_delay

theorem DHoare_id:
    DHoare (@Ckt.id A) id 0 := by
  simp [DHoare]; constructor
  apply SizeBound_id; apply CostBound_id

theorem DHoare_fst:
    DHoare (@Ckt.fst A B) (↑↑Prod.fst) 0 := by
  simp [DHoare]; constructor
  apply SizeBound_fst; apply CostBound_fst

theorem DHoare_snd:
    DHoare (@Ckt.snd A B) (↑↑Prod.snd) 0 := by
  simp [DHoare]; constructor
  apply SizeBound_snd; apply CostBound_snd

end DHoare

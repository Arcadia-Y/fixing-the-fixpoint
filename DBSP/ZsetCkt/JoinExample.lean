import DBSP.ZsetCkt.ZsetCkt
import DBSP.ZsetCkt.ZsetHoareR
open CktBasic

namespace JoinExample
--- the original circuit
def ckt1 : Ckt ([Z[ℤ×ℤ×ℤ]]v ×ᵥ [Z[ℤ×ℤ×ℤ]]v) ([Z[ℤ×ℤ]]v) 0 :=
  (c1st >>c zfilter (fun x => x.1 > 2) >>c zmap (fun x => x.2) &&c
    c2nd >>c zfilter (fun x => x.1 > 5) >>c zmap (fun x => x.2)) >>c
  zjoin Prod.snd Prod.fst >>c
  zmap (fun (t1, t2) => (t1.1, t2.1)) >>c zdistinct

instance : IncCkt ckt1 := by
  unfold ckt1; infer_instance

-- the optimized incremental circuit
def ckt2 : Ckt ([Z[ℤ×ℤ×ℤ]]v ×ᵥ [Z[ℤ×ℤ×ℤ]]v) ([Z[ℤ×ℤ]]v) 0 :=
  (c1st >>c zfilter (fun x => x.1 > 2) >>c zmap (fun x => x.2) &&c
    c2nd >>c zfilter (fun x => x.1 > 5) >>c zmap (fun x => x.2)) >>c
  bilinear_opt (zjoin Prod.snd Prod.fst) >>c
  zmap (fun (t1, t2) => (t1.1, t2.1)) >>c incr_dist

lemma incOpt_ckt1_ckt2:
  incOpt ckt1 = ckt2 := rfl

theorem ckt1_HoareR {x1 x2: SOType 0 Z[ℤ×ℤ×ℤ]} {b1 b2: stream ℕ}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2):
    HoareR
      (fun x => x = sprod (x1, x2))
      ckt1
      (fun y => ZSB y (fun i ↦ b1 i * b2 i))
      (fun i => 3 * (b1 i + 1) * (b2 i + 1)) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  unfold ckt1
  apply HoareR_seq
  apply HoareR_seq
  apply HoareR_seq
  apply HoareR_par'
  · apply HoareR_seq
    apply HoareR_seq
    apply HoareR_fst
    apply HoareR_ZSB_filter ; tauto
    apply HoareR_sintro; intros
    apply HoareR_ZSB_map ; tauto
  · apply HoareR_seq
    apply HoareR_seq
    apply HoareR_snd
    apply HoareR_ZSB_filter ; tauto
    apply HoareR_sintro; intros
    apply HoareR_ZSB_map ; tauto
  apply HoareR_sintro
  rintro v ⟨y1, ⟨y2, ⟨_, ⟨_, _⟩⟩⟩⟩
  subst v; simp only [sprodO]
  apply HoareR_ZSB_join <;> tauto
  apply HoareR_sintro
  intro y hy; simp at hy
  apply HoareR_ZSB_map; tauto
  apply HoareR_sintro
  intro y hy; simp at hy
  apply HoareR_ZSB_distinct; tauto
  · simp
    intro i; simp
    linarith
  · simp [ZSB]

lemma HoareR_ZSB_opt_join {x1 x2: SOType 0 Z[ℤ×ℤ]} {b1 b2: stream ℕ}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2)
  (h1d: stream_id_distinct Prod.snd x1)
  (h2d: stream_id_distinct Prod.fst x2):
    HoareR
      (fun x => x = sprod (x1, x2))
      (bilinear_opt (ns:=0) (zjoin Prod.snd Prod.fst))
      (fun y => ZSB y (b1 + b2))
      (fun i => (I b1 i + 1) * (b2 i + 4) + (I b2 i + 1) * (b1 i + 4)) := by
  unfold bilinear_opt
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_seq
  apply HoareR_par'
  · apply HoareR_seq
    apply HoareR_par'
    · apply HoareR_seq
      apply HoareR_fst
      simp; apply HoareR_sid_I <;> tauto
    · apply HoareR_snd
    apply HoareR_sintro
    rintro v ⟨y1, ⟨y2, ⟨_, ⟨_, hy2⟩⟩⟩⟩
    simp at hy2; subst y2
    subst v; simp only [sprodO]
    apply HoareR_sid_join_r <;> tauto
  · apply HoareR_seq
    apply HoareR_par'
    · apply HoareR_fst
    · repeat (apply HoareR_seq)
      apply HoareR_snd
      simp; apply HoareR_sid_I <;> tauto
      apply HoareR_sintro
      rintro y ⟨hy, hsy⟩
      apply HoareR_sid_delay <;> try tauto
      apply mono_integral_stream
    apply HoareR_sintro
    rintro v ⟨y1, ⟨y2, ⟨_, ⟨hy1, _⟩⟩⟩⟩
    simp at hy1; subst y1
    subst v; simp only [sprodO]
    apply HoareR_sid_join_l <;> tauto
  apply HoareR_sintro
  rintro v ⟨y1, ⟨y2, ⟨_, ⟨_, _⟩⟩⟩⟩
  subst v; simp
  apply HoareR_ZSB_add <;> tauto
  · intro i; simp
    linarith
  · rw [add_comm]; simp

lemma HoareR_incr_dist {A: Type} [DecidableEq A] {x: SOType 0 Z[A]} {b: SOType 0 ℕ}
  (h: ZSB x b):
    HoareR
      (fun y => y = x)
      (incr_dist (A:=A) (ns:=0))
      (fun y => ZSB y (I b + b))
      (fun i => 6 * I b i) := by
  unfold incr_dist
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_seq
  apply HoareR_par'
  · apply HoareR_seq
    apply HoareR_ZSB_I; tauto
    apply HoareR_conseq_post (Q:= fun y => ZSB y (I b))
    apply HoareR_sintro; rintro y hy
    apply HoareR_ZSB_delay; tauto
    simp [ZSB]
    intros
    apply le_trans; tauto
    apply delay_le
    apply mono_integral_stream
  · apply HoareR_id
  apply HoareR_sintro
  rintro _ ⟨y1, ⟨y2, ⟨hv, ⟨hy1, hy2⟩⟩⟩⟩; subst hv; subst y2
  simp only [sprodO]
  apply HoareR_weaken_bound
  apply HoareR_ZSB_H (ns:=0) <;> tauto
  apply add_le_add
  rfl; apply le_integral
  · intro i; simp
    linarith
  · simp

theorem ckt2_HoareR {x1 x2: SOType 0 Z[ℤ×ℤ×ℤ]} {b1 b2: stream ℕ}
  (h1: ZSB x1 b1) (h2: ZSB x2 b2)
  (h1d: stream_id_distinct (fun x => x.2.2) x1)
  (h2d: stream_id_distinct (fun x => x.2.1) x2):
    HoareR
       (fun x => x = sprod (x1, x2))
      ckt2
      (fun y => ZSB y (I (b1 + b2) + (b1 + b2)))
      (fun i => (I b1 i + 4) * (b2 i + 10) + (I b2 i + 4) * (b1 i + 10)) := by
  unfold ckt2
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_seq
  apply HoareR_seq
  apply HoareR_seq
  apply HoareR_par'
  · apply HoareR_seq
    apply HoareR_seq
    apply HoareR_fst
    apply HoareR_sid_filter (π:=Prod.snd ∘ Prod.snd)
    · tauto
    · convert h1d
    apply HoareR_sintro; rintro y ⟨hy, hd⟩
    apply HoareR_sid_map (g:=Prod.snd)
    · exact hy
    · exact hd
  · apply HoareR_seq
    apply HoareR_seq
    apply HoareR_snd
    apply HoareR_sid_filter (π:=Prod.fst ∘ Prod.snd)
    · tauto
    · convert h2d
    apply HoareR_sintro; rintro y ⟨hy, hd⟩
    apply HoareR_sid_map (g:=Prod.fst)
    · exact hy
    · exact hd
  apply HoareR_sintro
  rintro _ ⟨y1, ⟨y2, ⟨hv, ⟨⟨hy1, hd1⟩, ⟨hy2, hd2⟩⟩⟩⟩⟩
  subst hv
  apply HoareR_ZSB_opt_join
  · exact hy1
  · exact hy2
  · exact hd1
  · exact hd2
  apply HoareR_sintro
  intro y hy
  apply HoareR_ZSB_map; tauto
  apply HoareR_sintro
  intro y hy
  apply HoareR_incr_dist
  case h => assumption
  case hq => simp
  case hr =>
    intro i; simp
    rw [integral_linear]; simp
    linarith

-- Let's assume that the delta stream is bounded by a constant, say 1
-- Then the database stream is bounded by n+1
lemma ckt1_HoareR_example {x1 x2: SOType 0 Z[ℤ×ℤ×ℤ]}
  (h1: ZSB x1 (fun n => n+1)) (h2: ZSB x2 (fun n => n+1)):
    HoareR
      (fun x => x = sprod (x1, x2))
      ckt1
      (fun y => ZSB y (fun n ↦ n*n + 4*n + 4))
      (fun n => 3*n*n + 12*n + 12) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply ckt1_HoareR <;> tauto
  intro n; simp; nlinarith
  simp [ZSB]; intro x h
  apply le_trans h
  intro i; simp; nlinarith

@[simp]
lemma I1_simp:
  I (fun _ => 1) = fun i => i.succ := by
  funext b2; simp [integral_sumVals]; induction b2 <;> simp
  rename_i ih; rw [ih]; omega

lemma ckt2_HoareR_example {x1 x2: SOType 0 Z[ℤ×ℤ×ℤ]}
  (h1: ZSB x1 (fun _ => 1)) (h2: ZSB x2 (fun _ => 1))
  (h1d: stream_id_distinct (fun x => x.2.2) x1)
  (h2d: stream_id_distinct (fun x => x.2.1) x2):
    HoareR
       (fun x => x = sprod (x1, x2))
      ckt2
      (fun y => ZSB y (fun n => 2*n + 4))
      (fun n => 22*n + 110) := by
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply ckt2_HoareR <;> tauto
  intro n; simp; nlinarith
  simp [ZSB]; intro x h
  apply le_trans h
  rw [integral_linear]
  intro i; simp; nlinarith

end JoinExample

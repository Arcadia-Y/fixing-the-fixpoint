import DBSP.ZsetCkt.GraphExample

namespace GraphExample
open CktBasic
open Datalog

-- `JoinRes` represents the result of a doubly-lifted join on `S1 ` and `S2`
abbrev JoinRes
  (S1: SOType 1 (Finset (ℕ × ℕ)))
  (S2: SOType 1 (Finset (ℕ × ℕ))):
    SOType 1 (Finset ((ℕ × ℕ) × (ℕ × ℕ))) :=
  fun i j => {t ∈ (S1 i j) ×ˢ (S2 i j) | t.1.2 = t.2.1}

-- `Dis n` contains exactly `(n-1, n)` for `n > 0`, and is empty for `n = 0`
abbrev Dis (n: ℕ): Finset (ℕ × ℕ) :=
  if n = 0 then ∅ else {(n-1, n)}

lemma Dis_eq:
    D is = fun n => Zset.fromSet (Dis n) := by
  funext n; rcases n with _ | n <;> simp [D, is]
  · rw [<- Zset.isSet_support_fromSet]
    simp; simp [path]
  · ext x; rcases x with ⟨a, b⟩
    simp [path, Dis]
    split_ifs <;> simp <;> omega

lemma Dis_card (n: ℕ):
    (Dis n).card = if n = 0 then 0 else 1 := by
  split_ifs <;> simp [Dis]

lemma Dis_card_bound (n: ℕ):
    (Dis n).card ≤ 1 := by
  rw [Dis_card]; split_ifs <;> simp

lemma Dis_biUnion (i: ℕ):
    (Finset.range (i+1)).biUnion Dis = path i := by
  ext ⟨a, b⟩; simp [Dis, path, Finset.mem_biUnion, Finset.mem_range]; constructor
  · rintro ⟨k, hk, hm⟩
    split_ifs at hm with h
    · exact absurd hm (Finset.notMem_empty _)
    · simp at hm; omega
  · rintro ⟨hk, rfl⟩
    exact ⟨a + 1, by omega, by simp⟩

lemma delta_biUnion_j (S: stream (Finset (ℕ × ℕ)))(i j: ℕ):
    (Finset.range (j+1)).biUnion (fun k => ↑↑δ0 S i k) = S i := by
  ext a; simp [Finset.mem_biUnion, Finset.mem_range]; constructor
  · rintro ⟨k, hk, ha⟩; split_ifs at ha with h <;> [exact ha; exact absurd ha (Finset.notMem_empty _)]
  · intro ha; exact ⟨0, by omega, by simp [ha]⟩

lemma delta_biUnion_i (S: stream (Finset (ℕ × ℕ)))(i j: ℕ):
    (Finset.range (i+1)).biUnion (fun k => ↑↑δ0 S k j) =
    ↑↑δ0 (fun n => (Finset.range (n+1)).biUnion S) i j := by
  ext a; simp [Finset.mem_biUnion, Finset.mem_range]; constructor
  · rintro ⟨k, hk, ha⟩; split_ifs at ha ⊢
    · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, ha⟩
    · exact absurd ha (Finset.notMem_empty _)
  · intro ha; split_ifs at ha ⊢
    · obtain ⟨k, hk, hka⟩ := Finset.mem_biUnion.mp ha
      exact ⟨k, Finset.mem_range.mp hk, hka⟩
    · exact absurd ha (Finset.notMem_empty _)

-- `DS1 i j` contains all edges pointing to the new node `i` in `P_i`
--   that are at most `j+1` hops long
-- `1` means `D` operates on the first time dimension
abbrev DS1 (i j: ℕ): Finset (ℕ × ℕ) :=
  (Finset.range (min i (j+1))).image fun x => (i - 1 - x, i)

lemma mono_S_i (i j: ℕ): S i j ⊆ S (i + 1) j := by
  intro ⟨a, b⟩ hab
  simp only [S, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hab ⊢
  obtain ⟨x, hx, k, hk, hab⟩ := hab
  exact ⟨x, by omega, k, by omega, hab⟩

lemma fromSet_sub_sdiff {A: Type} [DecidableEq A] (s1 s2: Finset A) (h: s2 ⊆ s1):
    Zset.fromSet s1 - Zset.fromSet s2 = Zset.fromSet (s1 \ s2) := by
  ext a; rw [Zset.sub_apply]
  simp only [Zset.fromSet_apply, Finset.mem_sdiff]
  by_cases h1 : a ∈ s1 <;> by_cases h2 : a ∈ s2 <;> simp [h1, h2]
  exact absurd (h h2) h1

lemma S_sdiff_DS1 (i j: ℕ): S (i + 1) j \ S i j = DS1 (i + 1) j := by
  ext ⟨a, b⟩
  simp only [Finset.mem_sdiff, S, DS1, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x, hx, k, hk, rfl, rfl⟩, hns⟩
    have hke : k = i - x := by
      by_contra hne
      exact hns ⟨x, by omega, k, by omega, rfl, rfl⟩
    subst hke; exact ⟨x, hx, rfl, by omega⟩
  · rintro ⟨x, hx, rfl, rfl⟩
    refine ⟨⟨x, hx, i - x, by omega, rfl, by omega⟩, ?_⟩
    rintro ⟨y, hy, k, hk, h1, h2⟩; omega

lemma DS1_eq:
    D (fun i j => Zset.fromSet (S i j)) =
    (fun i j => Zset.fromSet (DS1 i j)) := by
  funext i j; rcases i with _ | i <;> simp [D, is]
  · rw [<- Zset.isSet_support_fromSet]
    simp; simp [S, DS1]
  · rw [fromSet_sub_sdiff _ _ (mono_S_i i j), S_sdiff_DS1]

lemma DS1_card (i j: ℕ):
    (DS1 i j).card = min i (j + 1) := by
  simp [DS1]
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_range]
  · intro a ha b hb h
    simp [Finset.mem_range] at ha hb
    have := (Prod.mk.inj h).1
    omega

lemma DS1_card_bound (i j: ℕ):
    (DS1 i j).card ≤ i := by
  rw [DS1_card]; apply Nat.min_le_left

lemma DS1_biUnion_i (i j: ℕ):
    (Finset.range (i+1)).biUnion (fun k => DS1 k j) = S i j := by
  ext ⟨a, b⟩; simp [DS1, S, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]; constructor
  · rintro ⟨k, hk, x, ⟨hx1, hx2⟩, rfl, rfl⟩; exact ⟨x, ⟨by omega, hx2⟩, by omega, by omega⟩
  · rintro ⟨x, ⟨hx1, hx2⟩, ha, rfl⟩; exact ⟨a + x + 1, by omega, x, ⟨by omega, hx2⟩, by omega, rfl⟩

-- `DS12 i j` contains all edges pointing to the new node `i` in `P_i`
--   that are exactly `j+1` hops long
-- `12` means `D` operates on both time dimensions
abbrev DS12 (i j: ℕ): Finset (ℕ × ℕ) :=
  if j + 1 ≤ i then {(i-j-1, i)} else ∅

lemma DS12_card (i j: ℕ):
    (DS12 i j).card = if j + 1 ≤ i then 1 else 0 := by
  simp [DS12]
  split_ifs <;> simp

lemma DS12_card_bound (i j: ℕ):
    (DS12 i j).card ≤ 1 := by
  rw [DS12_card]; split_ifs <;> simp

lemma DS12_DS2_eq:
    D (fun i j => Zset.fromSet (DS2 i j)) =
    (fun i j => Zset.fromSet (DS12 i j)) := by
  funext i j; rcases i with _ | i <;>
  simp [D, DS2, DS12]
  ext ⟨a ,b⟩; simp
  split_ifs <;> simp at * <;> omega

lemma DS12_DS1_eq i:
    (fun j => Zset.fromSet (DS12 i j)) =
    D (fun j => Zset.fromSet (DS1 i j)) := by
  have hm : Monotone (DS1 i) := by
    intro j1 j2 hj
    apply Finset.image_subset_image
    apply Finset.range_mono (by omega)
  rw [mono_D_sdiff (h := hm)]
  funext j; congr 1
  rcases j with _ | j
  · simp [DS12, DS1, delay]
    ext ⟨a, b⟩; simp [Finset.mem_image, Finset.mem_range]
    split_ifs with h <;> simp at * <;> omega
  · simp only [DS12]
    split_ifs with hj
    · ext ⟨a, b⟩
      simp only [Finset.mem_singleton, Prod.mk.injEq, DS1, delay, Nat.succ_ne_zero,
        ↓reduceIte, Nat.add_one_sub_one, Finset.mem_sdiff, Finset.mem_image,
        Finset.mem_range]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨⟨j + 1, by omega, by omega, rfl⟩, fun ⟨x, hx1, hx2, hx3⟩ => by omega⟩
      · rintro ⟨⟨x, hx1, rfl, rfl⟩, hns⟩
        have : x = j + 1 := by
          by_contra hne; exact hns ⟨x, by omega, rfl, rfl⟩
        subst this; constructor <;> omega
    · ext ⟨a, b⟩
      simp only [Finset.notMem_empty, DS1, delay, Nat.succ_ne_zero, ↓reduceIte,
        Nat.add_one_sub_one, Finset.mem_sdiff, Finset.mem_image, Finset.mem_range,
        Prod.mk.injEq, false_iff, not_and]
      rintro ⟨x, hx1, rfl, rfl⟩ hns
      exact hns ⟨x, by omega, rfl, rfl⟩

lemma delay_biUnion {A:Type}
  [DecidableEq A] (S: stream (Finset A)) (i: ℕ):
    (Finset.range (i+1)).biUnion (z⁻¹ S) =
    z⁻¹ (fun i => (Finset.range (i+1)).biUnion S) i := by
  rcases i with _ | i
  · simp [delay]
  · simp only [delay, Nat.succ_ne_zero, ↓reduceIte, Nat.add_one_sub_one]
    ext a; simp [Finset.mem_biUnion, Finset.mem_range]; constructor
    · rintro ⟨k, hk, ha⟩
      rcases k with _ | k
      · simp at ha
      · exact ⟨k, by omega, ha⟩
    · rintro ⟨k, hk, ha⟩
      exact ⟨k + 1, by omega, ha⟩

lemma nested_fun_delay_eq {A:Type} [Zero A]
  (S: stream (stream A)) (j: ℕ):
    (fun k => z⁻¹ S k j) = z⁻¹ (fun k => S k j) := by
  funext k; rcases k <;> simp

lemma delay_biUnion_nested_i {A:Type}
  [DecidableEq A] (S: stream (stream (Finset A))) (i j: ℕ):
    (Finset.range (i+1)).biUnion (fun k => z⁻¹ S k j) =
    z⁻¹ (fun i => (Finset.range (i+1)).biUnion (fun k => S k j)) i := by
  rw [nested_fun_delay_eq, delay_biUnion]

lemma lifted_delay_biUnion_i {A:Type}
  [DecidableEq A] (S: stream (stream (Finset A))) i j:
    (Finset.range (i+1)).biUnion (fun k => ↑↑z⁻¹ S k j) =
    ↑↑z⁻¹ (fun i j => (Finset.range (i+1)).biUnion (fun k => S k j)) i j := by
  simp; rcases j with _ | j
  · ext; simp [delay]
  · simp

lemma lifted_delay_biUnion_j {A:Type}
  [DecidableEq A] (S: stream (stream (Finset A))) i j:
    (Finset.range (j+1)).biUnion (↑↑z⁻¹ S i) =
    ↑↑z⁻¹ (fun i j => (Finset.range (j+1)).biUnion (S i)) i j := by
  simp; rcases j with _ | j
  · ext; simp [delay]
  · rw [delay_biUnion]

lemma DS12_biUnion_i (i j: ℕ):
    (Finset.range (i+1)).biUnion (fun k => DS12 k j) = DS2 i j := by
  ext ⟨a, b⟩; simp [DS12, DS2, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]; constructor
  · rintro ⟨k, hk, hm⟩
    split_ifs at hm with hj
    · simp at hm; omega
    · exact absurd hm (Finset.notMem_empty _)
  · rintro ⟨ha, rfl⟩
    exact ⟨a + j + 1, by omega, by simp; omega⟩

lemma DS12_biUnion_j (i j: ℕ):
    (Finset.range (j+1)).biUnion (DS12 i) = DS1 i j := by
  ext ⟨a, b⟩; simp [DS12, DS1, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]; constructor
  · rintro ⟨k, hk, hm⟩
    split_ifs at hm with hi
    · simp at hm; exact ⟨k, ⟨by omega, hk⟩, by omega, by omega⟩
    · exact absurd hm (Finset.notMem_empty _)
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl, rfl⟩
    exact ⟨x, hx2, by simp [show x + 1 ≤ i from by omega]; omega⟩

lemma JoinRes11_card_bound i j:
    (JoinRes (fun i _ => path i) (↑↑z⁻¹ (fun i j => DS12 i j)) i j).card ≤ 1 := by
  simp only [JoinRes]; rcases j with _ | j
  · simp [delay]
  · simp [delay, DS12]; split_ifs with h
    · simp [path]; rw [Finset.card_le_one]
      intro ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩ h1 ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩ h2
      simp at h1 h2
      obtain ⟨⟨k1, hk1, rfl, rfl⟩, rfl, rfl⟩ := h1
      obtain ⟨⟨k2, hk2, rfl, rfl⟩, rfl, rfl⟩ := h2
      simp; omega
    · simp

lemma JoinRes12_eq i j:
    JoinRes (fun i _ => Dis i) (z⁻¹ (↑↑z⁻¹ DS2)) i j = ∅ := by
  simp [JoinRes, Dis, DS2, delay]
  rcases i with _ | i
  · simp
  · rcases j with _ | j
    · simp
    · ext ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩; simp; omega

lemma JoinRes21_eq i j:
    JoinRes (↑↑δ0 path) (↑↑z⁻¹ (↑↑z⁻¹ DS1)) i j = ∅ := by
  simp [JoinRes, delay]
  rcases j with _ | j
  · simp [delay]
  · simp

lemma JoinRes22_eq i j:
    JoinRes (↑↑δ0 fun n ↦ Dis n) (z⁻¹ (↑↑z⁻¹ (↑↑z⁻¹ S))) i j = ∅ := by
  simp [JoinRes, delay]
  rcases j with _ | j
  · split_ifs <;> simp [delay]
  · simp

lemma opt_c1_map_card_bound i j:
    (Finset.image (fun x => (x.1.1, x.2.2))
      (JoinRes (fun i _ => path i) (↑↑z⁻¹ DS12) i j)).card ≤ 1 := by
  exact le_trans Finset.card_image_le (JoinRes11_card_bound i j)

lemma opt_join_res i j:
    ↑↑δ0 (fun n ↦ Dis n) i j ∪
    Finset.image (fun x => (x.1.1, x.2.2))
      (JoinRes (fun i _ ↦ path i) (↑↑z⁻¹ DS12) i j) =
    DS12 i j := by
  rcases j with _ | j
  · simp [JoinRes, delay, DS12, Dis]
    split_ifs with h1 h2 <;> first | omega | rfl
  · ext ⟨a, b⟩
    simp [JoinRes, DS12, path, delay, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_product, Finset.mem_range, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs with h1 h2
    · simp; constructor
      · rintro ⟨ha, h3, rfl⟩; omega
      · rintro ⟨rfl, rfl⟩; omega
    · simp; rintro ha h3 rfl; omega
    · omega
    · simp

lemma H_res i j:
    DS2 i j \ ↑↑z⁻¹ S i j = DS2 i j := by
  apply Finset.sdiff_eq_self_iff_disjoint.mpr
  simp [Finset.disjoint_left, DS2, S]
  intro a ha
  rcases j with _ | j
  · simp [delay]
  · change (a, a + (j + 1) + 1) ∉ S i j
    simp only [S, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, Prod.mk.injEq, not_exists]
    intro x ⟨hx1, k2, hk2, h1, h2⟩; omega

abbrev cjoin {ns: Bool}: Ckt ([Z[ℕ × ℕ]]v ×ᵥ [Z[ℕ × ℕ]]v) ([Z[(ℕ × ℕ) × (ℕ×ℕ)]]v) ns :=
  zjoin Prod.snd Prod.fst

instance c0_IncCkt: IncCkt c0 := by unfold c0; infer_instance

def c1 : Ckt ([Z[ℕ × ℕ]]v ×ᵥ [Z[ℕ × ℕ]]v) ([Z[ℕ × ℕ]]v) 1 :=
  (c1st &&c lifted_bilinear_opt (cjoin) >>c zmap (fun (x, y) => (x.1, y.2))) >>c
    cadd >>c lifted_incr_dist (c₂ HBinaryNode)

lemma hc1:
    pushLifting (incOpt c0) = c1:= by
  unfold c0 c1;
  simp [cjoin, IncBinary.opt, IncUnary.opt, pushLifting]

instance c1_IncCkt: IncCkt c1 := by
  unfold c1 lifted_bilinear_opt lifted_incr_dist
  infer_instance

lemma opt_c1_eq:
  incOpt c1 =
  (c1st &&c lifted_bilinear_opt (bilinear_opt cjoin) >>c zmap (fun (x, y) => (x.1, y.2))) >>c
    cadd >>c (lifted_incr_dist (cΔ (c₂ HBinaryNode))) := rfl

lemma bodyOutput_eq:
    ↑↑(bodyOutput (A:=[Z[ℕ×ℕ]]v) (B:=[Z[ℕ×ℕ]]v) R) is = (fun i j => Zset.fromSet (DS2 i j)) := by
  funext i; simp; rw [<- DS2_eq]
  simp [bodyOutput]
  apply congr; simp
  unfold f; simp; rw [fs_eq]

theorem loop_c1_HoareT:
    HoareT
      (fun x => x = ↑↑δ0 (fun n => Zset.fromSet (Dis n)))
      (cloop2 (incOpt c1))
      (fun y => y = (fun i j => Zset.fromSet (DS12 i j))) := by
  apply HoareT_conseq_pre (P':= fun x => x = ↑↑δ0 (D is))
  case hp =>
    simp; apply congr; simp
    rw [Dis_eq]
  apply HoareT_conseq_post
  apply opt_lifted_body_HoareT (hf := c0_hf)
    (htv := by intros; apply c0_ht)
    (hc1 := hc1)
  simp; rw [bodyOutput_eq]
  rw [DS12_DS2_eq]

theorem loop_c1_HoareI2:
    HoareI2
      (fun x => x = ↑↑δ0 (fun n => Zset.fromSet (Dis n)))
      (cloop2 (incOpt c1))
      (fun _ => True)
      (fun n => n + 2) := by
  apply HoareI2_conseq_pre (P':= fun x => x = ↑↑δ0 (D is))
  case hp =>
    simp; apply congr; simp
    rw [Dis_eq]
  apply HoareI2_bound_mono
  apply opt_lifted_body_HoareI2 (hf := c0_hf)
    (htv := by intros; apply c0_ht)
    (hei := c0_hei)
    (hc1 := hc1)
    (hfa := by intros; apply c0_hfa)
  intro n; rcases n <;> simp

lemma bilinear_join_HoareR
  (x1 x2: SOType 1 Z[ℕ × ℕ]) (S1 S2 IS1 IS2: SOType 1 (Finset (ℕ × ℕ)))
  (h1s: ∀ i j, (x1 i j).support = S1 i j)
  (h2s: ∀ i j, (x2 i j).support = S2 i j)
  (h1b: ∀ i j, (x1 i j).IsBag)
  (h2b: ∀ i j, (x2 i j).IsBag)
  (hIs1: ∀ i j, (Finset.range (i+1)).biUnion (fun k => S1 k j) = IS1 i j)
  (hIs2: ∀ i j, (Finset.range (i+1)).biUnion (fun k => S2 k j) = IS2 i j):
    HoareR
      (fun z ↦ z = sprod2 (x1, x2))
      (bilinear_opt (cjoin (ns:=1)))
      (fun y =>
        (∀ (i j : ℕ), DFinsupp.support (y i j) =
          JoinRes IS1 S2 i j ∪ JoinRes S1 (z⁻¹ IS2) i j) ∧
         ∀ (i j : ℕ), Zset.IsBag (y i j))
      (fun i j =>
        ((IS1 i j).card + 1) * ((S2 i j).card + 1) +
        ((S1 i j).card + 1) * ((IS2 (i - 1) j).card + 1) +
        (IS1 (i - 1) j).card + 2 * (IS2 i j).card +
        (JoinRes IS1 S2 i j).card + (JoinRes S1 (z⁻¹ IS2) i j).card) := by
  have jeq1: ∀ i j, {t ∈ IS1 i j ×ˢ S2 i j | t.1.2 = t.2.1} = JoinRes IS1 S2 i j := by
    intro i j; simp [JoinRes]
  have jeq2: ∀ i j,
      {t ∈ S1 i j ×ˢ z⁻¹ IS2 i j | t.1.2 = t.2.1} =
      JoinRes S1 (z⁻¹ IS2) i j := by
    intro i j; simp [JoinRes]
  unfold bilinear_opt
  apply HoareR_conseq_post; apply HoareR_weaken_bound
  apply HoareR_seq
  apply HoareR_par'
  · apply HoareR_seq; apply HoareR_par'
    · apply HoareR_seq; apply HoareR_fst; simp
      apply HoareR_I_support_ns1 (h1s:=h1s) (hres:=hIs1)
      tauto
    · apply HoareR_snd
    simp; apply HoareR_sintro; simp
    intro v x1 _ hx1s hx1b; subst v
    apply HoareR_join_support_ns1 <;> tauto
  · apply HoareR_seq; apply HoareR_par'
    · apply HoareR_fst
    · apply HoareR_seq; apply HoareR_seq; apply HoareR_snd; simp
      apply HoareR_I_support_ns1 (h1s:=h2s) (hres:=hIs2) (h1b:=h2b)
      apply HoareR_sintro; intros
      apply HoareR_delay_support_ns1 <;> tauto
    simp; apply HoareR_sintro; simp
    intro v x1 x2 _ _ hx2s hx2b; subst v x1
    apply HoareR_join_support_ns1 <;> tauto
  simp; apply HoareR_sintro; simp
  intro v x1 x2; intros; subst v
  apply HoareR_add_support_ns1 <;> tauto
  · simp_rw [jeq1, jeq2]
    intro i j; simp; rcases i <;> simp <;>
    nlinarith
  · simp_rw [jeq1, jeq2]; tauto

lemma bilinear_join_HoareR_1
  (x1 x2: SOType 1 Z[ℕ × ℕ])
  (h1s: ∀ i j, (x1 i j).support = Dis i)
  (h2s: ∀ i j, (x2 i j).support = ↑↑z⁻¹ (fun i j ↦ DS12 i j) i j)
  (h1b: ∀ i j, (x1 i j).IsBag)
  (h2b: ∀ i j, (x2 i j).IsBag):
    HoareR
      (fun z ↦ z = sprod2 (x1, x2))
      (bilinear_opt (cjoin (ns:=1)))
      (fun y =>
        (∀ (i j : ℕ), (y i j).support = JoinRes (fun i _ => path i) (↑↑z⁻¹ DS12) i j) ∧
         ∀ (i j : ℕ), Zset.IsBag (y i j))
      (fun i _ => 7 * (i + 1)) := by
  apply HoareR_conseq_post; apply HoareR_weaken_bound
  apply bilinear_join_HoareR
    (h1s:=h1s) (h2s:=h2s) (h1b:=h1b) (h2b:=h2b)
  case hIs1 =>
    intros; rw [Dis_biUnion]
  case hIs2 =>
    intros i j; rewrite [lifted_delay_biUnion_i]
    have h := funext₂ fun i j => DS12_biUnion_i i j
    rw [h]
  case hq =>
    simp; intro x h1 h2; simp [h2]
    intro i j; specialize h1 i j
    rw [JoinRes12_eq] at h1
    simp at h1; tauto
  case hr =>
    intro i j; simp; rw [JoinRes12_eq]
    have := Dis_card_bound i
    rcases j with _ | j <;> simp
    · have := JoinRes11_card_bound i 0
      omega
    · have := DS12_card_bound i j
      have := DS2_card_bound (i-1) j
      have := DS2_card_bound i j
      have := JoinRes11_card_bound i (j+1)
      have : (i + 1) * ((DS12 i j).card + 1) ≤ 2 * (i + 1) := by
         rw [mul_comm]; apply mul_le_mul <;> omega
      have : ((Dis i).card + 1) * ((DS2 (i - 1) j).card + 1) ≤ 2 * (i+1) := by
        apply mul_le_mul <;> omega
      omega

-- This is the dominant cost for the optimized join
lemma bilinear_join_HoareR_2
  (x1 x2: SOType 1 Z[ℕ × ℕ])
  (h1s: ∀ i j, (x1 i j).support = ↑↑δ0 (fun n ↦ Dis n) i j)
  (h2s: ∀ i j, (x2 i j).support = ↑↑z⁻¹ (↑↑z⁻¹ DS1) i j)
  (h1b: ∀ i j, (x1 i j).IsBag)
  (h2b: ∀ i j, (x2 i j).IsBag):
    HoareR
      (fun z ↦ z = sprod2 (x1, x2))
      (bilinear_opt (cjoin (ns:=1)))
      (fun y =>
        (∀ (i j : ℕ), (y i j).support = ∅) ∧
         ∀ (i j : ℕ), Zset.IsBag (y i j))
      (fun i _ => 3 * (i + 1)^2) := by
  apply HoareR_conseq_post; apply HoareR_weaken_bound
  apply bilinear_join_HoareR
    (h1s:=h1s) (h2s:=h2s) (h1b:=h1b) (h2b:=h2b)
  case hIs1 =>
    intros; rewrite [delta_biUnion_i]
    have := funext fun n => Dis_biUnion n
    rw [this]
  case hIs2 =>
    intros i j; rewrite [lifted_delay_biUnion_i]
    iterate 2 apply congr (h₂:= rfl)
    apply congr (h₁:=rfl)
    funext i j
    rewrite [lifted_delay_biUnion_i]
    have h := funext₂ fun i j => DS1_biUnion_i i j
    rw [h]
  case hq =>
    simp; intro x h1 h2; simp [h2]
    intro i j; specialize h1 i j
    rw [JoinRes21_eq, JoinRes22_eq] at h1
    simp at h1; tauto
  case hr =>
    intro i j; simp
    rw [JoinRes21_eq, JoinRes22_eq]; simp
    have := Dis_card_bound i
    rcases j with _ | j <;> simp
    · rw [add_pow_two]; simp
      omega
    rcases j with _ | j <;> simp
    · rw [pow_two]; nlinarith
    have := S_card_bound' (i-1) j
    have := S_card_bound' i j
    have := DS1_card_bound i j
    have h1 : (i - 1) * (i - 1 + 1) ≤ i * (i + 1) := Nat.mul_le_mul (by omega) (by omega)
    rw [pow_two]; nlinarith

lemma lifted_bilinear_HoareR
  (x1 x2: SOType 1 Z[ℕ × ℕ])
  (h1s: ∀ i j, (x1 i j).support = ↑↑δ0 (fun n ↦ Dis n) i j)
  (h2s: ∀ i j, (x2 i j).support = ↑↑z⁻¹ (DS12) i j)
  (h1b: ∀ i j, (x1 i j).IsBag)
  (h2b: ∀ i j, (x2 i j).IsBag):
    HoareR
      (fun z ↦ z = sprod2 (x1, x2))
      (lifted_bilinear_opt (bilinear_opt cjoin))
      (fun y =>
        (∀ i j, (y i j).support = JoinRes (fun i _ ↦ path i) (↑↑z⁻¹ DS12) i j) ∧
        ∀ i j, Zset.IsBag (y i j))
      (fun i _ => 3 * (i+3)^2) := by
  unfold lifted_bilinear_opt
  apply HoareR_conseq_post
  apply HoareR_weaken_bound
  apply HoareR_seq
  apply HoareR_par'
  · apply HoareR_seq; apply HoareR_par'
    · apply HoareR_seq; apply HoareR_fst; simp
      apply HoareR_lifted_I_support
        (h1s := h1s) (h1b:=h1b)
        (hres := by apply delta_biUnion_j)
    · apply HoareR_snd
    simp; apply HoareR_sintro; simp
    intro v x1 _ hx1s hx1b; subst v
    apply bilinear_join_HoareR_1 <;> tauto
  · apply HoareR_seq; apply HoareR_par'
    · apply HoareR_fst
    · apply HoareR_seq; apply HoareR_seq
      apply HoareR_snd; simp
      apply HoareR_lifted_I_support
        (h1s := h2s)
        (h1b := h2b)
      case hres =>
        intro i j; rewrite [lifted_delay_biUnion_j]
        have h := funext₂ fun i j => DS12_biUnion_j i j
        rw [h]
      apply HoareR_sintro; intros
      apply HoareR_lifted_delay_support_ns1 <;> tauto
    apply HoareR_sintro
    rintro v ⟨y1, y2, _, _, h2s, h2b⟩; subst v y1
    simp; apply bilinear_join_HoareR_2 <;> tauto
  apply HoareR_sintro;
  rintro v ⟨y1, y2, _, ⟨h1s, h1b⟩, ⟨h2s, h2b⟩⟩; subst v
  simp; apply HoareR_add_support_ns1 <;> tauto
  case hq => simp
  case hr =>
    intro i j; simp
    have := Dis_card_bound i
    have := JoinRes11_card_bound i j
    rcases j with _ | j <;> simp
    · nlinarith
    have := DS12_card_bound i j
    have := DS1_card_bound i j
    rcases j with _ | j <;> simp
    · nlinarith
    have := DS1_card_bound i j
    nlinarith

lemma lifted_incr_dist_HoareR
  (x: SOType 1 Z[ℕ × ℕ])
  (hs: ∀ i j, (x i j).support = DS12 i j)
  (hb: ∀ i j, (x i j).IsBag):
    HoareR
      (fun z => z = x)
      (lifted_incr_dist (cΔ c₂ HBinaryNode))
      (fun _ => True)
      (fun i _ => 3 * (i+3)^2) := by
  apply HoareR_weaken_bound
  unfold lifted_incr_dist cΔ
  apply HoareR_seq
  apply HoareR_par'
  · apply HoareR_seq
    apply HoareR_lifted_I_support
      (h1s := hs) (h1b:= hb)
      (hres := by apply DS12_biUnion_j)
    apply HoareR_sintro; simp
    intro x hs hb
    apply HoareR_lifted_delay_support_ns1 <;> tauto
  · apply HoareR_id
  apply HoareR_sintro; simp [-HBinaryNode, - lifting_eq]
  intro v x1 _ h1s h1b; subst v
  apply HoareR_seq; apply HoareR_seq
  apply HoareR_I_sprod2_support
    (h1s := h1s) (h1b := h1b)
    (h2s := hs) (h2b := hb)
  case his1 =>
    intros; rewrite [lifted_delay_biUnion_i]
    have := funext₂ fun i j => DS1_biUnion_i i j
    rw [this]
  case his2 =>
    intros; rw [DS12_biUnion_i]
  apply HoareR_sintro; simp [-HBinaryNode, - lifting_eq]
  intro v x1 x2 _ h1s h1b h2s h2b; subst v
  apply HoareR_H_support_ns1 <;> tauto
  apply HoareR_sintro; intro v h
  have h': ∀ i j, v i j = Zset.fromSet (DS2 i j) := by
    intro i j; specialize h i j
    rw [h, H_res]
  apply HoareR_conseq_post (hq := by tauto)
  apply HoareR_ZSB_D_mono
  case h =>
    simp [ZSB]; intro i j
    simp [Zset.size]
    rewrite [h']
    simp; rfl
  case hm =>
    intro a b h t; simp
    simp_rw [DS2_card]; omega
  case hr =>
    intro i j; simp
    have := DS12_card_bound i j
    have := DS2_card_bound i j
    have := DS2_card_bound (i-1) j
    have := DS1_card_bound i j
    have := DS1_card_bound (i-1) j
    rcases j with _ | j <;> simp
    · have : i - 1 ≤ i := Nat.sub_le i 1; nlinarith
    have := DS1_card_bound i j
    have := S_card_bound' (i-1) j
    have := S_card_bound' i j
    have : i - 1 ≤ i := Nat.sub_le i 1
    have : (i - 1) * (i - 1 + 1) ≤ i * (i + 1) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith

theorem loop_c1_HoareR:
    HoareR
      (fun x => x = ↑↑δ0 (fun n => Zset.fromSet (Dis n)))
      (cloop2 (incOpt c1))
      (fun y => y = (fun i j => Zset.fromSet (DS12 i j)))
      (fun i _ => 6 * (i + 3)^2 + 4) := by
  apply HoareR_weaken_bound
  apply HoareR_lifted_loop
  case ht => apply loop_c1_HoareT
  case hs =>
    simp; intro i j
    simp [VType_space, Zset.size]; rfl
  simp; rw [opt_c1_eq]
  set x1 := ↑↑δ0 fun n ↦ Zset.fromSet (Dis n)
  set x2 := ↑↑z⁻¹ fun i j ↦ Zset.fromSet (DS12 i j)
  have h1s : ∀ i j,
      (x1 i j).support =
      (↑↑δ0 (fun n => Dis n)) i j := by
    intro i j; rcases j <;> simp [x1]
  have h1b : ∀ i j, (x1 i j).IsBag := by
    intro i j; rcases j <;> simp [x1]
  have h2s : ∀ i j,
      (x2 i j).support =
      (↑↑z⁻¹ (fun i j => DS12 i j)) i j := by
    intro i j; rcases j <;> simp [x2]
  have h2b : ∀ i j, (x2 i j).IsBag := by
    intro i j; rcases j <;> simp [x2]
  repeat apply HoareR_seq
  apply HoareR_par'
  · apply HoareR_fst
  · apply HoareR_seq
    apply lifted_bilinear_HoareR <;> tauto
    apply HoareR_sintro; intros
    apply HoareR_map_support_ns1 <;> tauto
  apply HoareR_sintro; simp
  intro v x x2 _ _ h2s h2b; subst v x
  apply HoareR_add_support_ns1 <;> tauto
  apply HoareR_sintro; rintro v ⟨hs, hvb⟩
  have hvs: ∀ i j,
      (v i j).support = DS12 i j := by
    intro i j; specialize hs i j
    rw [opt_join_res] at hs; tauto
  clear hs h1s h1b h2s h2b
  apply lifted_incr_dist_HoareR <;> tauto
  case hr =>
    intro i j; simp
    have := JoinRes11_card_bound i j
    have := DS12_card_bound i j
    have := opt_c1_map_card_bound i j
    rcases j with _ | j <;> simp
    · have := Dis_card_bound i
      nlinarith
    nlinarith

-- The optimized query's cost is `O(n^3)` for the iteration `n`
-- The dominant cost is introduced by the two `I` with `S`-like output in the optimized join and before the `H`. The cost of such an operation is `O(n^2)`.
-- Note that we DO NOT do in-place update by default. With in-place optimizations for operations like addition and integration, we can reduce its cost to `O(n)`, leading to an overall cost of `O(n^2)`.
theorem opt_query_HoareR:
    HoareR
      (fun x => x = D is)
      (opt_query c1)
      (fun _ => True)
      (fun n => 6 * (n+4)^3) := by
  rw [Dis_eq]
  apply HoareR_conseq_post (hq:= by tauto)
  apply HoareR_weaken_bound
  apply HoareR_bracket
  case h.hr =>
    simp; apply loop_c1_HoareR
  case hi =>
    simp; apply loop_c1_HoareI2
  case hb =>
    simp; intro i; simp
    intro j hj; simp
    simp [DS12]
    split_ifs; omega
    rfl
  case hic =>
    simp; intro i
    apply HoareR_weaken_bound (r':= fun _ => 2*i+1)
    apply HoareR_conseq_post (hq := by tauto)
    apply HoareR_Zset_I_ns0
    intro j; simp [Zset.size]
    rewrite [DS12_DS1_eq]; simp
    have := DS12_card_bound i j
    have := DS1_card_bound i j
    rcases j with _ | j <;> simp
    · nlinarith
    have := DS1_card_bound i j
    nlinarith
  case hr =>
    intro n; simp [-integral_succ]
    apply le_trans
    apply le_I_le
    intro t ht; simp; rfl
    nlinarith

end GraphExample

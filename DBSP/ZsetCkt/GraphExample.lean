import DBSP.ZsetCkt.ZsetCkt
import DBSP.ZsetCkt.ZsetHoareR
import DBSP.Practical.Expressiveness

namespace GraphExample
open CktBasic
open Datalog

-- The lifted scalar circuit `c0`
def c0 : Ckt ([Z[ℕ × ℕ]]v ×ᵥ [Z[ℕ × ℕ]]v) ([Z[ℕ × ℕ]]v) 0 :=
  (c1st &&c zjoin Prod.snd Prod.fst >>c zmap (fun (x, y) => (x.1, y.2))) >>c
    cadd >>c zdistinct

lemma c0_LiftedScalar: LiftedScalar c0 := by
  unfold c0; decide

lemma c0_ht x: IntConv c0 x := by
  apply IntConv_LiftedScalar
  apply c0_LiftedScalar

lemma c0_hei x n (h: ExtFP1 c0 x n): IntFP1 c0 x n := by
  apply LiftedScalar_ExtFP1_IntFP1
  apply c0_LiftedScalar
  assumption

def R: (Z[ℕ × ℕ] × Z[ℕ × ℕ]) -> Z[ℕ × ℕ] :=
  fun (E, R0) =>
    let p := equiJoin Prod.snd Prod.fst E R0
    let R1 := Zset.map (fun (x, y) => (x.1, y.2)) p
    Zset.distinct (E + R1)

lemma c0_hf:
    DenoteLiftedScalar c0 R := by
  simp [DenoteLiftedScalar, c0, denote, liftO]
  funext x i; simp [R]

open Zset in
@[simp]
lemma R_0 (S: Finset (ℕ × ℕ)):
    R (Zset.fromSet S, 0) = Zset.fromSet S := by
  simp only [R, equiJoin_0_r, map_zpp, add_zero]
  exact distinct_set_id _ (by intro a ha; rw [elem_fromSet] at ha; simp [ha])

-- The specific input "Path n" `P_n`
def path (n: ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n).image fun i => (i, i+1)

@[simp]
lemma path_card (n: ℕ):
    (path n).card = n := by
  simp [path]
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_range]
  · intro a b h; simp at h; exact h

def is : stream (Z[ℕ × ℕ]) :=
  fun n => Zset.fromSet (path n)

@[simp]
lemma R_is_0 (i: ℕ):
    R (is i, 0) = is i := by
  simp [is]

@[simp]
lemma is_support (n: ℕ):
    (is n).support = path n := by
  simp [is]

@[simp]
lemma is_size (n: ℕ):
    (is n).size = n := by
  simp [is, Zset.size]

-- `S i j` contains all edges in `P_i` that are at most `j+1` hops long
abbrev S (i j: ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (min i (j+1))).biUnion fun x =>
    (Finset.range (i-x)).image fun k => (k, k + x + 1)

lemma mono_D_sdiff {A: Type} [DecidableEq A]
  (s: ℕ -> Finset A) (h: Monotone s):
    D (fun i => Zset.fromSet (s i)) =
    (fun i => Zset.fromSet
      (s i \ z⁻¹ s i)) := by
  funext i; rcases i with _ | i <;> simp [D]
  ext x; rw [Zset.sub_apply]
  simp only [Zset.fromSet_apply, Finset.mem_sdiff]
  by_cases h1 : x ∈ s (i + 1) <;> by_cases h2 : x ∈ s i <;> simp [h1, h2]
  exact absurd (h (Nat.le_succ i) h2) h1

lemma mono_S (i: ℕ):
    Monotone (S i) := by
  intro j1 j2 hj
  apply Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono (by omega))

-- `DS2 i j` contains all edges that are exactly `j+1` hops long in `P_i`
-- `2` means `D` operates on the second time dimension
abbrev DS2 (i j: ℕ): Finset (ℕ × ℕ) :=
  (Finset.range (i-j)).image fun k => (k, k + j + 1)

lemma DS2_eq (i: ℕ):
    D (fun j => Zset.fromSet (S i j)) =
    (fun j => Zset.fromSet (DS2 i j)) := by
  rw [mono_D_sdiff (h:= mono_S i)]
  funext j; rw [<- Zset.isSet_support_fromSet]; simp
  rcases j with _ | j
  · simp [DS2, S]; ext ⟨a, b⟩; simp; omega
  · simp only [delay, Nat.succ_ne_zero, ↓reduceIte, Nat.add_one_sub_one]
    ext ⟨a, b⟩; simp [DS2, S, Finset.mem_sdiff]; constructor
    · rintro ⟨⟨x, ⟨hx1, hx2⟩, k, hk, rfl⟩, hns⟩
      have hx : x = j + 1 := by
        by_contra hne
        exact hns x hx1 (by omega) k rfl
      subst hx; exact ⟨k, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      constructor
      · exact ⟨j + 1, ⟨by omega, by omega⟩, by omega, rfl⟩
      · intro x hx1 hx2 _ h; omega

lemma DS2_card (i j: ℕ):
    (DS2 i j).card = i - j := by
  simp [DS2]
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro a b h; exact (Prod.mk.inj h).1

lemma DS2_card_bound (i j: ℕ):
    (DS2 i j).card ≤ i := by
  rw [DS2_card]; omega

private lemma sum_decr (c n : ℕ) (h : n ≤ c) :
    2 * ∑ x ∈ Finset.range n, (c - x) = n * (2 * c + 1 - n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih (by omega : k ≤ c)]
    zify [show k ≤ 2 * c + 1 from by omega, show k ≤ c from by omega,
          show k + 1 ≤ 2 * c + 1 from by omega]
    ring

lemma S_card (i j: ℕ):
    (S i j).card =
    if j + 1 ≤ i then (2 * i - j) * (j + 1) / 2 else i * (i + 1) / 2  := by
  simp only [S, Finset.card_biUnion]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (min i (j + 1))) : Set ℕ)
      (fun x => (Finset.range (i - x)).image fun k => (k, k + x + 1)) := by
    intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hxa hxb
    simp only [Finset.mem_image, Finset.mem_range] at hxa hxb
    obtain ⟨k1, _, rfl⟩ := hxa
    obtain ⟨k2, _, hk2⟩ := hxb
    exact absurd (show a = b from by have := Prod.mk.inj hk2; omega) hab
  rw [Finset.card_biUnion hdisj]
  have hinj : ∀ (n : ℕ), Function.Injective fun k => (k, k + n + 1) := by
    intro n a b h; exact (Prod.mk.inj h).1
  simp_rw [Finset.card_image_of_injective _ (hinj _), Finset.card_range]
  split_ifs with h
  · rw [min_eq_right h]
    have h2 := sum_decr i (j + 1) h
    rw [show 2 * i + 1 - (j + 1) = 2 * i - j from by omega] at h2
    rw [show (2 * i - j) * (j + 1) = (j + 1) * (2 * i - j) from by ring]
    omega
  · push_neg at h
    rw [min_eq_left (by omega : i ≤ j + 1)]
    have h2 := sum_decr i i le_rfl
    rw [show 2 * i + 1 - i = i + 1 from by omega] at h2
    omega

lemma S_card_bound (i j: ℕ):
    (S i j).card ≤ i * (j+1) := by
  rw [S_card]
  split_ifs
  · apply Nat.div_le_of_le_mul
    nlinarith [Nat.sub_le (2 * i) j]
  · apply Nat.div_le_of_le_mul
    nlinarith

lemma S_card_bound' (i j: ℕ):
    (S i j).card ≤ i * (i+1) := by
  rw [S_card]
  split_ifs
  · apply Nat.div_le_of_le_mul
    nlinarith [Nat.sub_le (2 * i) j]
  · apply Nat.div_le_of_le_mul
    nlinarith

lemma S_card' (i j: ℕ):
    (S i j).card =
    if j ≤ i then (2 * i - j) * (j + 1) / 2 else i * (i + 1) / 2  := by
  simp [S_card]; split_ifs <;> try omega
  have : j = i := by omega
  subst this; simp [two_mul]

lemma S_size (i j: ℕ):
    (Zset.fromSet (S i j)).size =
    if j + 1 ≤ i then (2 * i - j) * (j + 1) / 2 else i * (i + 1) / 2  := by
  simp [Zset.size, Zset.fromSet_support, S_card]

lemma c0_map_res (i j: ℕ):
    Finset.image (fun x ↦ (x.1.1, x.2.2)) ({t ∈ path i ×ˢ S i j | t.1.2 = t.2.1}) = S i (j + 1) \ path i := by
  ext x; simp [path]
  constructor
  · rintro ⟨a, _, _, _, ⟨⟨⟨⟨ha, rfl⟩, a', ⟨ha'i, ha'j⟩, ha1, rfl⟩, rfl⟩, rfl⟩⟩
    exact ⟨⟨a' + 1, ⟨by omega, by omega⟩, a, by omega, by ext <;> omega⟩,
           by intro x hx h; have := Prod.mk.inj h; omega⟩
  · rintro ⟨⟨a', ⟨ha'1, ha'2⟩, k, hk, rfl⟩, hpath⟩
    rcases a' with _ | a'
    · exfalso; exact hpath k (by omega) rfl
    · exact ⟨k, k + 1, k + 1, k + a' + 2, ⟨⟨⟨⟨by omega, rfl⟩, a', ⟨by omega, by omega⟩, by omega, by omega⟩, rfl⟩, rfl⟩⟩

lemma c0_union_res (i j: ℕ):
    path i ∪ Finset.image (fun x ↦ (x.1.1, x.2.2)) ({t ∈ path i ×ˢ S i j | t.1.2 = t.2.1}) = S i (j + 1) := by
  rw [c0_map_res]
  apply Finset.union_sdiff_of_subset
  intro x hx
  simp [path] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  simp; omega

private lemma path_sub_S (i j: ℕ): path i ⊆ S i (j + 1) := by
  intro x hx
  simp [path] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  simp; omega

lemma c0_map_res_card (i j: ℕ):
    (S i (j + 1) \ path i).card = (S i (j + 1)).card - i := by
  rw [Finset.card_sdiff (path_sub_S i j), path_card]

lemma c0_join_res_card (i j: ℕ):
    {t ∈ path i ×ˢ S i j | t.1.2 = t.2.1}.card =
    (S i (j + 1)).card - i  := by
  have hinj : Set.InjOn (fun x : (ℕ × ℕ) × (ℕ × ℕ) => (x.1.1, x.2.2))
      ({t ∈ path i ×ˢ S i j | t.1.2 = t.2.1} : Finset _) := by
    intro ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩ h1 ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩ h2 heq
    simp [path] at h1 h2
    obtain ⟨⟨⟨k1, _, rfl, rfl⟩, _⟩, rfl⟩ := h1
    obtain ⟨⟨⟨k2, _, rfl, rfl⟩, _⟩, rfl⟩ := h2
    simp at heq; ext <;> simp <;> omega
  rw [← Finset.card_image_of_injOn hinj, c0_map_res, c0_map_res_card]

open Zset in
lemma fs_eq (i: ℕ):
    funcIterStream (fun r => R (is i, r)) (is i) =
    fun j => Zset.fromSet (S i j) := by
  funext j
  induction' j with j ih
  · simp [is, path]
    ext x; simp
    rcases i <;> simp
  · unfold funcIterStream at ih ⊢
    rw [Function.iterate_succ_apply', ih]
    nth_rewrite 1 [R]; simp
    have hb1: (is i).IsBag := by simp [is]
    have hb2: (Zset.fromSet (S i j)).IsBag := by simp
    have hb3: (equiJoin Prod.snd Prod.fst (is i) (Zset.fromSet (S i j))).IsBag := by
      apply equiJoin_pos <;> tauto
    have hb4: (Zset.map (fun x ↦ (x.1.1, x.2.2)) (equiJoin Prod.snd Prod.fst (is i) (Zset.fromSet (S i j)))).IsBag := by
      apply map_pos; tauto
    rw [<- isSet_support_fromSet]; simp
    rw [<- union, <- union_eq, isBag_union_support] <;> try tauto
    rw [isBag_map_support (h:=by tauto)]
    rw [equiJoin_support]; simp
    rw [c0_union_res]

lemma c0_hfa (i: ℕ):
    FixedAt (fun r => R (is i, r)) 0 i := by
  rcases i with _ | i
  · simp [FixedAt, is]; symm
    rw [<- Zset.isSet_support_fromSet]
    simp [path]
  · rw [FixedAt_funcIterStream_iff]
    rw [funcIterStream_0_delay, FixAfter1_delay_succ]
    simp; rw [fs_eq]
    intro j hj; simp
    rw [<- Zset.isSet_support_fromSet]; simp [S]
    rw [show min i j = i by omega]

open Zset in
theorem c0_HoareR (i: ℕ):
    HoareR
      (fun z ↦ z = sprod (fun _ ↦ is i, z⁻¹ fun j ↦ Zset.fromSet (S i j)))
      c0
      (fun _ ↦ True)
      (fun j => (i+3)^2 * (j+1)) := by
  unfold c0
  apply HoareR_weaken_bound
  apply HoareR_conseq_post (hq:=by tauto)
  have h1s := is_support i
  have h1b : (is i).IsBag := by simp [is]
  have h2s : ∀ j, (z⁻¹ (fun j => Zset.fromSet (S i j)) j).support =
      if j = 0 then ∅ else S i (j-1) := by
    intro j; rcases j <;> simp
  have h2b : ∀ j, (z⁻¹ (fun j => Zset.fromSet (S i j)) j).IsBag := by
    intro j; rcases j <;> simp
  apply HoareR_seq; apply HoareR_seq
  apply HoareR_par'
  · apply HoareR_fst
  · apply HoareR_seq
    apply HoareR_join_support_ns0 <;> try tauto
    apply HoareR_sintro; intros
    apply HoareR_map_support_ns0 <;> tauto
  simp
  apply HoareR_sintro; rintro v ⟨y1, ⟨y2, ⟨_, ⟨_, _⟩⟩⟩⟩
  subst v y1
  apply HoareR_add_support_ns0 <;> try tauto
  apply HoareR_sintro; intros
  apply HoareR_distinct_support_ns0 <;> tauto
  · intro j; rcases j with _ | j <;> simp
    · nlinarith
    · rw [c0_union_res, c0_map_res, c0_join_res_card, c0_map_res_card]
      nth_rw 1 [S_card]
      simp_rw [S_card']
      split_ifs
      · have hA : (2 * i - j) * (j + 1) / 2 ≤ i * (j + 1) :=
          Nat.div_le_of_le_mul (by
            calc (2 * i - j) * (j + 1) ≤ 2 * i * (j + 1) :=
                    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
              _ = 2 * (i * (j + 1)) := by ring)
        have hB : (2 * i - (j + 1)) * (j + 1 + 1) / 2 ≤ i * (j + 1 + 1) :=
          Nat.div_le_of_le_mul (by
            calc (2 * i - (j + 1)) * (j + 1 + 1) ≤ 2 * i * (j + 1 + 1) :=
                    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
              _ = 2 * (i * (j + 1 + 1)) := by ring)
        nlinarith [Nat.mul_le_mul_left i hA, Nat.sub_le ((2 * i - (j + 1)) * (j + 1 + 1) / 2) i]
      · have h := Nat.div_le_self (i * (i + 1)) 2
        nlinarith [Nat.mul_le_mul_left i h, Nat.sub_le (i * (i + 1) / 2) i]

theorem body_HoareR (i: ℕ):
    HoareR
      (fun x => x = δ0 (is i))
      (body c0)
      (fun y => y = D (fun j => Zset.fromSet (S i j)))
      (fun j => (i + 7) ^ 2 * (j + 1)) := by
  unfold body cΔ
  apply HoareR_weaken_bound
  apply HoareR_seq; apply HoareR_seq
  apply HoareR_weaken_bound; apply HoareR_Zset_I
  · intro t; rewrite [Zsize_delta]
    simp; rfl
  rw [integral_delta]
  apply HoareR_loop
  · apply HoareT_conseq_post
    apply loop_HoareT (hf:=c0_hf) (ht:=by apply c0_ht)
    intro x h; unfold f at h; simp at h
    rw [fs_eq] at h
    exact h
  · simp; apply c0_HoareR
  · intro y _; subst y
    intro j; simp [VType_space, Zset.size]
    apply S_card_bound
  apply HoareR_ZSB_D_mono
  · intro j; simp [Zset.size]
    apply S_card_bound
  · intro a b h; simp; nlinarith
  · intro j; simp
    nlinarith

theorem lifted_body_HoareR:
    HoareR
      (fun x => x = ↑↑δ0 is)
      (c↑ (body c0))
      (fun y => y = fun i => D (fun j => Zset.fromSet (S i j)))
      (fun i j => (i + 7) ^ 2 * (j + 1)) := by
  simp_rw [fun_stream_eq_forall]; simp
  apply HoareR_lifting (c:= body c0) (P := fun i x => x = δ0 (is i))
    (Q := fun i y => y = D (fun j => Zset.fromSet (S i j)))
  apply body_HoareR

lemma le_I_le (s: ℕ -> ℕ) (i b: ℕ)
  (hb: ∀ t ≤ i, s t ≤ b):
    I s i ≤ (i+1) * b := by
  induction' i with i ih
  · simp [hb]
  · simp
    specialize ih (by intros; apply hb; omega)
    specialize hb (i + 1) (by rfl)
    nlinarith

-- The unoptimized query's cost is `O(n^4)` for the iteration `n`
-- Note that we assume `join s1 s2` takes `O(|s1| * |s2|)` time, which may be improved to `O(|s1| + |s2|)` in this example, leading to `O(n^3)` total cost.
theorem query_HoareR:
    HoareR
      (fun x => x = is)
      (query c0)
      (fun _ => True)
      (fun i => (i+7)^4) := by
  unfold query
  apply HoareR_conseq_post (hq:= by tauto)
  apply HoareR_weaken_bound
  apply HoareR_bracket
  · simp; apply lifted_body_HoareR
  · simp
    apply lifted_body_HoareI2
      (hf:= c0_hf)
      (htv := by intros; apply c0_ht)
      (hei:= c0_hei)
      (hfa := by intros; apply c0_hfa)
  · simp; intro i; simp
    rw [ZeroAfter_succ_D_FixAfter1]
    intro j hj; simp
    rw [<- Zset.isSet_support_fromSet]; simp [S]
    rw [show min i (j+1) = i by omega]
  · simp; intro i
    apply HoareR_conseq_post (hq:=by tauto)
    apply HoareR_weaken_bound (r' := fun j => i *(2*j+2))
    apply HoareR_Zset_I_ns0
    intro j; simp [Zset.size]
    rewrite [DS2_eq]; simp
    rcases j with _ | j <;> simp <;> rw [DS2_card]
    · have := S_card_bound i 0
      omega
    · have := S_card_bound i j
      have := S_card_bound i (j + 1)
      have : i - (j + 1) ≤ i := by omega
      nlinarith
  intro i; simp
  have :
      I ((fun j ↦ (i + 7) ^ 2 * (j + 1)) + fun j ↦ i * (2 * j + 2)) i ≤
      (i+1) * (i+8)^3 := by
    apply le_I_le
    intro t ht; rw [stream_add_apply]
    nlinarith
  nlinarith

end GraphExample

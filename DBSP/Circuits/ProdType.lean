-- Product Types based on a single basetype
import Mathlib.Order.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

inductive PType (T: Type): Type 1 where
  | base: PType T
  | prod (a b: PType T): PType T

notation a "×ₚ" b :30 => PType.prod a b

@[reducible]
def PType_interp {T: Type} (a: PType T): Type :=
  match a with
  | PType.base => T
  | PType.prod a b => PType_interp a × PType_interp b

instance PTypePartialOrder {T: Type} [PartialOrder T] (pt: PType T):
    PartialOrder (PType_interp (pt)) :=
  match pt with
  | PType.base => by infer_instance
  | PType.prod a b => by
      haveI := PTypePartialOrder a; haveI := PTypePartialOrder b; infer_instance

instance PTypeAddCancelCommMonoid {T: Type} [AddCancelCommMonoid T] (pt: PType T):
    AddCancelCommMonoid (PType_interp (pt)) :=
  match pt with
  | PType.base => by infer_instance
  | PType.prod a b => by
      haveI := PTypeAddCancelCommMonoid a; haveI := PTypeAddCancelCommMonoid b; simp [PType_interp]; infer_instance

@[simp]
def PType_sum {T: Type} [AddCommMonoid T] {pt: PType T} (v: PType_interp pt): T :=
  match pt with
  | PType.base => v
  | PType.prod _ _ => PType_sum (v.fst) + PType_sum (v.snd)

lemma PType_Nat_0_min {pt: PType Nat} (a: PType_interp pt): 0 ≤ a := by
  induction pt <;> simp at *
  rename_i a b iha ihb
  rcases a; constructor <;> simp
  apply iha; apply ihb

lemma PType_sum_Nat_mono {pt: PType Nat} (v1 v2: PType_interp pt)
  (H: v1 ≤ v2): PType_sum v1 ≤ PType_sum v2 := by
  revert v1 v2
  induction pt
  · intros; simp [*]
  · rename_i a b ih1 ih2
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ H
    rcases H with ⟨H1, H2⟩
    specialize ih1 a1 a2 H1
    specialize ih2 b1 b2 H2
    simp; omega

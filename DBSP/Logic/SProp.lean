import DBSP.StreamTheory.Linear
import DBSP.StreamTheory.Stream
import DBSP.StreamTheory.StreamElim

-- `Sprop`, i.e. stream of Prop, is used to reason about properties of streams
-- `SPred` is a stream predicate on streams of type A
section SProp

@[reducible, simp]
def SProp := stream Prop

def STrue: SProp := fun _ => True
@[simp]
lemma STrue_apply {n: ℕ}:
  STrue n = True := by rfl

def SAnd: SProp -> SProp -> SProp :=
  fun P Q n => P n ∧ Q n
@[simp]
lemma SAnd_apply (P Q: SProp) (n: ℕ):
    SAnd P Q n = (P n ∧ Q n) := by rfl

def STrue2: stream (stream Prop) := fun _ _ => True
@[simp]
lemma STrue2_apply {m n: ℕ}:
    STrue2 m n = True := by rfl

def SAnd2: stream (stream Prop) -> stream (stream Prop) -> stream (stream Prop) :=
  fun P Q m n => P m n ∧ Q m n
@[simp]
lemma SAnd2_apply (P Q: stream (stream Prop)) (m n: ℕ):
    SAnd2 P Q m n = (P m n ∧ Q m n) := by rfl

-- This is to make `Sprop` downward-closed
def true_until (n: ℕ) (P: SProp) :=
  ∀ m ≤ n, P m

lemma true_until_mono {P: SProp} {n m: ℕ}
  (ht: true_until m P) (h: n ≤ m):
    true_until n P := by
  intro k hk; apply ht; omega

lemma true_until_forall {P: SProp}:
  (∀ n, P n) <-> (∀ n, true_until n P) := by
  constructor <;> simp [true_until] <;>
  intros <;> tauto

variable {A: Type} [Zero A] {n: ℕ}

@[reducible, simp]
def SPred (A: Type) := Operator A Prop

-- The `later` modality in step indexing
@[simp]
def later (P: SPred A): SPred A :=
  fun s n =>
    if n = 0 then s 0 = 0
     else P (drop 1 s) (n-1)

lemma later_delay (P: SPred A) (s: stream A) (n: ℕ):
    P s n <-> later P (z⁻¹ s) (n+1) := by simp

lemma later_delay_true_until (P: SPred A) (s: stream A) (n: ℕ):
    true_until n (P s) <-> true_until (n+1) (later P (z⁻¹ s)) := by
  simp [true_until]; constructor
  · intro hp m hm hm0
    apply hp; omega
  · intro h m hm
    have : m = m + 1 - 1 := by omega
    rw [this]; apply h <;> omega

lemma later_delay_forall (P: SPred A) (s: stream A):
    (∀ n, P s n) <-> (∀ n, later P (z⁻¹ s) (n+1)) := by simp

lemma later_delay_true_until_forall (P: SPred A) (s: stream A):
    (∀ n, true_until n (P s)) <-> (∀ n, true_until n (later P (z⁻¹ s))) := by
  constructor
  · intro h n; cases n; simp [true_until]
    rw [<- later_delay_true_until]; tauto
  · intro h n
    rw [later_delay_true_until]; tauto

end SProp

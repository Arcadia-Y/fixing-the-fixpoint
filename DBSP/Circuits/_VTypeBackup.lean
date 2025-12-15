import DBSP.StreamTheory.Operators
import DBSP.StreamTheory.Stream

-- the type of the values flowing through the circuit
-- n denotes the depth of the stream layers
inductive VType: ℕ -> Type 1 where
  | base (T: Type) [BaseType T]: VType 0
  | prod {n: ℕ} (a b: VType n) : VType n
  | stream {n: ℕ} (a: VType n) : VType (n + 1)

notation a "×ᵥ" b :30 => VType.prod a b

@[simp]
def VType_interp {n: ℕ} (a: VType n): Type :=
  match a with
  | VType.base T => T
  | VType.prod a b => VType_interp a × VType_interp b
  | VType.stream a => stream (VType_interp a)

instance Zero_VType_interp {n: ℕ} (a: VType n) : Zero (VType_interp a) :=
  match a with
  | VType.base T => by simp; infer_instance
  | VType.prod a b => by haveI := Zero_VType_interp a; haveI := Zero_VType_interp b; simp; infer_instance
  | VType.stream a => by haveI := Zero_VType_interp a; simp; infer_instance

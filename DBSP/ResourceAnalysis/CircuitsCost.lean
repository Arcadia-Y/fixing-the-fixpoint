import DBSP.Circuits.Circuits_v5
import DBSP.FPC.FPChecker_v2

namespace CktBasic

def add_cost {a: VType} (x: VType_interp a × VType_interp a): ℕ :=
  match a with
  | VType.base _ => BaseType.add_cost x
  | VType.prod _ _ => add_cost (x.1.1, x.2.1) + add_cost (x.1.2, x.2.2)

def sub_cost {a: VType} (x: VType_interp a × VType_interp a): ℕ :=
  match a with
  | VType.base _ => BaseType.sub_cost x
  | VType.prod _ _ => sub_cost (x.1.1, x.2.1) + sub_cost (x.1.2, x.2.2)

def VType_space {a: VType} (x: VType_interp a) :=
  PType_sum (VType_size x)

-- Type of cost function of a circuit
-- For `cf: CostFunType ns a`, `cf x` is the cost of computing the output on input `x`
-- If an entry of `cf x` is `some n`,
--   then if all previous computation terminate, the step terminates and the cost is `n`
-- otherwise if it is `∞`,
--   then the step diverges
@[simp, reducible]
def CostFunType (ns: Bool) (a: VType) :=
  (SOVType ns a) -> (SOType ns ℕ∞)

instance (ns: Bool): CanonicallyOrderedAdd (SOType ns ℕ∞) := by
  rcases ns <;> simp [stream] <;> infer_instance

-- extend the `ℕ` in `f`'s domain to `ℕ∞`
@[simp]
def extend_fun {ns} {a: VType} (f: SOVType ns a -> SOType ns ℕ): CostFunType ns a :=
  fun x => match ns with
  | false => fun n => ↑(f x n)
  | true => fun m n => ↑(f x m n)

def FirstTrue (s: stream Prop) (n: ℕ): Prop :=
  s n ∧ ∀ m < n, ¬ s m

-- Cost model for circuits based on the default evaluation strategy
-- For a circuit `c`, `cost_f c` is a function maps an input of `c` to the cost of computing the output
noncomputable def cost_f {ns} {a b: VType}: (Ckt a b ns) -> (CostFunType ns a)
  | Ckt.node1 f => extend_fun (↑↑f.cost)
  | Ckt.node2 f => extend_fun (↑↑f.cost)
  | Ckt.const _ => 0
  | Ckt.id => 0
  | Ckt.fst => 0
  | Ckt.snd => 0
  | Ckt.add => extend_fun (liftO ns add_cost)
  | Ckt.sub => extend_fun (liftO ns sub_cost)
  | Ckt.seq c1 c2 => fun x => cost_f c1 x + cost_f c2 (denote c1 x)
  -- We assume a sequential implementation
  -- For a parallel implementation, we can take max instead of sum
  | Ckt.par c1 c2 => fun x => cost_f c1 x + cost_f c2 x
  | Ckt.delay => extend_fun (liftO ns VType_space)
  | Ckt.lifting c => ↑↑(cost_f c)
  | Ckt.loop c => fun x => let o := denote (Ckt.loop c) x
      cost_f c (sprodO ns (x, z⁻¹ o)) + extend_fun (liftO ns VType_space) o
  | Ckt.loop_lifted c => fun x => let o := denote (Ckt.loop_lifted c) x
      fun m n => cost_f c (sprod2 (x, ↑↑z⁻¹ o)) m n + (liftO 1 VType_space) o m n
  | Ckt.bracket c => fun x i =>
      let o := denote c (↑↑δ0 x)
      let fp := FPChecker2 c (↑↑δ0 x)
      -- If cost checker returns true for the first time at step n,
      -- then the cost is the sum of the cost of `c` and the integration cost
      match Classical.propDecidable (∃ n, FirstTrue (fp i) n) with
      | Decidable.isTrue h =>
        let sumO := fun n => sumVals (o i) n
        let c_cost := cost_f c (↑↑δ0 x) i
        let integral_cost: stream ℕ∞ := fun n => ↑(add_cost (sumO n, o i n))
        -- Question: should we omit the integral cost and the checker cost?
        sumVals (c_cost + integral_cost) (Classical.choose h + 1)
      | Decidable.isFalse _ => ⊤

end CktBasic

import DBSP.Circuits.Circuits
import DBSP.Convergence.Spec
import DBSP.Convergence.FPProp
open Classical

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

-- Cost model for **terminating** circuits based on the default evaluation strategy
-- For a circuit `c`, `cost_f c` is a function maps an input of `c` to the cost of computing the output
-- We assume that the underlying data is big enough such that
-- we can count only the cost of computing and storing these data and ignore other bookkeeping cost
noncomputable def cost_f {ns} {A B: VType} (c: Ckt A B ns) (x: SOVType ns A) (ht: IntConv c x) : SOType ns ℕ :=
  match c with
  | Ckt.node1 f => liftO ns f.cost x
  | Ckt.node2 f => liftO ns f.cost x
  | Ckt.const _ => 0
  | Ckt.id => 0
  | Ckt.fst => 0
  | Ckt.snd => 0
  | Ckt.add => liftO ns add_cost x
  | Ckt.sub => liftO ns sub_cost x
  | Ckt.seq c1 c2 => cost_f c1 x ht.1 + cost_f c2 (denote c1 x) ht.2
  -- We assume a sequential implementation
  -- For a parallel implementation, we can take max instead of sum
  | Ckt.par c1 c2 => cost_f c1 x ht.1 + cost_f c2 x ht.2
  -- delay needs to store the current results for later use
  | Ckt.delay => liftO ns VType_space x
  -- lifted delay needs to do the same
  | Ckt.lifted_delay => liftO 1 VType_space x
  | Ckt.lifting c => fun i => cost_f c (x i) (ht i)
  -- There's an delay in the loop's back edge, so we need to add the cost of delay
  | Ckt.loop c => let o := denote (Ckt.loop c) x
      cost_f c (sprodO ns (x, z⁻¹ o)) ht + liftO ns VType_space o
  | Ckt.lifted_loop c => let o := denote (Ckt.lifted_loop c) x
      cost_f c (sprod2 (x, ↑↑z⁻¹ o)) ht + liftO 1 VType_space o
  -- `bracket` maintains an internal accumulator, which can be regarded as an `cI` operator
  | Ckt.bracket c => fun i =>
      let b := Nat.find ((IntConv_bracket_alt ht).2 i)
      let o := denote c (↑↑δ0 x) i
      let c_cost: stream ℕ := cost_f c (↑↑δ0 x) ht.1 i
      -- This is essentially unfolding `cost_f cI o`
      let I_cost: stream ℕ := ↑↑add_cost (sprod (o, z⁻¹ (I o))) + ↑↑VType_space (I o)
      I (c_cost + I_cost) b

end CktBasic

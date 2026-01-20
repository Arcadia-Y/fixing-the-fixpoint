import DBSP.Circuits.Circuits_v6
open CktBasic

-- Push the lifting operator inside to simplify a circuit
-- spec is denote (push_lifting c) = denote (c↑ c)
def push_lifting {a b} (c: Ckt a b 0): Ckt a b 1 :=
  match c with
  | Ckt.node1 f => Ckt.node1 f
  | Ckt.node2 f => Ckt.node2 f
  | Ckt.const x => Ckt.const x
  | Ckt.id => Ckt.id
  | Ckt.fst => Ckt.fst
  | Ckt.snd => Ckt.snd
  | Ckt.add => Ckt.add
  | Ckt.sub => Ckt.sub
  | Ckt.seq c1 c2 => (push_lifting c1) >>c (push_lifting c2)
  | Ckt.par c1 c2 => (push_lifting c1) &&c (push_lifting c2)
  | Ckt.delay => Ckt.delay
  | Ckt.loop c =>  Ckt.loop_lifted (push_lifting c)
  | Ckt.bracket c => c↑ (cbracket c)

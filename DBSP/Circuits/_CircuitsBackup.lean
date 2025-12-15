import DBSP.StreamTheory.Operators

namespace ckt

section Circuits

-- the type of the values flowing through the circuit
inductive VType where
  | prim (a: Type): VType
  | prod (a b: VType) : VType
  | stream (a: VType) : VType

notation a "×ᵥ" b => VType.prod a b

def VType_interp : VType -> Type
  | VType.prim a => a
  | VType.prod a b => VType_interp a × VType_interp b
  | VType.stream a => stream (VType_interp a)

def stream_layer (a: VType): ℕ :=
  match a with
  | VType.prim _ => 0
  | VType.prod _ _ => 0
  | VType.stream s => 1 + stream_layer s

inductive Size : VType -> Type 1
  | prim {a: Type} (n: ℕ): Size (VType.prim a)
  | prod {a b: VType} (s1: Size a) (s2: Size b): Size (VType.prod a b)
  | stream {a: VType} (t: stream (Size a)): Size (VType.stream a)

def size_zero {a: VType}: Size a :=
  match a with
  | VType.prim _ => Size.prim 0
  | VType.prod _ _  => Size.prod size_zero size_zero
  | VType.stream _ => Size.stream (fun _ => size_zero)

instance ZeroSize (a: VType): Zero (Size a) where
  zero := size_zero

-- primitive time cost and time cost of a stream
inductive Time : ℕ -> Type 1
  | prim (n: ℕ): Time 0
  | stream {n: ℕ} (t: stream (Time n)): Time (n+1)

def time_add {n: ℕ} (t1 t2: Time n): Time n :=
  match t1, t2 with
  | Time.prim n1, Time.prim n2 => Time.prim (n1 + n2)
  | Time.stream s1, Time.stream s2 => Time.stream (fun i => time_add (s1 i) (s2 i))

instance HAddTime {n: ℕ}: HAdd (Time n) (Time n) (Time n) where
  hAdd := time_add

def time_zero {n: ℕ}: Time n :=
  match n with
  | 0 => Time.prim 0
  | Nat.succ n' => Time.stream (fun _ => @time_zero n')

instance ZeroTime {n: ℕ}: Zero (Time n) where
  zero := time_zero

-- Primitive node typeclass
class PrimNode (P: VType -> VType -> Type 1) where
  -- denotational semantics
  denote: ∀ {a b: VType}, P a b -> VType_interp a -> VType_interp b
  -- input_size -> output_size
  size_f: ∀ {a b: VType}, P a b -> Size a -> Size b
  -- input_size -> time_cost
  time_f: ∀ {a b: VType}, P a b -> Size a -> Time (stream_layer b)

variable
  (P: VType -> VType -> Type 1)
  [PrimNode P]

-- general circuit type
inductive Ckt: VType -> VType -> Type 1
  -- primitive nodes
  | node {a b: VType} (p: P a b) : Ckt a b
  -- combiℕor for product type
  | id {a: VType} : Ckt a a
  | fst {a b: VType} : Ckt (a ×ᵥ b) a
  | snd {a b: VType} : Ckt (a ×ᵥ b) b
  -- sequential composition
  | seq {a b c : VType} (f1 : Ckt a b) (f2 : Ckt b c) : Ckt a c
  -- parallel composition
  | par {a b c : VType} (f1 : Ckt a b) (f2 : Ckt a c) : Ckt a (b ×ᵥ c)
  -- feedback loop
  | loop {a b: VType} [Zero (VType_interp b)] (f: Ckt (a ×ᵥ VType.stream b) (VType.stream b)): Ckt a (VType.stream b)

-- denotational semantics
def denote {a b: VType}: (Ckt P a b) -> (VType_interp a -> VType_interp b)
  | Ckt.node p => PrimNode.denote p
  | Ckt.id => id
  | Ckt.fst => Prod.fst
  | Ckt.snd => Prod.snd
  | Ckt.seq f1 f2 => denote f2 ∘ denote f1
  | Ckt.par f1 f2 => fun x => (denote f1 x, denote f2 x)
  | Ckt.loop f => fun a => fix (fun s => denote f (a, s))

-- size function of a circuit
def size_f {a b: VType}: (Ckt P a b) -> Size a -> Size b
  | Ckt.node p => PrimNode.size_f p
  | Ckt.id => id
  | Ckt.fst => fun (Size.prod s1 _) => s1
  | Ckt.snd => fun (Size.prod _ s2) => s2
  | Ckt.seq f1 f2 => fun s => size_f f2 (size_f f1 s)
  | Ckt.par f1 f2 => fun s => Size.prod (size_f f1 s) (size_f f2 s)
  | Ckt.loop f =>
      fun size_a => Size.stream <|
        fix (fun str_size_b =>
          let (Size.stream s) := size_f f (Size.prod size_a (Size.stream str_size_b))
          s
        )

def loop_time_f {a b: VType} [Zero (VType_interp b)]
  (f: Size (a ×ᵥ b.stream) -> Time (stream_layer b.stream))
  (size_a: Size a) (str_size_b: stream (Size b)) (n: ℕ): Time (stream_layer b.stream) :=
   match n with
   | 0 =>


def time_f {a b: VType}: (Ckt P a b) -> Size a -> Time (stream_layer b)
  | Ckt.node p => PrimNode.time_f p
  | Ckt.id => fun _ => 0
  | Ckt.fst => fun _ => 0
  | Ckt.snd => fun _ => 0
  | Ckt.seq f1 f2 => fun s => time_f f2 (size_f P f1 s) + (time_f f1 s)
  | Ckt.par f1 f2 => fun s => 0
  | Ckt.loop f =>
      fun size_a => Time.stream <| fun n =>
        let size_b := size_f f size_a
        time_f f (Size.prod size_a size_b)

end Circuits

end ckt

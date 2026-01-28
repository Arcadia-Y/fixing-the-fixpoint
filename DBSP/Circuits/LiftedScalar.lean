-- Since our formal definition only covers circuits with streams and nested streams
-- we need a predicate to denote those lifted scalar circuits for lifted relational queries
import DBSP.Circuits.Circuits
open CktBasic

-- A lifted scalar circuit is a circuit without any delay, loops and brackets
inductive LiftedScalar: ∀ {a b ns}, Ckt a b ns -> Prop
  | node1 {A B: Type} [BaseType A] [BaseType B] (n: @UnaryNode A B _ _):
      LiftedScalar (Ckt.node1 n)
  | node2 {A B C: Type} [BaseType A] [BaseType B] [BaseType C] (n: @BinaryNode A B C _ _ _):
      LiftedScalar (Ckt.node2 n)
  | const {b: VType} (x: VType_interp b) :
    LiftedScalar (Ckt.const x)
  | id : LiftedScalar (Ckt.id)
  | fst : LiftedScalar (Ckt.fst)
  | snd : LiftedScalar (Ckt.snd)
  | add : LiftedScalar (Ckt.add)
  | sub : LiftedScalar (Ckt.sub)
  | seq {ns a b c} (c1 : Ckt a b ns) (c2 : Ckt b c ns) :
      LiftedScalar c1 -> LiftedScalar c2 -> LiftedScalar (Ckt.seq c1 c2)
  | par {ns a b c} (c1 : Ckt a b ns) (c2 : Ckt a c ns) :
      LiftedScalar c1 -> LiftedScalar c2 -> LiftedScalar (Ckt.par c1 c2)
  | lifting {a b} (c: Ckt a b 0) :
      LiftedScalar c -> LiftedScalar (Ckt.lifting c)

-- Decidable instance for LiftedScalar
def instDecidableLiftedScalar {ns} {a b} (c : Ckt a b ns) : Decidable (LiftedScalar c) :=
  match c with
  | Ckt.node1 n => isTrue (LiftedScalar.node1 n)
  | Ckt.node2 n => isTrue (LiftedScalar.node2 n)
  | Ckt.const x => isTrue (LiftedScalar.const x)
  | Ckt.id => isTrue LiftedScalar.id
  | Ckt.fst => isTrue LiftedScalar.fst
  | Ckt.snd => isTrue LiftedScalar.snd
  | Ckt.add => isTrue LiftedScalar.add
  | Ckt.sub => isTrue LiftedScalar.sub
  | Ckt.seq c1 c2 =>
    match instDecidableLiftedScalar c1, instDecidableLiftedScalar c2 with
    | isTrue h1, isTrue h2 => isTrue (LiftedScalar.seq c1 c2 h1 h2)
    | isFalse h1, _ => isFalse (by intro h; cases h; apply h1; assumption)
    | _, isFalse h2 => isFalse (by intro h; cases h; apply h2; assumption)
  | Ckt.par c1 c2 =>
    match instDecidableLiftedScalar c1, instDecidableLiftedScalar c2 with
    | isTrue h1, isTrue h2 => isTrue (LiftedScalar.par c1 c2 h1 h2)
    | isFalse h1, _ => isFalse (by intro h; cases h; apply h1; assumption)
    | _, isFalse h2 => isFalse (by intro h; cases h; apply h2; assumption)
  | Ckt.lifting c =>
    match instDecidableLiftedScalar c with
    | isTrue h => isTrue (LiftedScalar.lifting c h)
    | isFalse h => isFalse (by intro h'; cases h'; apply h; assumption)
  | Ckt.delay => isFalse (by intro h; cases h)
  | Ckt.lifted_delay => isFalse (by intro h; cases h)
  | Ckt.loop _ => isFalse (by intro h; cases h)
  | Ckt.lifted_loop _ => isFalse (by intro h; cases h)
  | Ckt.bracket _ => isFalse (by intro h; cases h)

instance {ns} {a b} (c : Ckt a b ns) : Decidable (LiftedScalar c) :=
  instDecidableLiftedScalar c

-- This is a purely semantic property
def DenoteLiftedScalar {ns} {A B: VType} (c: Ckt A B ns) (f: VType_interp A -> VType_interp B): Prop :=
  denote c = liftO ns f

-- The key semantic property of lifted scalar circuits
theorem LiftedScalar_Denote {ns} {A B: VType} (c: Ckt A B ns):
    LiftedScalar c -> ∃f, DenoteLiftedScalar c f := by
  intro h
  induction h <;> simp [DenoteLiftedScalar, denote]
  case seq ns a b c c1 c2 h1 h2 ih1 ih2 =>
    rcases ih1 with ⟨f1, hf1⟩
    rcases ih2 with ⟨f2, hf2⟩
    exists f2 ∘ f1
    rw [hf1, hf2]
    rcases ns <;> simp [liftO] <;> rfl
  case par ns a b c c1 c2 h1 h2 ih1 ih2 =>
    rcases ih1 with ⟨f1, hf1⟩
    rcases ih2 with ⟨f2, hf2⟩
    exists (fun x => (f1 x, f2 x))
    rw [hf1, hf2]
    rcases ns <;> simp [liftO, sprodO] <;> rfl
  case lifting a b c h ih =>
    rcases ih with ⟨f, hf⟩
    exists f
    rw [hf]
    simp [liftO, lifting]

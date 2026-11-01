module

public import LeanInets.Net

/-!
# Example nets

Small nets used to check that the definitions are usable.
-/

@[expose] public section

namespace Examples

/-! ### A lone wire -/

/-- The identity net: a single wire connecting the two free ports. Its interface is `Side`,
so the free port `l` is linked to the left end of the wire and `r` to the right one. -/
def ident (S : Signature) : Net S Side where
  Agent := Empty
  Wire := Unit
  label := Empty.elim
  link
    | .free s => .wire () s
    | .wire () s => .free s
    | .pri a => a.elim
    | .aux a _ => a.elim
  link_link p := by rcases p with _ | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | _ <;> rfl
  link_ne p := by rcases p with _ | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | _ <;> nofun
  link_free _ := trivial

/-! ### Unary arithmetic

Lafont's addition on unary numbers: `Z` (zero), `S` (successor, one auxiliary port) and
`add` (two auxiliary ports). The principal port of `add` is its first argument; its
auxiliary ports are the second argument and the result. -/

/-- The symbols of unary arithmetic. -/
inductive Arith where
  | zero
  | succ
  | add
  deriving DecidableEq, Repr

/-- The signature of unary arithmetic. -/
def arith : Signature where
  Sym := Arith
  arity
    | .zero => 0
    | .succ => 1
    | .add => 2

namespace OnePlusZero

/-- The agents of the net computing `S Z + Z`. -/
inductive Agent where
  | add
  | s
  | z₁
  | z₂
  deriving DecidableEq, Repr

instance : Fintype Agent :=
  Fintype.ofList [.add, .s, .z₁, .z₂] (by intro a; cases a <;> decide)

/-- The symbol of each agent. -/
def label : Agent → arith.Sym
  | .add => .add
  | .s => .succ
  | .z₁ => .zero
  | .z₂ => .zero

/-- The wiring of `S Z + Z`; the result is the single free port. -/
def link : Port label Empty Unit → Port label Empty Unit
  | .pri .add => .pri .s
  | .pri .s => .pri .add
  | .aux .s _ => .pri .z₁
  | .pri .z₁ => .aux .s ⟨0, by decide⟩
  | .aux .add ⟨0, _⟩ => .pri .z₂
  | .pri .z₂ => .aux .add ⟨0, by decide⟩
  | .aux .add _ => .free ()
  | .free () => .aux .add ⟨1, by decide⟩
  | .aux .z₁ k | .aux .z₂ k => k.elim0
  | .wire w _ => w.elim

end OnePlusZero

open OnePlusZero in
/-- The net `S Z + Z`, with its result as the only free port. -/
def onePlusZero : Net arith Unit where
  Agent := OnePlusZero.Agent
  Wire := Empty
  label := label
  link := link
  link_link := by decide
  link_ne := by decide
  link_free _ := trivial

/-- The `add` agent and the successor agent form an active pair. -/
example : onePlusZero.IsActivePair OnePlusZero.Agent.add OnePlusZero.Agent.s := rfl

/-- So `S Z + Z` is not in normal form. -/
example : ¬ onePlusZero.IsNormal := fun h => h OnePlusZero.Agent.add OnePlusZero.Agent.s rfl

end Examples

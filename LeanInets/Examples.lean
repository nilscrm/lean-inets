module

public import LeanInets.Unit

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

/-- The identity net with its wire the other way round. -/
def identFlip (S : Signature) : Net S Side where
  Agent := Empty
  Wire := Unit
  label := Empty.elim
  link
    | .free s => .wire () s.flip
    | .wire () s => .free s.flip
    | .pri a => a.elim
    | .aux a _ => a.elim
  link_link p := by rcases p with _ | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | _ <;> simp
  link_ne p := by rcases p with _ | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | _ <;> nofun
  link_free _ := trivial

/-- Isomorphisms cannot flip wires, so the two orientations of the identity net are not
isomorphic. -/
example (S : Signature) : ¬ (ident S).Isomorphic (identFlip S) := by
  rintro ⟨e⟩
  have : Port.wire () .r = .wire (e.wire ()) .l := e.link_port (.free .l)
  cases this

/-! ### Isomorphism up to wires

`ident` and `identFlip` are not isomorphic, but they have the same connections: in both, the
free port `l` is connected to `r`. -/

theorem ident_conn (S : Signature) : (ident S).Conn (.free .l) (.free .r) :=
  .single (Net.step_wire (N := ident S) () .l)

theorem identFlip_conn (S : Signature) : (identFlip S).Conn (.free .l) (.free .r) :=
  .single (Net.step_wire (N := identFlip S) () .r)

/-- The two orientations of the identity net are isomorphic up to wires. -/
def identWireIso (S : Signature) : Net.WireIso (ident S) (identFlip S) where
  agent := .refl _
  label_agent a := a.elim
  conn_map x y h := by
    rcases x with (_ | _) | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩
    · obtain rfl := h.unique (ident_conn S)
      exact identFlip_conn S
    · obtain rfl := h.unique (ident_conn S).symm
      exact (identFlip_conn S).symm

example (S : Signature) : ident S ≈ identFlip S := (identWireIso S).equiv

/-- A vicious circle: a wire whose two ends are linked to each other. -/
def loop (S : Signature) : Net S Empty where
  Agent := Empty
  Wire := Unit
  label := Empty.elim
  link
    | .wire () s => .wire () s.flip
    | .free i => i.elim
    | .pri a => a.elim
    | .aux a _ => a.elim
  link_link p := by rcases p with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨⟨⟩, _ | _⟩ <;> rfl
  link_ne p := by rcases p with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨⟨⟩, _ | _⟩ <;> nofun
  link_free i := i.elim

/-- The empty net. -/
def empty (S : Signature) : Net S Empty where
  Agent := Empty
  Wire := Empty
  label := Empty.elim
  link p := p
  link_link _ := rfl
  link_ne p := by rcases p with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩
  link_free i := i.elim

/-- Vicious circles of wires vanish up to `≈`. -/
example (S : Signature) : loop S ≈ empty S :=
  Net.WireIso.equiv
    { agent := .refl _
      label_agent := nofun
      conn_map := by rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩) }

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

/-! ### Gluing -/

/-- Label a single agent. -/
def single (s : arith.Sym) : Unit → arith.Sym := fun _ => s

/-- A single `Z`, its principal port on the right of the interface. -/
def zero : Net arith (Empty ⊕ Unit) where
  Agent := Unit
  Wire := Empty
  label := single .zero
  link
    | .pri () => .free (.inr ())
    | .free (.inr ()) => .pri ()
    | .free (.inl e) => e.elim
    | .aux () k => k.elim0
    | .wire w _ => w.elim
  link_link := by decide
  link_ne := by decide
  link_free := by decide

/-- A single `S`, its principal port on the left of the interface and its auxiliary port on
the right. -/
def succPri : Net arith (Unit ⊕ Unit) where
  Agent := Unit
  Wire := Empty
  label := single .succ
  link
    | .pri () => .free (.inl ())
    | .free (.inl ()) => .pri ()
    | .aux () _ => .free (.inr ())
    | .free (.inr ()) => .aux () ⟨0, by decide⟩
    | .wire w _ => w.elim
  link_link := by decide
  link_ne := by decide
  link_free := by decide

/-- A single `S`, its auxiliary port on the left of the interface and its principal port on
the right. -/
def succAux : Net arith (Unit ⊕ Unit) where
  Agent := Unit
  Wire := Empty
  label := single .succ
  link
    | .aux () _ => .free (.inl ())
    | .free (.inl ()) => .aux () ⟨0, by decide⟩
    | .pri () => .free (.inr ())
    | .free (.inr ()) => .pri ()
    | .wire w _ => w.elim
  link_link := by decide
  link_ne := by decide
  link_free := by decide

/-- Gluing `Z` to the principal port of `S` creates an active pair across the boundary. -/
example : (zero.glue succPri).IsActivePair (.inl ()) (.inr ()) := rfl

/-- Gluing `Z` to the auxiliary port of `S` gives the numeral `S Z`, which is normal. -/
example : (zero.glue succAux).IsNormal := by
  rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) ⟨⟩

end Examples

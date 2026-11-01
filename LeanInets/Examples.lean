module

public import LeanInets.Unit
public import LeanInets.Reduction

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

/-- In `ident`, the free ports and both ends of the wire form a single path. -/
example (S : Signature) : (ident S).Connected (.free .l) (.wire () .r) :=
  (Net.connected_link (N := ident S) _).trans (Net.connected_flipEnd (N := ident S) _)

theorem ident_partner (S : Signature) : (ident S).Partner (.free .l) (.free .r) :=
  .single (Net.step_wire (N := ident S) () .l)

theorem identFlip_partner (S : Signature) : (identFlip S).Partner (.free .l) (.free .r) :=
  .single (Net.step_wire (N := identFlip S) () .r)

/-- The two orientations of the identity net are isomorphic up to wires. -/
def identWireIso (S : Signature) : Net.WireIso (ident S) (identFlip S) :=
  .ofPartner (.refl _)
    (fun a => a.elim) fun x y h => by
      rcases x with (_ | _) | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩
      · obtain rfl := h.unique (ident_partner S)
        exact identFlip_partner S
      · obtain rfl := h.unique (ident_partner S).symm
        exact (identFlip_partner S).symm

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
    (.ofPartner (.refl _) nofun (by rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩)))

/-! ### Unary arithmetic

Lafont's unary arithmetic: `Z` (zero), `S` (successor, one auxiliary port), `add` and `mul`
(two auxiliary ports each), and the eraser `ε` (no auxiliary ports) and duplicator `δ` (two
auxiliary ports) for numerals. The principal port of `add` and `mul` is their first argument;
their auxiliary ports are the second argument and the result. -/

/-- The symbols of unary arithmetic. -/
inductive Arith where
  | zero
  | succ
  | add
  | mul
  | erase
  | dup
  deriving DecidableEq, Repr

/-- The signature of unary arithmetic. -/
def arith : Signature where
  Sym := Arith
  arity
    | .zero => 0
    | .succ => 1
    | .add => 2
    | .mul => 2
    | .erase => 0
    | .dup => 2

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

/-! ### Interaction rules for addition

Lafont's rules for addition: `add Z y = y` and `add (S x) y = S (add x y)`. The interface of
a rule for `add ⋈ β` starts with the auxiliary ports of `add` (`inl 0` is `y`, `inl 1` is
the result), followed by those of `β` (for `S`, `inr 0` is `x`). -/

/-- The rule for `add ⋈ Z`: a wire connecting `y` to the result. -/
def addZero : Net arith (Fin 2 ⊕ Fin 0) where
  Agent := Empty
  Wire := Unit
  label := Empty.elim
  link
    | .free (.inl 0) => .wire () .l
    | .free (.inl 1) => .wire () .r
    | .wire () .l => .free (.inl 0)
    | .wire () .r => .free (.inl 1)
    | .free (.inr k) => k.elim0
    | .pri a => a.elim
    | .aux a _ => a.elim
  link_link := by decide
  link_ne := by decide
  link_free := by decide

namespace AddSucc

/-- The agents of the rule for `add ⋈ S`. -/
inductive Agent where
  | add
  | s
  deriving DecidableEq, Repr

instance : Fintype Agent :=
  Fintype.ofList [.add, .s] (by intro a; cases a <;> decide)

/-- The symbol of each agent. -/
def label : Agent → arith.Sym
  | .add => .add
  | .s => .succ

/-- The wiring of `S (add x y)`. -/
def link : Port label Empty (Fin 2 ⊕ Fin 1) → Port label Empty (Fin 2 ⊕ Fin 1)
  | .pri .s => .free (.inl 1)
  | .aux .s _ => .aux .add ⟨1, by decide⟩
  | .pri .add => .free (.inr 0)
  | .aux .add ⟨0, _⟩ => .free (.inl 0)
  | .aux .add _ => .aux .s ⟨0, by decide⟩
  | .free (.inl ⟨0, _⟩) => .aux .add ⟨0, by decide⟩
  | .free (.inl _) => .pri .s
  | .free (.inr _) => .pri .add
  | .wire w _ => w.elim

end AddSucc

/-- The rule for `add ⋈ S`: the net `S (add x y)`. -/
def addSucc : Net arith (Fin 2 ⊕ Fin 1) where
  Agent := AddSucc.Agent
  Wire := Empty
  label := AddSucc.label
  link := AddSucc.link
  link_link := by decide
  link_ne := by decide
  link_free := by decide

/-- The rule for `ε ⋈ Z`: the empty net. -/
def eraseZero : Net arith (Fin 0 ⊕ Fin 0) where
  Agent := Empty
  Wire := Empty
  label := Empty.elim
  link p := p
  link_link _ := rfl
  link_ne := by decide
  link_free := by decide

/-- The rule for `ε ⋈ S`: an eraser on the predecessor. -/
def eraseSucc : Net arith (Fin 0 ⊕ Fin 1) where
  Agent := Unit
  Wire := Empty
  label := single .erase
  link
    | .pri () => .free (.inr 0)
    | .free (.inr _) => .pri ()
    | .free (.inl k) => k.elim0
    | .aux () k => k.elim0
    | .wire w _ => w.elim
  link_link := by decide
  link_ne := by decide
  link_free := by decide

/-- Two agents with the same symbol. -/
def pair (s : arith.Sym) : Fin 2 → arith.Sym := fun _ => s

/-- The rule for `δ ⋈ Z`: two copies of `Z`. -/
def dupZero : Net arith (Fin 2 ⊕ Fin 0) where
  Agent := Fin 2
  Wire := Empty
  label := pair .zero
  link
    | .pri i => .free (.inl i)
    | .free (.inl i) => .pri i
    | .free (.inr k) => k.elim0
    | .aux _ k => k.elim0
    | .wire w _ => w.elim
  link_link := by decide
  link_ne := by decide
  link_free := by decide

namespace DupSucc

/-- The agents of the rule for `δ ⋈ S`. -/
inductive Agent where
  | dup
  | s (i : Fin 2)
  deriving DecidableEq

instance : Fintype Agent :=
  Fintype.ofList [.dup, .s 0, .s 1] (by
    intro a
    cases a
    · decide
    · rename_i i
      revert i
      decide)

/-- The symbol of each agent. -/
def label : Agent → arith.Sym
  | .dup => .dup
  | .s _ => .succ

/-- The wiring of the rule for `δ ⋈ S`: duplicate the predecessor, and put an `S` on each
copy. -/
def link : Port label Empty (Fin 2 ⊕ Fin 1) → Port label Empty (Fin 2 ⊕ Fin 1)
  | .pri .dup => .free (.inr 0)
  | .free (.inr _) => .pri .dup
  | .aux .dup i => .aux (.s i) (0 : Fin 1)
  | .aux (.s i) _ => .aux .dup i
  | .pri (.s i) => .free (.inl i)
  | .free (.inl i) => .pri (.s i)
  | .wire w _ => w.elim

end DupSucc

/-- The rule for `δ ⋈ S`. -/
def dupSucc : Net arith (Fin 2 ⊕ Fin 1) where
  Agent := DupSucc.Agent
  Wire := Empty
  label := DupSucc.label
  link := DupSucc.link
  link_link := by decide
  link_ne := by decide
  link_free := by decide

namespace MulZero

/-- The agents of the rule for `mul ⋈ Z`. -/
inductive Agent where
  | erase
  | z
  deriving DecidableEq

instance : Fintype Agent :=
  Fintype.ofList [.erase, .z] (by intro a; cases a <;> decide)

/-- The symbol of each agent. -/
def label : Agent → arith.Sym
  | .erase => .erase
  | .z => .zero

/-- The wiring of the rule for `mul ⋈ Z`: erase the second argument, the result is `Z`. -/
def link : Port label Empty (Fin 2 ⊕ Fin 0) → Port label Empty (Fin 2 ⊕ Fin 0)
  | .pri .erase => .free (.inl 0)
  | .pri .z => .free (.inl 1)
  | .free (.inl ⟨0, _⟩) => .pri .erase
  | .free (.inl _) => .pri .z
  | .free (.inr k) => k.elim0
  | .aux .erase k => k.elim0
  | .aux .z k => k.elim0
  | .wire w _ => w.elim

end MulZero

/-- The rule for `mul ⋈ Z`. -/
def mulZero : Net arith (Fin 2 ⊕ Fin 0) where
  Agent := MulZero.Agent
  Wire := Empty
  label := MulZero.label
  link := MulZero.link
  link_link := by decide
  link_ne := by decide
  link_free := by decide

namespace MulSucc

/-- The agents of the rule for `mul ⋈ S`. -/
inductive Agent where
  | dup
  | mul
  | add
  deriving DecidableEq

instance : Fintype Agent :=
  Fintype.ofList [.dup, .mul, .add] (by intro a; cases a <;> decide)

/-- The symbol of each agent. -/
def label : Agent → arith.Sym
  | .dup => .dup
  | .mul => .mul
  | .add => .add

/-- The wiring of `add (mul x y₁) y₂`, where `y₁` and `y₂` are copies of `y`. -/
def link : Port label Empty (Fin 2 ⊕ Fin 1) → Port label Empty (Fin 2 ⊕ Fin 1)
  | .pri .dup => .free (.inl 0)
  | .free (.inl ⟨0, _⟩) => .pri .dup
  | .pri .mul => .free (.inr 0)
  | .free (.inr _) => .pri .mul
  | .aux .mul ⟨0, _⟩ => .aux .dup ⟨0, by decide⟩
  | .aux .dup ⟨0, _⟩ => .aux .mul ⟨0, by decide⟩
  | .aux .mul _ => .pri .add
  | .pri .add => .aux .mul ⟨1, by decide⟩
  | .aux .add ⟨0, _⟩ => .aux .dup ⟨1, by decide⟩
  | .aux .dup _ => .aux .add ⟨0, by decide⟩
  | .aux .add _ => .free (.inl 1)
  | .free (.inl _) => .aux .add ⟨1, by decide⟩
  | .wire w _ => w.elim

end MulSucc

/-- The rule for `mul ⋈ S`: `(S x) * y = x * y + y`. -/
def mulSucc : Net arith (Fin 2 ⊕ Fin 1) where
  Agent := MulSucc.Agent
  Wire := Empty
  label := MulSucc.label
  link := MulSucc.link
  link_link := by decide
  link_ne := by decide
  link_free := by decide

/-- The rules of unary arithmetic, for an operation (`add`, `mul`, `ε`, `δ`) facing a numeral
(`Z`, `S`). The rules for a numeral facing an operation are obtained by swapping the
interface. -/
def arithRule : (α β : arith.Sym) → Option (Net arith (Fin (arith.arity α) ⊕ Fin (arith.arity β)))
  | .add, .zero => some addZero
  | .zero, .add => some addZero.swap
  | .add, .succ => some addSucc
  | .succ, .add => some addSucc.swap
  | .mul, .zero => some mulZero
  | .zero, .mul => some mulZero.swap
  | .mul, .succ => some mulSucc
  | .succ, .mul => some mulSucc.swap
  | .erase, .zero => some eraseZero
  | .zero, .erase => some eraseZero.swap
  | .erase, .succ => some eraseSucc
  | .succ, .erase => some eraseSucc.swap
  | .dup, .zero => some dupZero
  | .zero, .dup => some dupZero.swap
  | .dup, .succ => some dupSucc
  | .succ, .dup => some dupSucc.swap
  | _, _ => none

/-- The interaction system of unary arithmetic. -/
def arithSystem : InteractionSystem arith where
  rule := arithRule
  rule_swap α β N h := by
    cases α <;> cases β <;> cases h
    all_goals first
      | exact ⟨_, rfl, Setoid.refl _⟩
      | exact ⟨_, rfl, (Net.swapSwap _).symm.equiv⟩

/-- There is no rule for `S ⋈ Z`: their active pair is a deadlock. -/
example : arithSystem.rule .succ .zero = none := rfl

/-! ### Reduction -/

/-- `S Z + Z` reduces, by the rule for `add ⋈ S`. -/
example : ∃ N', arithSystem.Step onePlusZero N' :=
  ⟨_, InteractionSystem.step_removePair
    (show onePlusZero.IsActivePair OnePlusZero.Agent.add OnePlusZero.Agent.s from rfl).isActivePairW
    (R := addSucc) rfl⟩

/-- `mul ⋈ S` reduces to the right-hand side of its rule, `add (mul x y₁) y₂` with `y`
duplicated into `y₁` and `y₂`. -/
example : arithSystem.Step (Net.activePair (S := arith) .mul .succ) mulSucc :=
  InteractionSystem.step_activePair rfl

/-- The numeral `S Z` is in normal form. -/
example : arithSystem.Normal (zero.glue succAux) :=
  have : IsEmpty (zero.glue succAux).Wire := inferInstanceAs (IsEmpty (Empty ⊕ Empty))
  InteractionSystem.normal_of_isNormal (by rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) ⟨⟩)

/-- `Z` glued to the principal port of `S` is in normal form, although it has an active pair:
there is no rule for `Z ⋈ S`. -/
example : arithSystem.Normal (zero.glue succPri) :=
  InteractionSystem.normal_iff.mpr fun a b _ => by
    rcases a with ⟨⟩ | ⟨⟩ <;> rcases b with ⟨⟩ | ⟨⟩ <;> rfl

end Examples

module

public import LeanInets.Signature
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-!
# Ports

The ports of a net are the free ports of its interface, the principal and auxiliary
ports of its agents, and the two ends of its wires.

`Port` is parameterised by the agent labelling (rather than by a `Net`) because the
wiring of a net is itself a function on ports, so ports must be definable before nets.
-/

@[expose] public section

/-- The two ends of a wire. -/
inductive Side where
  | l
  | r
  deriving DecidableEq, Repr

namespace Side

/-- Sides correspond to booleans; used to transfer instances. -/
def equivBool : Side ≃ Bool where
  toFun | l => false | r => true
  invFun | false => l | true => r
  left_inv s := by cases s <;> rfl
  right_inv b := by cases b <;> rfl

instance : Fintype Side := Fintype.ofEquiv _ equivBool.symm

/-- The other end of a wire. -/
def flip : Side → Side
  | l => r
  | r => l

@[simp] theorem flip_l : flip l = r := rfl
@[simp] theorem flip_r : flip r = l := rfl
@[simp] theorem flip_flip (s : Side) : s.flip.flip = s := by cases s <;> rfl
theorem flip_ne (s : Side) : s.flip ≠ s := by cases s <;> nofun

end Side

/-- The ports of a net whose agents are `Agent` (labelled by `label`), whose wires are
`Wire`, and whose interface is `ι`. -/
inductive Port {S : Signature} {Agent : Type} (label : Agent → S.Sym) (Wire ι : Type) where
  /-- A free port of the interface. -/
  | free (i : ι)
  /-- The principal port of an agent. -/
  | pri (a : Agent)
  /-- The `k`-th auxiliary port of an agent. -/
  | aux (a : Agent) (k : Fin (S.arity (label a)))
  /-- One end of a wire. -/
  | wire (w : Wire) (s : Side)
  deriving DecidableEq

namespace Port

variable {S : Signature} {Agent : Type} {label : Agent → S.Sym} {Wire ι : Type}

/-- Ports are a plain sum type; used to transfer instances such as `Fintype`. -/
def equivSum :
    Port label Wire ι ≃ ι ⊕ Agent ⊕ (Σ a, Fin (S.arity (label a))) ⊕ Wire × Side where
  toFun
    | free i => .inl i
    | pri a => .inr (.inl a)
    | aux a k => .inr (.inr (.inl ⟨a, k⟩))
    | wire w s => .inr (.inr (.inr (w, s)))
  invFun
    | .inl i => free i
    | .inr (.inl a) => pri a
    | .inr (.inr (.inl ⟨a, k⟩)) => aux a k
    | .inr (.inr (.inr (w, s))) => wire w s
  left_inv p := by cases p <;> rfl
  right_inv x := by rcases x with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ <;> rfl

instance [Fintype ι] [Fintype Agent] [Fintype Wire] : Fintype (Port label Wire ι) :=
  Fintype.ofEquiv _ equivSum.symm

/-- Whether a port belongs to an entity (an agent or a wire) rather than the interface. -/
def IsEntity : Port label Wire ι → Prop
  | free _ => False
  | _ => True

instance : DecidablePred (IsEntity (label := label) (Wire := Wire) (ι := ι)) := fun p => by
  cases p <;> unfold IsEntity <;> infer_instance

@[simp] theorem not_isEntity_free (i : ι) : ¬ (free i : Port label Wire ι).IsEntity := id
@[simp] theorem isEntity_pri (a : Agent) : (pri a : Port label Wire ι).IsEntity := trivial
@[simp] theorem isEntity_aux (a : Agent) (k) : (aux a k : Port label Wire ι).IsEntity :=
  trivial
@[simp] theorem isEntity_wire (w : Wire) (s) : (wire w s : Port label Wire ι).IsEntity :=
  trivial

end Port

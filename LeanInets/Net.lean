module

public import LeanInets.Port
public import Mathlib.Logic.Equiv.Defs

/-!
# Interaction nets

A net consists of finitely many *entities* — agents and wires — together with an
interface of free ports. Every port is linked to exactly one other port; we encode this as
a fixed-point-free involution `link` on ports.

Wires are entities in their own right (with two ports and no principal port). This lets us
require that free ports are only ever linked to entity ports, so that gluing nets along
their interfaces never creates chains of free ports that would have to be followed. The
price is that nets differing only by chains of wires are no longer isomorphic; they will be
identified by a coarser equivalence that only looks at connections through wires.
-/

@[expose] public section

/-- An interaction net over the signature `S` with interface `ι`. -/
structure Net (S : Signature) (ι : Type) where
  /-- The agents of the net. -/
  Agent : Type
  /-- The wires of the net. -/
  Wire : Type
  [agentFintype : Fintype Agent]
  [wireFintype : Fintype Wire]
  /-- The symbol each agent is labelled with. -/
  label : Agent → S.Sym
  /-- Each port is linked to exactly one other port. -/
  link : Port label Wire ι → Port label Wire ι
  link_link : ∀ p, link (link p) = p
  link_ne : ∀ p, link p ≠ p
  /-- Free ports are only linked to ports of agents or wires, never to each other. -/
  link_free : ∀ i, (link (.free i)).IsEntity

namespace Net

attribute [instance] agentFintype wireFintype

variable {S : Signature} {ι : Type} (N : Net S ι)

/-- The ports of the net `N`. -/
abbrev Port := _root_.Port N.label N.Wire ι

theorem link_involutive : Function.Involutive N.link := N.link_link

theorem link_injective : Function.Injective N.link := N.link_involutive.injective

theorem link_eq_comm {p q : N.Port} : N.link p = q ↔ N.link q = p := by
  constructor <;> rintro rfl <;> exact N.link_link _

/-! ### Active pairs -/

/-- Two agents form an active pair if their principal ports are linked. -/
def IsActivePair (a b : N.Agent) : Prop := N.link (.pri a) = .pri b

instance [DecidableEq N.Agent] [DecidableEq ι] [DecidableEq N.Wire] (a b : N.Agent) :
    Decidable (N.IsActivePair a b) :=
  inferInstanceAs (Decidable (N.link (.pri a) = .pri b))

variable {N}

theorem IsActivePair.symm {a b : N.Agent} (h : N.IsActivePair a b) : N.IsActivePair b a :=
  N.link_eq_comm.mp h

theorem IsActivePair.ne {a b : N.Agent} (h : N.IsActivePair a b) : a ≠ b := by
  rintro rfl
  exact N.link_ne _ h

variable (N)

/-- A net is in normal form if it has no active pairs. -/
def IsNormal : Prop := ∀ a b, ¬ N.IsActivePair a b

end Net

/-- The empty net, on an empty interface. -/
def Net.empty (S : Signature) (ι : Type) [IsEmpty ι] : Net S ι where
  Agent := Empty
  Wire := Empty
  label := Empty.elim
  link p := p
  link_link _ := rfl
  link_ne p := by rcases p with i | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩; exact isEmptyElim i
  link_free i := isEmptyElim i

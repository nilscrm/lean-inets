module

public import LeanInets.WireIso

/-!
# Interaction systems

An interaction rule for a pair of symbols `α`, `β` replaces the active pair `α ⋈ β`
(`Net.activePair α β`) by a net with the same interface: the auxiliary ports of `α` followed
by those of `β`, i.e. `Fin (arity α) ⊕ Fin (arity β)`.

An interaction system (`InteractionSystem`) gives at most one rule for each pair of symbols
(`rule α β` is an `Option`), and its rules are symmetric: the rule for `β ⋈ α` is the rule
for `α ⋈ β` with the two halves of its interface swapped. Since reduction will be defined up
to `≈`, symmetry is only required up to `≈`. For `α = β` it says that the rule itself is
symmetric (`InteractionSystem.rule_self`).
-/

@[expose] public section

namespace Net

variable {S : Signature}

/-! ### Active pairs as nets -/

namespace ActivePair

/-- The two agents of an active pair. -/
inductive Agent where
  | left
  | right
  deriving DecidableEq, Repr

instance : Fintype Agent :=
  Fintype.ofList [.left, .right] (by intro a; cases a <;> decide)

/-- Exchanging the two agents of an active pair. -/
def Agent.swap : Agent ≃ Agent where
  toFun | .left => .right | .right => .left
  invFun | .left => .right | .right => .left
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

/-- The left agent is labelled `α`, the right agent `β`. -/
def label (α β : S.Sym) : Agent → S.Sym
  | .left => α
  | .right => β

/-- The links of `α ⋈ β`: the principal ports are linked to each other, and the auxiliary
ports to the corresponding free ports. -/
def link (α β : S.Sym) :
    _root_.Port (ActivePair.label α β) Empty (Fin (S.arity α) ⊕ Fin (S.arity β)) →
      _root_.Port (ActivePair.label α β) Empty (Fin (S.arity α) ⊕ Fin (S.arity β))
  | .pri .left => .pri .right
  | .pri .right => .pri .left
  | .aux .left k => .free (.inl k)
  | .aux .right k => .free (.inr k)
  | .free (.inl k) => .aux .left k
  | .free (.inr k) => .aux .right k
  | .wire w _ => w.elim

end ActivePair

/-- The active pair `α ⋈ β`: an agent labelled `α` and an agent labelled `β` whose principal
ports are linked. Its interface consists of the auxiliary ports of `α`, followed by those of
`β`. This is the left-hand side of an interaction rule. -/
@[reducible] def activePair (α β : S.Sym) : Net S (Fin (S.arity α) ⊕ Fin (S.arity β)) where
  Agent := ActivePair.Agent
  Wire := Empty
  label := ActivePair.label α β
  link := ActivePair.link α β
  link_link p := by rcases p with (_ | _) | (_ | _) | ⟨_ | _, _⟩ | ⟨⟨⟩, _⟩ <;> rfl
  link_ne p := by rcases p with (_ | _) | (_ | _) | ⟨_ | _, _⟩ | ⟨⟨⟩, _⟩ <;> nofun
  link_free := by rintro (_ | _) <;> trivial

theorem activePair_isActivePair (α β : S.Sym) :
    (activePair α β).IsActivePair .left .right := rfl

/-- `α ⋈ β` with its interface swapped is `β ⋈ α`. -/
def activePairSwap (α β : S.Sym) : Iso (activePair α β).swap (activePair β α) where
  agent := ActivePair.Agent.swap
  wire := .refl _
  label_agent a := by cases a <;> rfl
  link_map p := by rcases p with (_ | _) | (_ | _) | ⟨_ | _, _⟩ | ⟨⟨⟩, _⟩ <;> rfl

end Net

/-! ### Interaction systems -/

/-- An interaction system over the signature `S`: at most one rule for each pair of symbols,
such that the rules are symmetric. -/
structure InteractionSystem (S : Signature) where
  /-- The right-hand side of the rule for `α ⋈ β`, if there is one. It has the same
  interface as `Net.activePair α β`. -/
  rule : (α β : S.Sym) → Option (Net S (Fin (S.arity α) ⊕ Fin (S.arity β)))
  /-- If `α ⋈ β` rewrites to `N`, then `β ⋈ α` rewrites to `N` with its interface swapped,
  up to `≈`. -/
  rule_swap : ∀ α β N, rule α β = some N → ∃ M, rule β α = some M ∧ M ≈ N.swap

namespace InteractionSystem

variable {S : Signature} (I : InteractionSystem S)

/-- There is a rule for `α ⋈ β` iff there is one for `β ⋈ α`. -/
theorem isSome_rule_comm (α β : S.Sym) : (I.rule α β).isSome = (I.rule β α).isSome := by
  have h {α β : S.Sym} : (I.rule α β).isSome → (I.rule β α).isSome := fun h => by
    obtain ⟨M, hM, -⟩ := I.rule_swap α β _ (Option.some_get h).symm
    rw [hM]
    rfl
  exact Bool.eq_iff_iff.mpr ⟨h, h⟩

/-- The rule for `α ⋈ α` is symmetric. -/
theorem rule_self {α : S.Sym} {N} (h : I.rule α α = some N) : N.swap ≈ N := by
  obtain ⟨M, hM, hMN⟩ := I.rule_swap α α N h
  obtain rfl : M = N := Option.some.inj (hM.symm.trans h)
  exact Setoid.symm hMN

end InteractionSystem

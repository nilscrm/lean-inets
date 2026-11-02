module

public import LeanInets.Confluence
public import LeanInets.Unit

/-!
# Interaction combinators

Lafont's interaction combinators: the symbols `γ` and `δ` with two auxiliary ports each, and
`ε` with none. Their six rules (up to symmetry):

* `γ ⋈ γ` and `δ ⋈ δ` annihilate: the auxiliary ports of the two agents are connected by wires,
  crossed for `γ` and in parallel for `δ`;
* `ε ⋈ ε` vanishes;
* `γ ⋈ δ` commutes: two `δ`s on the auxiliary ports of `γ`, two `γ`s on those of `δ`, connected
  in a square;
* `γ ⋈ ε` and `δ ⋈ ε` erase: an `ε` on each auxiliary port of the other agent.

Every pair of symbols has a rule, so a net is in normal form iff it has no active pairs up to
wires (`Combinators.normal_iff`). The rules for `γ ⋈ γ` and `δ ⋈ δ` are symmetric only up to
wires, since swapping their interfaces reverses their wires.

The file ends with a complete reduction: an `ε` erasing a `γ` whose auxiliary ports carry two
more `ε`s reaches the empty net in three steps, and by confluence every reduction to normal form
does (`Combinators.epsGamma_normalize`).
-/

@[expose] public section

namespace Combinators

open Net

/-- The symbols of the interaction combinators. -/
inductive Sym where
  | γ
  | δ
  | ε
  deriving DecidableEq, Repr

/-- The signature of the interaction combinators. -/
def sig : Signature where
  Sym := Sym
  arity
    | .γ => 2
    | .δ => 2
    | .ε => 0

/-! ### Nets of wires -/

/-- A net of wires connecting the free port `inl k` to the free port `inr (σ k)`. -/
def wires {κ : Type} [Fintype κ] (σ : κ ≃ κ) : Net sig (κ ⊕ κ) :=
  (idNet sig κ).reindex (Equiv.sumCongr (.refl κ) σ)

variable {κ : Type} [Fintype κ] (σ : κ ≃ κ)

theorem wires_partner (k : κ) : (wires σ).Partner (.free (.inl k)) (.free (.inr (σ k))) :=
  (reindexIso _ (idNet sig κ)).wireIso.partner_map (idNet_partner k)

theorem wires_swap_partner (k : κ) :
    (wires σ).swap.Partner (.free (.inr k)) (.free (.inl (σ k))) :=
  (reindexIso _ (wires σ)).wireIso.partner_map (wires_partner σ k)

/-- Swapping the interface of a net of wires inverts the permutation, up to wires. -/
def wiresSwap : WireIso (wires σ).swap (wires σ.symm) where
  agent := .refl Empty
  iface := .refl _
  label_agent a := a.elim
  partner_map {x y} h := by
    rcases x with (k | k) | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩
    · have := wires_swap_partner σ (σ.symm k)
      rw [Equiv.apply_symm_apply] at this
      obtain rfl := h.unique this.symm
      exact (wires_partner σ.symm k)
    · obtain rfl := h.unique (wires_swap_partner σ k)
      have := (wires_partner σ.symm (σ k)).symm
      rwa [Equiv.symm_apply_apply] at this

/-! ### The rules -/

/-- The rule for `γ ⋈ γ`: crossed wires. -/
def gammaGamma : Net sig (Fin 2 ⊕ Fin 2) := wires (Equiv.swap 0 1)

/-- The rule for `δ ⋈ δ`: parallel wires. -/
def deltaDelta : Net sig (Fin 2 ⊕ Fin 2) := wires (.refl _)

/-- The rule for `ε ⋈ ε`: the empty net. -/
def epsEps : Net sig (Fin 0 ⊕ Fin 0) := Net.empty _ _

namespace Commute

/-- The agents of the rule for `γ ⋈ δ`: a `δ` for each auxiliary port of `γ`, and a `γ` for each
auxiliary port of `δ`. -/
inductive Agent where
  | δ (i : Fin 2)
  | γ (j : Fin 2)
  deriving DecidableEq

instance : Fintype Agent :=
  Fintype.ofList [.δ 0, .δ 1, .γ 0, .γ 1]
    (by intro a; cases a <;> rename_i i <;> revert i <;> decide)

/-- The symbol of each agent. -/
def label : Agent → sig.Sym
  | .δ _ => .δ
  | .γ _ => .γ

/-- The wiring of the rule for `γ ⋈ δ`: the `i`-th auxiliary port of the `j`-th new `γ` is
linked to the `j`-th auxiliary port of the `i`-th new `δ`. -/
def link : Port label Empty (Fin 2 ⊕ Fin 2) → Port label Empty (Fin 2 ⊕ Fin 2)
  | .pri (.δ i) => .free (.inl i)
  | .pri (.γ j) => .free (.inr j)
  | .free (.inl i) => .pri (.δ i)
  | .free (.inr j) => .pri (.γ j)
  | .aux (.δ i) j => .aux (.γ j) i
  | .aux (.γ j) i => .aux (.δ i) j
  | .wire w _ => w.elim

end Commute

/-- The rule for `γ ⋈ δ`. -/
def commute : Net sig (Fin 2 ⊕ Fin 2) where
  Agent := Commute.Agent
  Wire := Empty
  label := Commute.label
  link := Commute.link
  link_link := by decide
  link_ne := by decide
  link_free := by decide

/-- Two `ε` agents. -/
def epsLabel : Fin 2 → sig.Sym := fun _ => .ε

/-- The rule for `γ ⋈ ε` and `δ ⋈ ε`: an `ε` on each auxiliary port. -/
def erase : Net sig (Fin 2 ⊕ Fin 0) where
  Agent := Fin 2
  Wire := Empty
  label := epsLabel
  link
    | .pri i => .free (.inl i)
    | .free (.inl i) => .pri i
    | .free (.inr k) => k.elim0
    | .aux _ k => k.elim0
    | .wire w _ => w.elim
  link_link := by decide
  link_ne := by decide
  link_free := by decide

/-- The rules of the interaction combinators. -/
def rule : (α β : sig.Sym) → Option (Net sig (Fin (sig.arity α) ⊕ Fin (sig.arity β)))
  | .γ, .γ => some gammaGamma
  | .δ, .δ => some deltaDelta
  | .ε, .ε => some epsEps
  | .γ, .δ => some commute
  | .δ, .γ => some commute.swap
  | .γ, .ε => some erase
  | .ε, .γ => some erase.swap
  | .δ, .ε => some erase
  | .ε, .δ => some erase.swap

/-- The interaction system of the interaction combinators. -/
def system : InteractionSystem sig where
  rule := rule
  rule_swap α β := by
    cases α <;> cases β
    all_goals try first
      | exact .some (Setoid.refl _)
      | exact .some (Setoid.symm (Net.swap_swap_equiv _))
    · refine .some ?_
      have := (wiresSwap (Equiv.swap (0 : Fin 2) 1)).equiv
      rw [Equiv.symm_swap] at this
      exact Setoid.symm this
    · exact .some (Setoid.symm (wiresSwap (.refl _)).equiv)
    · exact .some (WireIso.equiv
        { agent := .refl _
          iface := .refl _
          label_agent := nofun
          partner_map := fun {x} => by
            rcases x with (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩) | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩ })

/-- Every pair of interaction combinators has a rule. -/
theorem isSome_rule (α β : sig.Sym) : (system.rule α β).isSome := by
  cases α <;> cases β <;> rfl

/-- A net of interaction combinators is in normal form iff it has no active pairs up to
wires. -/
theorem normal_iff {ι : Type} {N : Net sig ι} :
    system.Normal N ↔ ∀ a b, ¬ N.IsActivePairW a b := by
  rw [InteractionSystem.normal_iff]
  refine forall₂_congr fun a b => ⟨fun h hab => ?_, fun h hab => absurd hab h⟩
  have := isSome_rule (N.label a) (N.label b)
  rw [h hab] at this
  cases this

/-! ### An example reduction

An `ε` facing a `γ` whose auxiliary ports are connected to two more `ε`s. Erasing the `γ`
creates two `ε ⋈ ε` pairs, so the net reduces to the empty net in three steps. -/

/-- Two `ε`s on the hole ports `inr i`. -/
def epsCtx : Net sig (Empty ⊕ (Fin 0 ⊕ Fin 2)) where
  Agent := Fin 2
  Wire := Empty
  label := epsLabel
  link
    | .pri i => .free (.inr (.inr i))
    | .free (.inr (.inr i)) => .pri i
    | .free (.inr (.inl k)) => k.elim0
    | .free (.inl e) => e.elim
    | .aux _ k => k.elim0
    | .wire w _ => w.elim
  link_link := by decide
  link_ne := by decide
  link_free := by decide

/-- The net: `ε ⋈ γ`, with an `ε` on each auxiliary port of `γ`. -/
def epsGamma : Net sig Empty := epsCtx.plug (activePair (S := sig) .ε .γ)

/-- The context of a single `ε ⋈ ε` pair, with an empty hole. -/
def epsPairCtx : Net sig (Empty ⊕ (Fin 0 ⊕ Fin 0)) :=
  (activePair (S := sig) .ε .ε).reindex (Equiv.emptySum Empty _).symm

/-- The empty context. -/
def emptyCtx : Net sig (Empty ⊕ (Fin 0 ⊕ Fin 0)) := Net.empty _ _

/-- The agents after erasing the `γ`: the two `ε`s of the context face the two new `ε`s. -/
def erasedAgent : Fin 2 ⊕ Fin 2 ≃ ActivePair.Agent ⊕ ActivePair.Agent where
  toFun
    | .inl ⟨0, _⟩ => .inl .left
    | .inl _ => .inr .left
    | .inr ⟨0, _⟩ => .inl .right
    | .inr _ => .inr .right
  invFun
    | .inl .left => .inl 0
    | .inr .left => .inl 1
    | .inl .right => .inr 0
    | .inr .right => .inr 1
  left_inv := by decide
  right_inv := by decide

/-- After erasing the `γ`, the net consists of two `ε ⋈ ε` pairs. -/
def erasedIso : Iso (epsCtx.plug erase.swap) (epsPairCtx.plug (activePair (S := sig) .ε .ε)) where
  agent := erasedAgent
  wire := .refl _
  iface := .refl _
  label_agent := by rintro (⟨_ | _ | _, _⟩ | ⟨_ | _ | _, _⟩) <;> rfl
  link_map := by
    rintro (⟨⟨⟩⟩ | (⟨_ | _ | _, _⟩ | ⟨_ | _ | _, _⟩) | ⟨a | a, k⟩ | ⟨⟨⟩ | ⟨⟩, _⟩)
    all_goals first | rfl | omega | exact Fin.elim0 ‹_› | (rename_i _ w; exact Empty.elim w)

/-- After the first `ε ⋈ ε` pair vanishes, the other one is left. -/
def oneErasedIso :
    Iso (epsPairCtx.plug epsEps) (emptyCtx.plug (activePair (S := sig) .ε .ε)) where
  agent := Equiv.sumComm _ _
  wire := .refl _
  iface := .refl _
  label_agent := by rintro ((_ | _) | ⟨⟩) <;> rfl
  link_map := by
    rintro (⟨⟨⟩⟩ | ((_ | _) | ⟨⟩) | ⟨(_ | _) | ⟨⟩, k⟩ | ⟨⟨⟩ | ⟨⟩, _⟩)
    all_goals first | rfl | exact Fin.elim0 ‹_› | (rename_i _ w; exact Empty.elim w)

/-- The empty net, as plugged into the empty context. -/
theorem normal_emptyCtx_plug : system.Normal (emptyCtx.plug epsEps) :=
  normal_iff.mpr fun a => by rcases a with a | a <;> exact Empty.elim a

/-- `epsGamma` reduces to the empty net in three steps. -/
theorem epsGamma_reducesIn : system.ReducesIn 3 epsGamma (emptyCtx.plug epsEps) :=
  .succ (InteractionSystem.step_plug (I := system) (α := Sym.ε) (β := Sym.γ) (R := erase.swap)
      rfl epsCtx) <|
    .succ ((InteractionSystem.step_plug (I := system) (α := Sym.ε) (β := Sym.ε) (R := epsEps) rfl
      epsPairCtx).of_equiv erasedIso.symm.equiv (Setoid.refl _)) <|
    .succ ((InteractionSystem.step_plug (I := system) (α := Sym.ε) (β := Sym.ε) (R := epsEps) rfl
      emptyCtx).of_equiv oneErasedIso.symm.equiv (Setoid.refl _)) <|
    .zero (Setoid.refl _)

/-- Every reduction of `epsGamma` to normal form takes three steps and ends in the empty net. -/
theorem epsGamma_normalize {n : ℕ} {N : Net sig Empty} (h : system.ReducesIn n epsGamma N)
    (hN : system.Normal N) : n = 3 ∧ N ≈ emptyCtx.plug epsEps := by
  obtain ⟨h₁, h₂⟩ := epsGamma_reducesIn.length_eq normal_emptyCtx_plug h hN
  exact ⟨h₁.symm, Setoid.symm h₂⟩

end Combinators

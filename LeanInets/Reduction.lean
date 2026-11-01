module

public import LeanInets.Context

/-!
# Reduction

A net `N` reduces in one step to `N'` (`I.Step N N'`) if, up to wires, `N` is an active pair
`α ⋈ β` plugged into a context `C`, and `N'` is the right-hand side of the rule for `α ⋈ β`
plugged into the same context:
`N ≈ C.plug (activePair α β)` and `N' ≈ C.plug R` where `I.rule α β = some R`.
Multi-step reduction (`I.Reduces`) is its reflexive transitive closure, and a net is in normal
form (`I.Normal`) if it does not reduce.

Since reduction is defined up to `≈`, it does not see wires: an active pair may be connected
through any number of wires. The redexes of a net are exactly its active pairs up to wires
whose symbols have a rule (`exists_step_iff`). The hard direction is cutting an active pair out
of its net, which is `Net.equiv_plug_removePair`.
-/

@[expose] public section

namespace InteractionSystem

open Net

variable {S : Signature} (I : InteractionSystem S) {ι : Type}

/-- One reduction step: up to wires, `N` is an active pair `α ⋈ β` in a context `C`, and `N'`
is the right-hand side of the rule for `α ⋈ β` in the same context. -/
def Step (N N' : Net S ι) : Prop :=
  ∃ (α β : S.Sym) (R : Net S (Fin (S.arity α) ⊕ Fin (S.arity β)))
    (C : Net S (ι ⊕ (Fin (S.arity α) ⊕ Fin (S.arity β)))),
    I.rule α β = some R ∧ N ≈ C.plug (activePair α β) ∧ N' ≈ C.plug R

/-- Multi-step reduction: the reflexive transitive closure of `Step`, up to `≈`. Without the
`≈`, a net would not reduce in zero steps to a net that differs from it only in its wires. -/
def Reduces (N N' : Net S ι) : Prop := ∃ M, Relation.ReflTransGen I.Step N M ∧ M ≈ N'

/-- A net is in normal form if it does not reduce. -/
def Normal (N : Net S ι) : Prop := ∀ N', ¬ I.Step N N'

variable {I}

/-- A rule applied in a context is a reduction step. -/
theorem step_plug {α β : S.Sym} {R : Net S (Fin (S.arity α) ⊕ Fin (S.arity β))}
    (hR : I.rule α β = some R) (C : Net S (ι ⊕ (Fin (S.arity α) ⊕ Fin (S.arity β)))) :
    I.Step (C.plug (activePair α β)) (C.plug R) :=
  ⟨α, β, R, C, hR, Setoid.refl _, Setoid.refl _⟩

/-- An active pair reduces to the right-hand side of its rule. -/
theorem step_activePair {α β : S.Sym} {R : Net S (Fin (S.arity α) ⊕ Fin (S.arity β))}
    (hR : I.rule α β = some R) : I.Step (activePair α β) R :=
  ⟨α, β, R, idNet S _, hR, Setoid.symm (idNet_plug _), Setoid.symm (idNet_plug _)⟩

/-- Reduction is closed under contexts. -/
theorem Step.plug {κ : Type} {R R' : Net S κ} (h : I.Step R R') (C : Net S (ι ⊕ κ)) :
    I.Step (C.plug R) (C.plug R') := by
  obtain ⟨α, β, Q, C', hQ, hR, hR'⟩ := h
  exact ⟨α, β, Q, C.glue C', hQ,
    Setoid.trans (plug_equiv (Setoid.refl C) hR) (plugPlug C C' _).equiv,
    Setoid.trans (plug_equiv (Setoid.refl C) hR') (plugPlug C C' _).equiv⟩

/-! ### Reduction respects `≈` -/

theorem Step.of_equiv {N N' M M' : Net S ι} (h : I.Step N N') (hN : N ≈ M) (hN' : N' ≈ M') :
    I.Step M M' :=
  let ⟨α, β, R, C, hR, h₁, h₂⟩ := h
  ⟨α, β, R, C, hR, Setoid.trans (Setoid.symm hN) h₁, Setoid.trans (Setoid.symm hN') h₂⟩

theorem step_congr {N N' M M' : Net S ι} (hN : N ≈ M) (hN' : N' ≈ M') :
    I.Step N N' ↔ I.Step M M' :=
  ⟨fun h => h.of_equiv hN hN', fun h => h.of_equiv (Setoid.symm hN) (Setoid.symm hN')⟩

theorem Step.reduces {N N' : Net S ι} (h : I.Step N N') : I.Reduces N N' :=
  ⟨N', .single h, Setoid.refl _⟩

theorem Reduces.of_equiv {N N' : Net S ι} (h : N ≈ N') : I.Reduces N N' := ⟨N, .refl, h⟩

theorem Reduces.refl (N : Net S ι) : I.Reduces N N := .of_equiv (Setoid.refl N)

/-- A reduction can start at any net equivalent to its source. -/
theorem reflTransGen_step_of_equiv {N M N' : Net S ι} (h : Relation.ReflTransGen I.Step N N')
    (hN : N ≈ M) : I.Reduces M N' := by
  rcases h.cases_head with rfl | ⟨K, hK, h⟩
  · exact .of_equiv (Setoid.symm hN)
  · exact ⟨N', h.head (hK.of_equiv hN (Setoid.refl K)), Setoid.refl _⟩

theorem Reduces.trans {N N' N'' : Net S ι} (h : I.Reduces N N') (h' : I.Reduces N' N'') :
    I.Reduces N N'' := by
  obtain ⟨M, hM, hMN'⟩ := h
  obtain ⟨M', hM', hM'N''⟩ := h'
  obtain ⟨K, hK, hKM'⟩ := reflTransGen_step_of_equiv hM' (Setoid.symm hMN')
  exact ⟨K, hM.trans hK, Setoid.trans hKM' hM'N''⟩

theorem Reduces.head {N N' N'' : Net S ι} (h : I.Step N N') (h' : I.Reduces N' N'') :
    I.Reduces N N'' :=
  h.reduces.trans h'

theorem Reduces.tail {N N' N'' : Net S ι} (h : I.Reduces N N') (h' : I.Step N' N'') :
    I.Reduces N N'' :=
  h.trans h'.reduces

theorem reduces_congr {N N' M M' : Net S ι} (hN : N ≈ M) (hN' : N' ≈ M') :
    I.Reduces N N' ↔ I.Reduces M M' := by
  have h {N N' M M' : Net S ι} (hN : N ≈ M) (hN' : N' ≈ M') (h : I.Reduces N N') :
      I.Reduces M M' :=
    ((Reduces.of_equiv (Setoid.symm hN)).trans h).trans (.of_equiv hN')
  exact ⟨h hN hN', h (Setoid.symm hN) (Setoid.symm hN')⟩

theorem Reduces.plug {κ : Type} {R R' : Net S κ} (h : I.Reduces R R') (C : Net S (ι ⊕ κ)) :
    I.Reduces (C.plug R) (C.plug R') := by
  obtain ⟨M, hM, hMR'⟩ := h
  exact ⟨C.plug M, Relation.ReflTransGen.lift _ (fun _ _ h => h.plug C) _ _ hM,
    plug_equiv (Setoid.refl C) hMR'⟩

theorem normal_congr {N M : Net S ι} (h : N ≈ M) : I.Normal N ↔ I.Normal M :=
  ⟨fun hN M' hM => hN M' (hM.of_equiv (Setoid.symm h) (Setoid.refl _)),
    fun hM N' hN => hM N' (hN.of_equiv h (Setoid.refl _))⟩

/-! ### Redexes are active pairs up to wires -/

/-- A net that reduces has an active pair up to wires whose symbols have a rule. -/
theorem Step.exists_isActivePairW {N N' : Net S ι} (h : I.Step N N') :
    ∃ a b, N.IsActivePairW a b ∧ (I.rule (N.label a) (N.label b)).isSome := by
  obtain ⟨α, β, R, C, hR, ⟨e⟩, -⟩ := h
  refine ⟨e.symm.agent (.inr .left), e.symm.agent (.inr .right),
    e.symm.isActivePairW_iff.mpr (isActivePair_plug_activePair C).isActivePairW, ?_⟩
  rw [e.symm.label_agent, e.symm.label_agent]
  change (I.rule α β).isSome
  rw [hR]
  rfl

/-- Every active pair up to wires whose symbols have a rule can be reduced. -/
theorem step_removePair {N : Net S ι} {a b : N.Agent} (h : N.IsActivePairW a b)
    {R : Net S (Fin (S.arity (N.label a)) ⊕ Fin (S.arity (N.label b)))}
    (hR : I.rule (N.label a) (N.label b) = some R) :
    I.Step N ((N.removePair a b h.1).plug R) :=
  ⟨_, _, R, _, hR, equiv_plug_removePair h, Setoid.refl _⟩

/-- A net reduces iff it has an active pair up to wires whose symbols have a rule. -/
theorem exists_step_iff {N : Net S ι} :
    (∃ N', I.Step N N') ↔ ∃ a b, N.IsActivePairW a b ∧ (I.rule (N.label a) (N.label b)).isSome :=
  ⟨fun ⟨_, h⟩ => h.exists_isActivePairW, fun ⟨_, _, h, hR⟩ =>
    ⟨_, step_removePair h (Option.some_get hR).symm⟩⟩

/-- A net is in normal form iff none of its active pairs up to wires has a rule. -/
theorem normal_iff {N : Net S ι} :
    I.Normal N ↔ ∀ a b, N.IsActivePairW a b → I.rule (N.label a) (N.label b) = none := by
  simp only [Normal, ← not_exists, exists_step_iff, Option.isSome_iff_ne_none]
  push Not
  rfl

/-- A net without wires and without active pairs is in normal form. -/
theorem normal_of_isNormal {N : Net S ι} [IsEmpty N.Wire] (h : N.IsNormal) : I.Normal N :=
  normal_iff.mpr fun a b hab => absurd (isActivePairW_iff_of_isEmpty.mp hab) (h a b)

end InteractionSystem

module

public import LeanInets.Decompose
public import LeanInets.Unit

/-!
# Contexts

Tools for reasoning about contexts and the nets plugged into them:

* two plugs into a context with two holes can be exchanged (`Net.plugExchange`);
* partners in a context are partners in the net obtained by plugging an active pair into it
  (`Net.partner_holeTPort_iff`);
* a context is determined, up to wires, by the net obtained by plugging an active pair into it
  (`Net.WireIso.ofPlugActivePair`).
-/

@[expose] public section

namespace Net

variable {S : Signature}

/-! ### Exchanging two holes -/

section exchange

/-- `(α ⊕ β) ⊕ γ ≃ (α ⊕ γ) ⊕ β`. -/
def sumRightComm (α β γ : Type) : (α ⊕ β) ⊕ γ ≃ (α ⊕ γ) ⊕ β where
  toFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr b) => .inr b
    | .inr c => .inl (.inr c)
  invFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr c) => .inr c
    | .inr b => .inl (.inr b)
  left_inv x := by rcases x with (_ | _) | _ <;> rfl
  right_inv x := by rcases x with (_ | _) | _ <;> rfl

variable {ι κ₁ κ₂ : Type} (D : Net S ((ι ⊕ κ₁) ⊕ κ₂)) (X : Net S κ₂) (Y : Net S κ₁)

/-- The context `D` with its two holes exchanged. -/
abbrev exchange : Net S ((ι ⊕ κ₂) ⊕ κ₁) := D.reindex (sumRightComm ι κ₁ κ₂)

/-- Exchanging the holes twice gives back the original context. -/
theorem exchange_exchange : D.exchange.exchange ≈ D :=
  ((reindexIso _ D).trans (reindexIso _ _)).symm.equiv

/-- Plugging into the two holes of a context can be done in either order. -/
def plugExchange : Iso ((D.plug X).plug Y) ((D.exchange.plug Y).plug X) :=
  (plugUnion D Y X).trans <|
    (Iso.plug ((reindexIso _ D).symm.trans ((reindexIso _ D).trans (reindexIso _ _)))
      (unionComm Y X) (.refl ι)).trans
    (plugUnion D.exchange X Y).symm

theorem plug_plug_equiv_exchange : (D.plug X).plug Y ≈ (D.exchange.plug Y).plug X :=
  (plugExchange D X Y).equiv

theorem plugExchange_agent (a : ((D.plug X).plug Y).Agent) :
    (plugExchange D X Y).agent a = sumRightComm _ _ _ a := by
  rcases a with (_ | _) | _ <;> rfl

end exchange

/-! ### Plugging an active pair -/

section activePair

variable {ι : Type} {α β : S.Sym} (C : Net S (ι ⊕ (Fin (S.arity α) ⊕ Fin (S.arity β))))

/-- Where a terminal port of the context ends up in `C.plug (activePair α β)`: the ports of the
hole become the auxiliary ports of the active pair. -/
def holeTPort : C.TPort → (C.plug (activePair α β)).TPort
  | .free (.inl i) => .free i
  | .free (.inr (.inl k)) => .aux (.inr .left) k
  | .free (.inr (.inr k)) => .aux (.inr .right) k
  | .pri c => .pri (.inl c)
  | .aux c k => .aux (.inl c) k

variable {C}

theorem holeTPort_injective : Function.Injective (holeTPort C) := by
  rintro ((i | k | k) | c | ⟨c, k⟩ | ⟨⟨⟩, _⟩) ((i' | k' | k') | c' | ⟨c', k'⟩ | ⟨⟨⟩, _⟩) h <;>
    simp only [holeTPort] at h <;> cases h <;> rfl

theorem tport_holeTPort (x : C.TPort) :
    (C.plug (activePair α β)).tport (holeTPort C x) = Plug.inl C _ (C.tport x) := by
  rcases x with (i | k | k) | c | ⟨c, k⟩ | ⟨⟨⟩, _⟩
  · rfl
  · rw [tport_free, Plug.inl_free_inr]
    rfl
  · rw [tport_free, Plug.inl_free_inr]
    rfl
  · rfl
  · rfl

/-- Partners in a context are partners in the plugged net. -/
theorem Partner.holeTPort {x y : C.TPort} (h : C.Partner x y) :
    (C.plug (activePair α β)).Partner (holeTPort C x) (holeTPort C y) :=
  Partner.map (Plug.inl C _) Sum.inl (Plug.link_inl C _) (fun _ _ => rfl)
    (tport_holeTPort x).symm (tport_holeTPort y).symm h

theorem partner_holeTPort_iff {x y : C.TPort} :
    (C.plug (activePair α β)).Partner (holeTPort C x) (holeTPort C y) ↔ C.Partner x y :=
  ⟨partner_reflect _ holeTPort_injective fun _ _ => Partner.holeTPort, Partner.holeTPort⟩

/-- Active pairs up to wires of the context are active pairs up to wires of the plugged net. -/
theorem isActivePairW_plug_activePair_iff {c d : C.Agent} :
    (C.plug (activePair α β)).IsActivePairW (.inl c) (.inl d) ↔ C.IsActivePairW c d :=
  and_congr (Sum.inl_injective.ne_iff) (partner_holeTPort_iff (x := .pri c) (y := .pri d))

end activePair

/-! ### Contexts are determined by plugging an active pair -/

section unique

variable {ι : Type} {α β : S.Sym} {C C' : Net S (ι ⊕ (Fin (S.arity α) ⊕ Fin (S.arity β)))}

/-- An equivalence of sums that fixes the right summand restricts to the left summands. -/
def restrictInl {A A' B : Type} (e : A ⊕ B ≃ A' ⊕ B) (h : ∀ b, e (.inr b) = .inr b) :
    A ≃ A' where
  toFun a := (e (.inl a)).getLeft (by
    rcases hb : e (.inl a) with _ | b
    · rfl
    · exact absurd (e.injective (hb.trans (h b).symm)) nofun)
  invFun a := (e.symm (.inl a)).getLeft (by
    rcases hb : e.symm (.inl a) with _ | b
    · rfl
    · rw [Equiv.symm_apply_eq, h b] at hb
      exact absurd hb nofun)
  left_inv a := by simp
  right_inv a := by simp

theorem inl_restrictInl {A A' B : Type} (e : A ⊕ B ≃ A' ⊕ B)
    (h : ∀ b, e (.inr b) = .inr b) (a : A) : .inl (restrictInl e h a) = e (.inl a) := by
  simp [restrictInl]

theorem WireIso.ofPlugActivePair_label
    (f : WireIso (C.plug (activePair α β)) (C'.plug (activePair α β)))
    (h : ∀ t, f.agent (.inr t) = .inr t) (c : C.Agent) :
    C'.label (restrictInl f.agent h c) = C.label c := by
  have := f.label_agent (.inl c)
  rw [← inl_restrictInl _ h] at this
  exact this

/-- If plugging the active pair `α ⋈ β` into two contexts gives nets that are isomorphic up to
wires, by an isomorphism that is the identity on the interface and maps the active pair to the
active pair, then the contexts are isomorphic up to wires. -/
def WireIso.ofPlugActivePair (f : WireIso (C.plug (activePair α β)) (C'.plug (activePair α β)))
    (hi : ∀ i, f.iface i = i) (h : ∀ t, f.agent (.inr t) = .inr t) : WireIso C C' where
  agent := restrictInl f.agent h
  iface := .refl _
  label_agent := ofPlugActivePair_label f h
  partner_map {x y} hxy := by
    have hp (z : C.TPort) : f.port (holeTPort C z) =
          holeTPort C' (z.map (restrictInl f.agent h) (ofPlugActivePair_label f h) id
            (Equiv.refl _)) := by
      rcases z with (i | k | k) | c | ⟨c, k⟩ | ⟨⟨⟩, _⟩
      · exact congrArg Port.free (hi i)
      · exact Port.aux_congr (h .left) rfl
      · exact Port.aux_congr (h .right) rfl
      · exact congrArg Port.pri (inl_restrictInl _ h c).symm
      · exact Port.aux_congr (inl_restrictInl _ h c).symm rfl
    rw [← partner_holeTPort_iff, ← hp, ← hp]
    exact f.partner_port (partner_holeTPort_iff.mpr hxy)

end unique

end Net

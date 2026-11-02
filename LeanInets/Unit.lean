module

public import LeanInets.WireIso

/-!
# The identity context

The identity net `idNet S κ` consists of one wire for each `k : κ`, connecting the free ports
`inl k` and `inr k`. Plugging a net into it puts a wire in front of each free port, so it gives
back the plugged net up to wires (`idNet_plug`), but not up to isomorphism.
-/

@[expose] public section

namespace Net

variable {S : Signature}

/-- The identity net on `κ`: a wire for each `k : κ`, with its left end linked to the free
port `inl k` and its right end linked to the free port `inr k`. -/
def idNet (S : Signature) (κ : Type) [Fintype κ] : Net S (κ ⊕ κ) where
  Agent := Empty
  Wire := κ
  label := Empty.elim
  link
    | .free (.inl k) => .wire k .l
    | .free (.inr k) => .wire k .r
    | .wire k .l => .free (.inl k)
    | .wire k .r => .free (.inr k)
    | .pri a => a.elim
    | .aux a _ => a.elim
  link_link p := by rcases p with (_ | _) | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨_, _ | _⟩ <;> rfl
  link_ne p := by rcases p with (_ | _) | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨_, _ | _⟩ <;> nofun
  link_free := by rintro (_ | _) <;> trivial

variable {κ : Type} [Fintype κ]

theorem idNet_partner (k : κ) : (idNet S κ).Partner (.free (.inl k)) (.free (.inr k)) :=
  .single (step_wire (N := idNet S κ) k .l)

variable (R : Net S κ)

/-- A net is isomorphic up to wires to the net plugged into the identity context. -/
def wireIsoIdNetPlug : WireIso R ((idNet S κ).plug R) where
  agent := (Equiv.emptySum Empty R.Agent).symm
  iface := .refl κ
  label_agent _ := rfl
  partner_map {x y} h := by
    have hstart : Relation.ReflTransGen ((idNet S κ).plug R).Step
        (((idNet S κ).plug R).link (((idNet S κ).plug R).tport
          (x.map (Equiv.emptySum Empty R.Agent).symm (fun _ => rfl) id id)))
        (Plug.inr (idNet S κ) R (R.link (R.tport x))) := by
      rcases x with k | _ | _ | ⟨⟨⟩, _⟩
      · change Relation.ReflTransGen _ (((idNet S κ).plug R).link (.free k)) _
        rw [Plug.link_free]
        exact .single (show ((idNet S κ).plug R).Step (.wire (.inl k) .l) _ from
          ((Plug.link_inl (idNet S κ) R (.wire k .r)).trans
            (Plug.inl_free_inr (idNet S κ) R k)).symm)
      all_goals exact .refl
    have hend : Relation.ReflTransGen ((idNet S κ).plug R).Step (Plug.inr (idNet S κ) R (R.tport y))
        (((idNet S κ).plug R).tport
          (y.map (Equiv.emptySum Empty R.Agent).symm (fun _ => rfl) id id)) := by
      rcases y with k | _ | _ | ⟨⟨⟩, _⟩
      · change Relation.ReflTransGen _ (Plug.inr (idNet S κ) R (.free k)) (.free k)
        rw [Plug.inr_free]
        exact .single (show ((idNet S κ).plug R).Step (.wire (.inl k) .r) _ from
          (Plug.link_inl (idNet S κ) R (.wire k .l)).symm)
      all_goals exact .refl
    exact hstart.trans ((reach_map (Plug.inr (idNet S κ) R) Sum.inr (Plug.link_inr _ _)
      (fun _ _ => rfl) h).trans hend)

/-- Plugging into the identity context gives back the plugged net, up to wires. -/
theorem idNet_plug : (idNet S κ).plug R ≈ R :=
  Setoid.symm (wireIsoIdNetPlug R).equiv

end Net

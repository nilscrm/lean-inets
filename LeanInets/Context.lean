module

public import LeanInets.Decompose
public import LeanInets.Unit

/-!
# Contexts

Tools for reasoning about nets of the form `C.plug R`:

* the ports of `C.plug R` come from the ports of `C` (`Plug.inl`) and of `R` (`Plug.inr`), and
  the links of the plugged net are the links of the parts (`Plug.link_inl`, `Plug.link_inr`);
* plugging respects isomorphisms up to wires (`WireIso.plug`), renaming the interface of the
  plugged net is the same as renaming the hole (`Net.plugReindex`), and two plugs into a
  context with two holes can be exchanged (`Net.plugExchange`);
* a context is determined, up to wires, by the net obtained by plugging an active pair into it
  (`Net.equiv_of_wireIso_plug_activePair`).
-/

@[expose] public section

namespace Net

variable {S : Signature}

/-! ### Reindexing twice -/

/-- Reindexing along `σ` and then along a left inverse of `σ` gives back the original net. -/
def reindexReindex {ι ι' : Type} (N : Net S ι) (σ : ι ≃ ι') (σ' : ι' ≃ ι)
    (h : ∀ i, σ' (σ i) = i) : Iso ((N.reindex σ).reindex σ') N where
  agent := .refl _
  wire := .refl _
  label_agent _ := rfl
  link_map p := by
    have h' (i : ι) : σ.symm (σ'.symm i) = i := by
      rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq, h]
    have hl (q : N.Port) : (N.reindexPort σ).symm (((N.reindex σ).reindexPort σ').symm q) = q := by
      rcases q with i | _ | _ | _
      · exact congrArg Port.free (h' i)
      all_goals rfl
    have hr (q : N.Port) : (N.reindex σ).reindexPort σ' (N.reindexPort σ q) = q := by
      rcases q with i | _ | _ | _
      · exact congrArg Port.free (h i)
      all_goals rfl
    simp only [Equiv.coe_refl, Port.map_id]
    change _ = (N.reindex σ).reindexPort σ' (N.reindexPort σ (N.link _))
    rw [hl, hr]

/-! ### Ports of a plugged net -/

namespace Plug

variable {ι κ : Type} (C : Net S (ι ⊕ κ)) (R : Net S κ)

/-- The net `R`, prepared for gluing. -/
abbrev hole : Net S (κ ⊕ Empty) := R.reindex (Equiv.sumEmpty κ Empty).symm

/-- Where a port of the context ends up in `C.plug R`. -/
def inl (q : C.Port) : (C.plug R).Port :=
  (C.glue (hole R)).reindexPort (Equiv.sumEmpty ι Empty) (Glue.inl C (hole R) q)

/-- Where a port of the plugged net ends up in `C.plug R`. -/
def inr (q : R.Port) : (C.plug R).Port :=
  (C.glue (hole R)).reindexPort (Equiv.sumEmpty ι Empty)
    (Glue.inr C (hole R) (R.reindexPort (Equiv.sumEmpty κ Empty).symm q))

theorem link_inl (q : C.Port) : (C.plug R).link (inl C R q) = inl C R (C.link q) := by
  unfold inl
  rw [reindex_link, glue_link_inl]

theorem link_inr (q : R.Port) : (C.plug R).link (inr C R q) = inr C R (R.link q) := by
  unfold inr
  rw [reindex_link, glue_link_inr, reindex_link]

theorem inl_free_inl (i : ι) : inl C R (.free (.inl i)) = .free i := rfl

theorem inl_free_inr (k : κ) : inl C R (.free (.inr k)) = inr C R (R.link (.free k)) := by
  unfold inl inr
  rw [Glue.inl_free_inr, ← reindex_link]
  rfl

theorem inr_free (k : κ) : inr C R (.free k) = inl C R (C.link (.free (.inr k))) := by
  unfold inl inr
  rw [← Glue.inr_free_inl]
  rfl

theorem link_free (i : ι) : (C.plug R).link (.free i) = inl C R (C.link (.free (.inl i))) := by
  rw [← inl_free_inl C R i, link_inl]

/-- Every port of a plugged net comes from the context or from the plugged net. -/
theorem cases (p : (C.plug R).Port) : (∃ q, p = inl C R q) ∨ ∃ q, p = inr C R q := by
  rcases p with i | (a | b) | ⟨a | b, k⟩ | ⟨w | w, s⟩
  · exact .inl ⟨.free (.inl i), rfl⟩
  · exact .inl ⟨.pri a, rfl⟩
  · exact .inr ⟨.pri b, rfl⟩
  · exact .inl ⟨.aux a k, rfl⟩
  · exact .inr ⟨.aux b k, rfl⟩
  · exact .inl ⟨.wire w s, rfl⟩
  · exact .inr ⟨.wire w s, rfl⟩

/-- To show that a map of ports out of a plugged net commutes with the links, it suffices to
check this on the ports of the two parts. -/
theorem link_ext {ι' : Type} {X : Net S ι'} (F : (C.plug R).Port → X.Port)
    (hl : ∀ q, X.link (F (inl C R q)) = F (inl C R (C.link q)))
    (hr : ∀ q, X.link (F (inr C R q)) = F (inr C R (R.link q)))
    (p : (C.plug R).Port) : X.link (F p) = F ((C.plug R).link p) := by
  rcases cases C R p with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · rw [hl, link_inl]
  · rw [hr, link_inr]

theorem step_inl {p q : C.Port} (h : C.Step p q) : (C.plug R).Step (inl C R p) (inl C R q) := by
  obtain ⟨w, s, rfl, rfl⟩ := h.eq
  rw [← link_inl]
  exact step_wire (N := C.plug R) (.inl w) s

theorem step_inr {p q : R.Port} (h : R.Step p q) : (C.plug R).Step (inr C R p) (inr C R q) := by
  obtain ⟨w, s, rfl, rfl⟩ := h.eq
  rw [← link_inr]
  exact step_wire (N := C.plug R) (.inr w) s

end Plug

/-! ### Plugging respects isomorphisms up to wires -/

section congr

variable {ι κ : Type} {C C' : Net S (ι ⊕ κ)} {R R' : Net S κ}

/-- Plugging respects isomorphisms up to wires. -/
def WireIso.plug (e : WireIso C C') (e' : WireIso R R') : WireIso (C.plug R) (C'.plug R') :=
  (e.glue (e'.reindex _)).reindex _

@[simp] theorem WireIso.plug_agent (e : WireIso C C') (e' : WireIso R R') :
    (e.plug e').agent = e.agent.sumCongr e'.agent :=
  rfl

end congr

/-! ### The identity context -/

/-- Plugging into the identity net gives back the plugged net, up to wires. -/
theorem idNet_plug {κ : Type} [Fintype κ] (R : Net S κ) : (idNet S κ).plug R ≈ R :=
  Setoid.trans (reindex_equiv _ (idNet_glue _))
    (reindexReindex R _ (Equiv.sumEmpty κ Empty) fun _ => rfl).equiv

/-! ### Plugging into a plugged net -/

/-- Plugging `X` into `C'` and the result into `C` is plugging `X` into the context
`C.glue C'`. -/
def plugPlug {ι κ κ' : Type} (C : Net S (ι ⊕ κ)) (C' : Net S (κ ⊕ κ')) (X : Net S κ') :
    Iso (C.plug (C'.plug X)) ((C.glue C').plug X) :=
  (((Iso.refl C).glue (reindexReindex (C'.glue (X.reindex (Equiv.sumEmpty κ' Empty).symm))
    (Equiv.sumEmpty κ Empty) (Equiv.sumEmpty κ Empty).symm (by
      rintro (_ | ⟨⟨⟩⟩)
      rfl))).trans (glueAssoc C C' _).symm).reindex _

/-! ### Reindexing the hole -/

section reindexHole

variable {ι κ κ' : Type} (C : Net S (ι ⊕ κ')) (R : Net S κ) (σ : κ ≃ κ')

/-- Renaming the hole of a context. -/
abbrev holeEquiv : ι ⊕ κ' ≃ ι ⊕ κ := Equiv.sumCongr (.refl ι) σ.symm

theorem Plug.inl_reindex_entity (q : C.Port) (hq : q.IsEntity) :
    inl C (R.reindex σ) q = inl (C.reindex (holeEquiv σ)) R (C.reindexPort (holeEquiv σ) q) := by
  rcases q with _ | _ | _ | _
  · exact absurd hq (Port.not_isEntity_free _)
  all_goals rfl

theorem Plug.inr_reindex_entity (q : (R.reindex σ).Port) (hq : q.IsEntity) :
    inr C (R.reindex σ) q = inr (C.reindex (holeEquiv σ)) R ((R.reindexPort σ).symm q) := by
  rcases q with _ | _ | _ | _
  · exact absurd hq (Port.not_isEntity_free _)
  all_goals rfl

theorem Plug.inl_reindex (q : C.Port) :
    inl C (R.reindex σ) q = inl (C.reindex (holeEquiv σ)) R (C.reindexPort (holeEquiv σ) q) := by
  rcases q with (i | k) | q
  · rfl
  · rw [inl_free_inr, inr_reindex_entity _ _ _ _ ((R.reindex σ).link_free k),
      (Equiv.symm_apply_eq _).mpr (reindex_link σ R _).symm, Equiv.symm_apply_apply]
    exact (inl_free_inr _ R (σ.symm k)).symm
  all_goals exact inl_reindex_entity C R σ _ trivial

theorem Plug.inr_reindex (q : (R.reindex σ).Port) :
    inr C (R.reindex σ) q = inr (C.reindex (holeEquiv σ)) R ((R.reindexPort σ).symm q) := by
  rcases q with k | q
  · rw [inr_free, inl_reindex_entity _ _ _ _ (C.link_free (.inr k)), ← reindex_link]
    exact (inr_free _ R (σ.symm k)).symm
  all_goals exact inr_reindex_entity C R σ _ trivial

/-- Renaming the interface of the plugged net is the same as renaming the hole of the
context. -/
def plugReindex : Iso (C.plug (R.reindex σ)) ((C.reindex (holeEquiv σ)).plug R) where
  agent := .refl _
  wire := .refl _
  label_agent _ := rfl
  link_map p := by
    simp only [Equiv.coe_refl, Port.map_id]
    refine Plug.link_ext C (R.reindex σ) (X := (C.reindex (holeEquiv σ)).plug R) (fun p => p)
      (fun q => ?_) (fun q => ?_) p
    · rw [Plug.inl_reindex, Plug.inl_reindex, Plug.link_inl, reindex_link]
    · rw [Plug.inr_reindex, Plug.inr_reindex, Plug.link_inr]
      congr 1
      change _ = (R.reindexPort σ).symm (R.reindexPort σ (R.link ((R.reindexPort σ).symm q)))
      rw [Equiv.symm_apply_apply]

end reindexHole

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

theorem sumRightComm_sumRightComm {α β γ : Type} (x : (α ⊕ β) ⊕ γ) :
    sumRightComm α γ β (sumRightComm α β γ x) = x := by
  rcases x with (_ | _) | _ <;> rfl

variable {ι κ₁ κ₂ : Type} (D : Net S ((ι ⊕ κ₁) ⊕ κ₂)) (X : Net S κ₂) (Y : Net S κ₁)

/-- The context `D` with its two holes exchanged. -/
abbrev exchange : Net S ((ι ⊕ κ₂) ⊕ κ₁) := D.reindex (sumRightComm ι κ₁ κ₂)

theorem plugExchange_label_agent (a : ((D.plug X).plug Y).Agent) :
    ((D.exchange.plug Y).plug X).label (sumRightComm _ _ _ a) = ((D.plug X).plug Y).label a := by
  rcases a with (_ | _) | _ <;> rfl

/-- The map of ports underlying `plugExchange`. -/
abbrev plugExchangePort : ((D.plug X).plug Y).Port → ((D.exchange.plug Y).plug X).Port :=
  Port.map (sumRightComm _ _ _) (plugExchange_label_agent D X Y) (sumRightComm _ _ _) id

open Plug

theorem plugExchangePort_D_entity (d : D.Port) (hd : d.IsEntity) :
    plugExchangePort D X Y (inl _ Y (inl D X d)) =
      inl _ X (inl D.exchange Y (D.reindexPort (sumRightComm ι κ₁ κ₂) d)) := by
  rcases d with _ | _ | _ | _
  · exact absurd hd (Port.not_isEntity_free _)
  all_goals rfl

theorem plugExchangePort_X_entity (x : X.Port) (hx : x.IsEntity) :
    plugExchangePort D X Y (inl _ Y (inr D X x)) = inr _ X x := by
  rcases x with _ | _ | _ | _
  · exact absurd hx (Port.not_isEntity_free _)
  all_goals rfl

theorem plugExchangePort_Y_entity (y : Y.Port) (hy : y.IsEntity) :
    plugExchangePort D X Y (inr _ Y y) = inl _ X (inr D.exchange Y y) := by
  rcases y with _ | _ | _ | _
  · exact absurd hy (Port.not_isEntity_free _)
  all_goals rfl

theorem plugExchangePort_D (d : D.Port) :
    plugExchangePort D X Y (inl _ Y (inl D X d)) =
      inl _ X (inl D.exchange Y (D.reindexPort (sumRightComm ι κ₁ κ₂) d)) := by
  rcases d with ((i | k) | k) | d
  · rfl
  · rw [show inl D X (.free (.inl (.inr k))) = .free (.inr k) from rfl, inl_free_inr,
      plugExchangePort_Y_entity _ _ _ _ (Y.link_free k)]
    exact congrArg (inl _ X) (inl_free_inr D.exchange Y k).symm
  · rw [inl_free_inr, plugExchangePort_X_entity _ _ _ _ (X.link_free k)]
    exact (inl_free_inr _ X k).symm
  all_goals exact plugExchangePort_D_entity D X Y _ trivial

theorem plugExchangePort_X (x : X.Port) :
    plugExchangePort D X Y (inl _ Y (inr D X x)) = inr _ X x := by
  rcases x with k | x
  · rw [inr_free, plugExchangePort_D_entity _ _ _ _ (D.link_free (.inr k)), inr_free,
      Plug.link_free, ← reindex_link]
    rfl
  all_goals exact plugExchangePort_X_entity D X Y _ trivial

theorem plugExchangePort_Y (y : Y.Port) :
    plugExchangePort D X Y (inr _ Y y) = inl _ X (inr D.exchange Y y) := by
  rcases y with k | y
  · rw [inr_free, Plug.link_free, plugExchangePort_D_entity _ _ _ _ (D.link_free _), inr_free,
      ← reindex_link]
    rfl
  all_goals exact plugExchangePort_Y_entity D X Y _ trivial

/-- Plugging into the two holes of a context can be done in either order. -/
def plugExchange : Iso ((D.plug X).plug Y) ((D.exchange.plug Y).plug X) where
  agent := sumRightComm _ _ _
  wire := sumRightComm _ _ _
  label_agent := plugExchange_label_agent D X Y
  link_map := Plug.link_ext (D.plug X) Y (plugExchangePort D X Y)
    (Plug.link_ext D X (fun q => plugExchangePort D X Y (inl _ Y q))
      (fun d => by
        rw [plugExchangePort_D, plugExchangePort_D, Plug.link_inl, Plug.link_inl, reindex_link])
      (fun x => by rw [plugExchangePort_X, plugExchangePort_X, Plug.link_inr]))
    (fun y => by rw [plugExchangePort_Y, plugExchangePort_Y, Plug.link_inl, Plug.link_inr])

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
    (C.plug (activePair α β)).Partner (holeTPort C x) (holeTPort C y) := by
  have := reflTransGen_map _ (fun _ _ => Plug.step_inl C (activePair α β)) h
  rw [← Plug.link_inl, ← tport_holeTPort, ← tport_holeTPort] at this
  exact this

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

/-- If plugging the active pair `α ⋈ β` into two contexts gives nets that are isomorphic up to
wires, by an isomorphism that maps the active pair to the active pair, then the contexts are
isomorphic up to wires. -/
def WireIso.ofPlugActivePair (f : WireIso (C.plug (activePair α β)) (C'.plug (activePair α β)))
    (h : ∀ t, f.agent (.inr t) = .inr t) : WireIso C C' :=
  have hlabel (c : C.Agent) : C'.label (restrictInl f.agent h c) = C.label c := by
    have := f.label_agent (.inl c)
    rw [← inl_restrictInl _ h] at this
    exact this
  .ofPartner (restrictInl f.agent h) hlabel fun x y hxy => by
      have hp (z : C.TPort) : f.port (holeTPort C z) =
          holeTPort C' (z.map (restrictInl f.agent h) hlabel id id) := by
        rcases z with (i | k | k) | c | ⟨c, k⟩ | ⟨⟨⟩, _⟩
        · rfl
        · exact Port.aux_congr (h .left) rfl
        · exact Port.aux_congr (h .right) rfl
        · exact congrArg Port.pri (inl_restrictInl _ h c).symm
        · exact Port.aux_congr (inl_restrictInl _ h c).symm rfl
      rw [← partner_holeTPort_iff, ← hp, ← hp]
      exact f.partner_port (partner_holeTPort_iff.mpr hxy)

end unique

end Net

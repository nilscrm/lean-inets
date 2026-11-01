module

public import LeanInets.WireIso

/-!
# The identity net is a unit for gluing

The identity net `idNet S κ` consists of one wire for each `k : κ`, connecting the free
ports `inl k` and `inr k`. Gluing it onto a net puts a wire in front of each glued port, so
it is a unit for gluing up to wires, i.e. up to `≈`, but not up to isomorphism.
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

section idNet

variable {κ : Type} [Fintype κ]

theorem idNet_partner_inl (k : κ) : (idNet S κ).Partner (.free (.inl k)) (.free (.inr k)) :=
  .single (step_wire (N := idNet S κ) k .l)

theorem idNet_partner_inr (k : κ) : (idNet S κ).Partner (.free (.inr k)) (.free (.inl k)) :=
  (idNet_partner_inl k).symm

theorem idNet_partner_inl_eq {k : κ} {y : (idNet S κ).TPort}
    (h : (idNet S κ).Partner (.free (.inl k)) y) : y = .free (.inr k) :=
  h.unique (idNet_partner_inl k)

theorem idNet_partner_inr_eq {k : κ} {y : (idNet S κ).TPort}
    (h : (idNet S κ).Partner (.free (.inr k)) y) : y = .free (.inl k) :=
  h.unique (idNet_partner_inr k)

end idNet

/-! ### Terminal ports that are not glued -/

namespace Glue

variable {ι κ ι' : Type} {N : Net S (ι ⊕ κ)} {M : Net S (κ ⊕ ι')}

theorem liftLT_ne_free_inr (b : _root_.Port N.label Empty ι) (k : κ) :
    liftLT N b ≠ .free (.inr k) := by
  rcases b with _ | _ | _ | ⟨⟨⟩, _⟩ <;> nofun

theorem liftRT_ne_free_inl (b : _root_.Port M.label Empty ι') (k : κ) :
    liftRT M b ≠ .free (.inl k) := by
  rcases b with _ | _ | _ | ⟨⟨⟩, _⟩ <;> nofun

theorem liftLT_eq_free_inl {b : _root_.Port N.label Empty ι} {i : ι}
    (h : liftLT N b = .free (.inl i)) : b = .free i := by
  rcases b with _ | _ | _ | ⟨⟨⟩, _⟩ <;> simp_all [liftLT]

theorem liftRT_eq_free_inr {b : _root_.Port M.label Empty ι'} {j : ι'}
    (h : liftRT M b = .free (.inr j)) : b = .free j := by
  rcases b with _ | _ | _ | ⟨⟨⟩, _⟩ <;> simp_all [liftRT]

end Glue

open Glue

variable {κ ι : Type} [Fintype κ]

/-! ### Left unit -/

section left

variable (N : Net S (κ ⊕ ι))

theorem idNetGlue_label_agent (a : ((idNet S κ).glue N).Agent) :
    N.label ((Equiv.emptySum Empty N.Agent : (idNet S κ).Agent ⊕ N.Agent ≃ N.Agent) a) =
      ((idNet S κ).glue N).label a := by
  rcases a with a | a
  exacts [(a : Empty).elim, rfl]

/-- The map of terminal ports underlying `idNetGlue`. -/
abbrev idNetGlueTPort : ((idNet S κ).glue N).TPort → N.TPort :=
  Port.map (Equiv.emptySum Empty N.Agent : (idNet S κ).Agent ⊕ N.Agent ≃ N.Agent)
    (idNetGlue_label_agent N) id id

theorem idNetGlueTPort_embLT (k : κ) :
    idNetGlueTPort N (embLT (idNet S κ) N (.free k)) = .free (.inl k) := rfl

theorem idNetGlueTPort_embRT (b : _root_.Port N.label Empty ι) :
    idNetGlueTPort N (embRT (idNet S κ) N b) = liftRT N b := by
  rcases b with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl

/-- Gluing the identity net on the left changes a net only up to wires. -/
def idNetGlue : WireIso ((idNet S κ).glue N) N :=
  .ofPartner (Equiv.emptySum Empty N.Agent : (idNet S κ).Agent ⊕ N.Agent ≃ N.Agent)
    (idNetGlue_label_agent N) fun x y h => by
      change N.Partner (idNetGlueTPort N x) (idNetGlueTPort N y)
      rcases cases_tport (idNet S κ) N x with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · rcases b with k | a | ⟨a, _⟩ | ⟨⟨⟩, _⟩
        rotate_left
        · exact (a : Empty).elim
        · exact (a : Empty).elim
        rw [idNetGlueTPort_embLT]
        cases GlueChain.of_partner_embLT h with
        | stopL hc => exact absurd (idNet_partner_inl_eq hc) (liftLT_ne_free_inr _ _)
        | crossL hc c =>
          cases idNet_partner_inl_eq hc
          cases c with
          | stopR hc => rwa [idNetGlueTPort_embRT]
          | crossR hc c =>
            cases c with
            | stopL hc' =>
              obtain rfl := liftLT_eq_free_inl (idNet_partner_inr_eq hc')
              exact hc
            | crossL hc' _ => exact absurd (idNet_partner_inr_eq hc') nofun
      · rw [idNetGlueTPort_embRT]
        cases GlueChain.of_partner_embRT h with
        | stopR hc => rwa [idNetGlueTPort_embRT]
        | crossR hc c =>
          cases c with
          | stopL hc' =>
            obtain rfl := liftLT_eq_free_inl (idNet_partner_inr_eq hc')
            exact hc
          | crossL hc' _ => exact absurd (idNet_partner_inr_eq hc') nofun

/-- The identity net is a left unit for gluing, up to `≈`. -/
theorem idNet_glue : (idNet S κ).glue N ≈ N := (idNetGlue N).equiv

end left

/-! ### Right unit -/

section right

variable (N : Net S (ι ⊕ κ))

theorem glueIdNet_label_agent (a : (N.glue (idNet S κ)).Agent) :
    N.label ((Equiv.sumEmpty N.Agent Empty : N.Agent ⊕ (idNet S κ).Agent ≃ N.Agent) a) =
      (N.glue (idNet S κ)).label a := by
  rcases a with a | a
  exacts [rfl, (a : Empty).elim]

/-- The map of terminal ports underlying `glueIdNet`. -/
abbrev glueIdNetTPort : (N.glue (idNet S κ)).TPort → N.TPort :=
  Port.map (Equiv.sumEmpty N.Agent Empty : N.Agent ⊕ (idNet S κ).Agent ≃ N.Agent)
    (glueIdNet_label_agent N) id id

theorem glueIdNetTPort_embLT (b : _root_.Port N.label Empty ι) :
    glueIdNetTPort N (embLT N (idNet S κ) b) = liftLT N b := by
  rcases b with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl

theorem glueIdNetTPort_embRT (k : κ) :
    glueIdNetTPort N (embRT N (idNet S κ) (.free k)) = .free (.inr k) := rfl

/-- Gluing the identity net on the right changes a net only up to wires. -/
def glueIdNet : WireIso (N.glue (idNet S κ)) N :=
  .ofPartner (Equiv.sumEmpty N.Agent Empty : N.Agent ⊕ (idNet S κ).Agent ≃ N.Agent)
    (glueIdNet_label_agent N) fun x y h => by
      change N.Partner (glueIdNetTPort N x) (glueIdNetTPort N y)
      rcases cases_tport N (idNet S κ) x with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · rw [glueIdNetTPort_embLT]
        cases GlueChain.of_partner_embLT h with
        | stopL hc => rwa [glueIdNetTPort_embLT]
        | crossL hc c =>
          cases c with
          | stopR hc' =>
            obtain rfl := liftRT_eq_free_inr (idNet_partner_inl_eq hc')
            exact hc
          | crossR hc' _ => exact absurd (idNet_partner_inl_eq hc') nofun
      · rcases b with k | a | ⟨a, _⟩ | ⟨⟨⟩, _⟩
        rotate_left
        · exact (a : Empty).elim
        · exact (a : Empty).elim
        rw [glueIdNetTPort_embRT]
        cases GlueChain.of_partner_embRT h with
        | stopR hc => exact absurd (idNet_partner_inr_eq hc) (liftRT_ne_free_inl _ _)
        | crossR hc c =>
          cases idNet_partner_inr_eq hc
          cases c with
          | stopL hc => rwa [glueIdNetTPort_embLT]
          | crossL hc c =>
            cases c with
            | stopR hc' =>
              obtain rfl := liftRT_eq_free_inr (idNet_partner_inl_eq hc')
              exact hc
            | crossR hc' _ => exact absurd (idNet_partner_inl_eq hc') nofun

/-- The identity net is a right unit for gluing, up to `≈`. -/
theorem glue_idNet : N.glue (idNet S κ) ≈ N := (glueIdNet N).equiv

end right

end Net

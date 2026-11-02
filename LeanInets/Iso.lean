module

public import LeanInets.Net

/-!
# Isomorphism of nets and reindexing

An isomorphism between nets `N` and `M` consists of bijections between their agents, their
wires and their interfaces that preserve labels and links. Since the interface map is part of
the data, nets with different interfaces can be isomorphic: this lets the structural laws of
union and trace be stated without reindexing every net by hand.

Isomorphism is strict about wires: `a — w — b` is not isomorphic to `a — b`, and a wire may
not be flipped. Both are identified by the coarser isomorphism up to wires (`WireIso`).

`N.reindex σ` renames the free ports of `N` along `σ : ι ≃ ι'`; it is isomorphic to `N` by an
isomorphism with interface map `σ` (`Net.reindexIso`).
-/

@[expose] public section

namespace Net

variable {S : Signature} {ι ι' ι'' : Type}

/-- An isomorphism between the nets `N` and `M`. -/
structure Iso (N : Net S ι) (M : Net S ι') where
  /-- The bijection on agents. -/
  agent : N.Agent ≃ M.Agent
  /-- The bijection on wires. -/
  wire : N.Wire ≃ M.Wire
  /-- The bijection on interfaces. -/
  iface : ι ≃ ι'
  label_agent : ∀ a, M.label (agent a) = N.label a
  link_map : ∀ p, M.link (Port.map agent label_agent wire iface p) =
    Port.map agent label_agent wire iface (N.link p)

namespace Iso

variable {N : Net S ι} {M : Net S ι'} {K : Net S ι''}

/-- The bijection on ports induced by an isomorphism. -/
def port (e : Iso N M) : N.Port ≃ M.Port :=
  Port.mapEquiv e.agent e.label_agent e.wire e.iface

variable (e : Iso N M)

@[simp] theorem port_free (i : ι) : e.port (.free i) = .free (e.iface i) := rfl
@[simp] theorem port_pri (a : N.Agent) : e.port (.pri a) = .pri (e.agent a) := rfl
@[simp] theorem port_aux (a : N.Agent) (k) :
    e.port (.aux a k) = .aux (e.agent a) (k.cast (congrArg S.arity (e.label_agent a).symm)) :=
  rfl
@[simp] theorem port_wire (w : N.Wire) (s : Side) :
    e.port (.wire w s) = .wire (e.wire w) s := rfl

theorem link_port (p : N.Port) : M.link (e.port p) = e.port (N.link p) := e.link_map p

/-- The identity isomorphism. -/
@[refl] protected def refl (N : Net S ι) : Iso N N where
  agent := .refl _
  wire := .refl _
  iface := .refl _
  label_agent _ := rfl
  link_map p := by simp only [Equiv.coe_refl, Port.map_id]

/-- The inverse of an isomorphism. -/
@[symm] protected def symm : Iso M N where
  agent := e.agent.symm
  wire := e.wire.symm
  iface := e.iface.symm
  label_agent a := by rw [← e.label_agent, e.agent.apply_symm_apply]
  link_map p := by
    change N.link (e.port.symm p) = e.port.symm (M.link p)
    rw [Equiv.eq_symm_apply, ← link_port, Equiv.apply_symm_apply]

/-- The composition of isomorphisms. -/
@[trans] protected def trans (e' : Iso M K) : Iso N K where
  agent := e.agent.trans e'.agent
  wire := e.wire.trans e'.wire
  iface := e.iface.trans e'.iface
  label_agent a := (e'.label_agent _).trans (e.label_agent a)
  link_map p := by
    have h (q : N.Port) : Port.map (e.agent.trans e'.agent)
        (fun a => (e'.label_agent _).trans (e.label_agent a)) (e.wire.trans e'.wire)
        (e.iface.trans e'.iface) q = e'.port (e.port q) := by
      cases q <;> rfl
    rw [h, h, link_port, link_port]

@[simp] theorem symm_port (p : M.Port) : e.symm.port p = e.port.symm p := rfl

@[simp] theorem trans_port (e' : Iso M K) (p : N.Port) :
    (e.trans e').port p = e'.port (e.port p) := by
  cases p <;> rfl

/-- Isomorphisms preserve and reflect active pairs. -/
theorem isActivePair_iff {a b : N.Agent} :
    M.IsActivePair (e.agent a) (e.agent b) ↔ N.IsActivePair a b := by
  unfold IsActivePair
  rw [← port_pri, ← port_pri, link_port, e.port.injective.eq_iff]

end Iso

/-! ### Reindexing the interface -/

section reindex

/-- The ports of `N`, with the interface renamed along `σ`. -/
def reindexPort (σ : ι ≃ ι') (N : Net S ι) : N.Port ≃ _root_.Port N.label N.Wire ι' :=
  Port.mapEquiv (.refl _) (fun _ => rfl) (.refl _) σ

/-- Rename the free ports of a net along a bijection of interfaces.

This is reducible (as are `union` and `trace`) so that the ports of the result unfold to a plain
`Port` type, which `rw` needs in order to see that lemmas about the underlying ports apply. -/
@[reducible] def reindex (σ : ι ≃ ι') (N : Net S ι) : Net S ι' where
  Agent := N.Agent
  Wire := N.Wire
  label := N.label
  link p := N.reindexPort σ (N.link ((N.reindexPort σ).symm p))
  link_link p := by simp [N.link_link]
  link_ne p h := N.link_ne _ ((Equiv.eq_symm_apply _).mpr h)
  link_free i := (Port.isEntity_map _ (fun _ => rfl) _ _ _).mpr (N.link_free (σ.symm i))

variable (σ : ι ≃ ι') (N : Net S ι)

theorem reindex_link (p : N.Port) :
    (N.reindex σ).link (N.reindexPort σ p) = N.reindexPort σ (N.link p) := by
  change N.reindexPort σ (N.link ((N.reindexPort σ).symm (N.reindexPort σ p))) = _
  rw [Equiv.symm_apply_apply]

/-- A net is isomorphic to its reindexing. -/
def reindexIso : Iso N (N.reindex σ) where
  agent := .refl _
  wire := .refl _
  iface := σ
  label_agent _ := rfl
  link_map := reindex_link σ N

/-- Swap the two halves of an interface. -/
abbrev swap {α β : Type} (N : Net S (α ⊕ β)) : Net S (β ⊕ α) :=
  N.reindex (Equiv.sumComm _ _)

/-- Swapping the interface twice gives back the original net. Its interface map is the identity
(`swapSwap_iface`). -/
def swapSwap {α β : Type} (N : Net S (α ⊕ β)) : Iso N.swap.swap N :=
  ((reindexIso _ N).trans (reindexIso _ _)).symm

theorem swapSwap_iface {α β : Type} (N : Net S (α ⊕ β)) (i : α ⊕ β) :
    (swapSwap N).iface i = i := by
  rcases i with _ | _ <;> rfl

end reindex

end Net

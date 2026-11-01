module

public import LeanInets.Net

/-!
# Isomorphism of nets

Two nets with the same interface are isomorphic if there are bijections between their
agents and between their wires that preserve labels and links and fix the interface.

Isomorphism is strict about wires: `a — w — b` is not isomorphic to `a — b`, and a wire may
not be flipped. Both are identified by the coarser isomorphism up to wires (`WireIso`).
-/

@[expose] public section

namespace Net

variable {S : Signature} {ι : Type}

/-- An isomorphism between nets `N` and `M` with the same interface. -/
structure Iso (N M : Net S ι) where
  /-- The bijection on agents. -/
  agent : N.Agent ≃ M.Agent
  /-- The bijection on wires. -/
  wire : N.Wire ≃ M.Wire
  label_agent : ∀ a, M.label (agent a) = N.label a
  link_map : ∀ p, M.link (Port.map agent label_agent wire id p) =
    Port.map agent label_agent wire id (N.link p)

namespace Iso

variable {N M K : Net S ι}

/-- The bijection on ports induced by an isomorphism. It is the identity on free ports. -/
def port (e : Iso N M) : N.Port ≃ M.Port :=
  Port.mapEquiv e.agent e.label_agent e.wire (.refl ι)

variable (e : Iso N M)

@[simp] theorem port_free (i : ι) : e.port (.free i) = .free i := rfl
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
  label_agent _ := rfl
  link_map p := by simp only [Equiv.coe_refl, Port.map_id]

/-- The inverse of an isomorphism. -/
@[symm] protected def symm : Iso M N where
  agent := e.agent.symm
  wire := e.wire.symm
  label_agent a := by rw [← e.label_agent, e.agent.apply_symm_apply]
  link_map p := by
    change N.link (e.port.symm p) = e.port.symm (M.link p)
    rw [Equiv.eq_symm_apply, ← link_port, Equiv.apply_symm_apply]

/-- The composition of isomorphisms. -/
@[trans] protected def trans (e' : Iso M K) : Iso N K where
  agent := e.agent.trans e'.agent
  wire := e.wire.trans e'.wire
  label_agent a := (e'.label_agent _).trans (e.label_agent a)
  link_map p := by
    have h (q : N.Port) : Port.map (e.agent.trans e'.agent)
        (fun a => (e'.label_agent _).trans (e.label_agent a)) (e.wire.trans e'.wire) id q =
        e'.port (e.port q) := by
      cases q <;> rfl
    rw [h, h, link_port, link_port]

@[simp] theorem symm_port (p : M.Port) : e.symm.port p = e.port.symm p := rfl

@[simp] theorem trans_port (e' : Iso M K) (p : N.Port) :
    (e.trans e').port p = e'.port (e.port p) := by
  cases p <;> rfl

/-! ### Invariance -/

/-- Isomorphisms preserve and reflect active pairs. -/
theorem isActivePair_iff {a b : N.Agent} :
    M.IsActivePair (e.agent a) (e.agent b) ↔ N.IsActivePair a b := by
  unfold IsActivePair
  rw [← port_pri, ← port_pri, link_port, e.port.injective.eq_iff]

/-- Isomorphisms preserve and reflect normal forms. -/
theorem isNormal_iff (e : Iso N M) : M.IsNormal ↔ N.IsNormal := by
  refine ⟨fun h a b hab => h _ _ (e.isActivePair_iff.mpr hab), fun h a b hab => ?_⟩
  rw [← e.agent.apply_symm_apply a, ← e.agent.apply_symm_apply b, isActivePair_iff] at hab
  exact h _ _ hab

end Iso

/-- Two nets are isomorphic if there is an isomorphism between them. -/
def Isomorphic (N M : Net S ι) : Prop := Nonempty (Iso N M)

namespace Isomorphic

variable {N M K : Net S ι}

@[refl] theorem refl (N : Net S ι) : Isomorphic N N := ⟨.refl N⟩

@[symm] theorem symm : Isomorphic N M → Isomorphic M N
  | ⟨e⟩ => ⟨e.symm⟩

@[trans] theorem trans : Isomorphic N M → Isomorphic M K → Isomorphic N K
  | ⟨e⟩, ⟨e'⟩ => ⟨e.trans e'⟩

theorem equivalence : Equivalence (@Isomorphic S ι) := ⟨refl, symm, trans⟩

end Isomorphic

/-- Nets up to isomorphism. This is deliberately not an instance: `≈` on nets is reserved
for the coarser isomorphism up to wires. -/
def isoSetoid (S : Signature) (ι : Type) : Setoid (Net S ι) :=
  ⟨Isomorphic, Isomorphic.equivalence⟩

end Net

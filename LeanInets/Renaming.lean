module

public import LeanInets.Net

/-!
# Renamings

A renaming between nets `N` and `M` consists of bijections between their agents and between
their interfaces that preserve labels. It is the part shared by isomorphisms (`Net.Iso`, which
also map wires and preserve links) and isomorphisms up to wires (`Net.WireIso`, which preserve
partners). Given a bijection of wires, a renaming acts on ports (`Renaming.port`).
-/

/-- `sum_rfl x` proves an equation by `rfl`, after case analysis on the nested sum `x` where
needed. -/
syntax "sum_rfl " ident : tactic

macro_rules
  | `(tactic| sum_rfl $x) =>
    `(tactic| first | rfl | (cases $x:ident with | inl y => sum_rfl y | inr y => sum_rfl y))

/-- Proves `∀ x, f x = g x` for maps out of nested sums that agree on each summand by computation.
It is the default proof of the conditions on interface maps of isomorphisms. -/
macro "iface_rfl" : tactic => `(tactic| (intro x; sum_rfl x))

@[expose] public section

namespace Net

variable {S : Signature} {ι ι' ι'' : Type}

/-- A renaming between the nets `N` and `M`: label-preserving bijections of agents and of
interfaces. -/
structure Renaming (N : Net S ι) (M : Net S ι') where
  /-- The bijection on agents. -/
  agent : N.Agent ≃ M.Agent
  /-- The bijection on interfaces. -/
  iface : ι ≃ ι'
  label_agent : ∀ a, M.label (agent a) = N.label a

namespace Renaming

variable {N : Net S ι} {M : Net S ι'} {K : Net S ι''}

/-- The identity renaming. -/
@[refl] protected def refl (N : Net S ι) : Renaming N N where
  agent := .refl _
  iface := .refl _
  label_agent _ := rfl

/-- The inverse of a renaming. -/
@[symm] protected def symm (e : Renaming N M) : Renaming M N where
  agent := e.agent.symm
  iface := e.iface.symm
  label_agent a := by rw [← e.label_agent, e.agent.apply_symm_apply]

/-- The composition of renamings. -/
@[trans] protected def trans (e : Renaming N M) (e' : Renaming M K) : Renaming N K where
  agent := e.agent.trans e'.agent
  iface := e.iface.trans e'.iface
  label_agent a := (e'.label_agent _).trans (e.label_agent a)

variable (e : Renaming N M) {W W' W'' : Type}

/-- The bijection on ports induced by a renaming and a bijection of wires. -/
def port (g : W ≃ W') : _root_.Port N.label W ι ≃ _root_.Port M.label W' ι' :=
  Port.mapEquiv e.agent e.label_agent g e.iface

variable (g : W ≃ W')

@[simp] theorem port_free (i : ι) : e.port g (.free i) = .free (e.iface i) := rfl
@[simp] theorem port_pri (a : N.Agent) : e.port g (.pri a) = .pri (e.agent a) := rfl
@[simp] theorem port_aux (a : N.Agent) (k) :
    e.port g (.aux a k) = .aux (e.agent a) (k.cast (congrArg S.arity (e.label_agent a).symm)) :=
  rfl
@[simp] theorem port_wire (w : W) (s : Side) : e.port g (.wire w s) = .wire (g w) s := rfl

theorem refl_port (p : _root_.Port N.label W ι) : (Renaming.refl N).port (.refl W) p = p := by
  cases p <;> rfl

theorem trans_port (e' : Renaming M K) (g' : W' ≃ W'') (p : _root_.Port N.label W ι) :
    (e.trans e').port (g.trans g') p = e'.port g' (e.port g p) := by
  cases p <;> rfl

end Renaming

end Net

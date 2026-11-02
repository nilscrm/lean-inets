module

public import LeanInets.Iso

/-!
# Disjoint union of nets

`N.union M` puts the nets `N` and `M` side by side: its agents, wires and interface are the
disjoint unions of those of `N` and `M`, and no link crosses between the two parts.

Union respects isomorphism (`Iso.union`), and is commutative (`unionComm`) and associative
(`unionAssoc`) up to isomorphism. Together with `trace` (and `reindex`), it is the only way of
building nets out of nets; plugging and gluing are derived from the two.
-/

@[expose] public section

namespace Net

variable {S : Signature}

section union

variable {ι ι' : Type} (N : Net S ι) (M : Net S ι')

/-- The ports of the union of `N` and `M`. -/
abbrev UnionPort := _root_.Port (Sum.elim N.label M.label) (N.Wire ⊕ M.Wire) (ι ⊕ ι')

namespace Union

/-- The ports of `N` as ports of the union. -/
def inl : N.Port → UnionPort N M := Port.map Sum.inl (fun _ => rfl) Sum.inl Sum.inl

/-- The ports of `M` as ports of the union. -/
def inr : M.Port → UnionPort N M := Port.map Sum.inr (fun _ => rfl) Sum.inr Sum.inr

/-- The links of the union. -/
def link : UnionPort N M → UnionPort N M
  | .free (.inl i) => inl N M (N.link (.free i))
  | .free (.inr j) => inr N M (M.link (.free j))
  | .pri (.inl a) => inl N M (N.link (.pri a))
  | .pri (.inr b) => inr N M (M.link (.pri b))
  | .aux (.inl a) k => inl N M (N.link (.aux a k))
  | .aux (.inr b) k => inr N M (M.link (.aux b k))
  | .wire (.inl w) s => inl N M (N.link (.wire w s))
  | .wire (.inr w) s => inr N M (M.link (.wire w s))

theorem link_inl (q : N.Port) : link N M (inl N M q) = inl N M (N.link q) := by
  cases q <;> rfl

theorem link_inr (q : M.Port) : link N M (inr N M q) = inr N M (M.link q) := by
  cases q <;> rfl

theorem inl_injective : Function.Injective (inl N M) :=
  Port.map_injective _ _ _ _ Sum.inl_injective Sum.inl_injective Sum.inl_injective

theorem inr_injective : Function.Injective (inr N M) :=
  Port.map_injective _ _ _ _ Sum.inr_injective Sum.inr_injective Sum.inr_injective

/-- Every port of the union comes from `N` or from `M`. -/
theorem cases (p : UnionPort N M) : (∃ q, p = inl N M q) ∨ ∃ q, p = inr N M q := by
  rcases p with (i | j) | (a | b) | ⟨a | b, k⟩ | ⟨w | w, s⟩
  · exact .inl ⟨.free i, rfl⟩
  · exact .inr ⟨.free j, rfl⟩
  · exact .inl ⟨.pri a, rfl⟩
  · exact .inr ⟨.pri b, rfl⟩
  · exact .inl ⟨.aux a k, rfl⟩
  · exact .inr ⟨.aux b k, rfl⟩
  · exact .inl ⟨.wire w s, rfl⟩
  · exact .inr ⟨.wire w s, rfl⟩

end Union

/-- The disjoint union of `N` and `M`. -/
@[reducible] def union : Net S (ι ⊕ ι') where
  Agent := N.Agent ⊕ M.Agent
  Wire := N.Wire ⊕ M.Wire
  label := Sum.elim N.label M.label
  link := Union.link N M
  link_link p := by
    rcases Union.cases N M p with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · rw [Union.link_inl, Union.link_inl, N.link_link]
    · rw [Union.link_inr, Union.link_inr, M.link_link]
  link_ne p := by
    rcases Union.cases N M p with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · rw [Union.link_inl]
      exact (Union.inl_injective N M).ne (N.link_ne q)
    · rw [Union.link_inr]
      exact (Union.inr_injective N M).ne (M.link_ne q)
  link_free
    | .inl i => (Port.isEntity_map (label' := Sum.elim N.label M.label) Sum.inl (fun _ => rfl)
        Sum.inl Sum.inl _).mpr (N.link_free i)
    | .inr j => (Port.isEntity_map (label' := Sum.elim N.label M.label) Sum.inr (fun _ => rfl)
        Sum.inr Sum.inr _).mpr (M.link_free j)

theorem union_link_inl (q : N.Port) :
    (N.union M).link (Union.inl N M q) = Union.inl N M (N.link q) :=
  Union.link_inl N M q

theorem union_link_inr (q : M.Port) :
    (N.union M).link (Union.inr N M q) = Union.inr N M (M.link q) :=
  Union.link_inr N M q

/-- To show that a map of ports out of a union commutes with the links, it suffices to check
this on the ports of the two parts. -/
theorem union_link_ext {ι'' : Type} {X : Net S ι''} (F : (N.union M).Port → X.Port)
    (hl : ∀ q, X.link (F (Union.inl N M q)) = F (Union.inl N M (N.link q)))
    (hr : ∀ q, X.link (F (Union.inr N M q)) = F (Union.inr N M (M.link q)))
    (p : (N.union M).Port) : X.link (F p) = F ((N.union M).link p) := by
  rcases Union.cases N M p with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · rw [hl, union_link_inl]
  · rw [hr, union_link_inr]

end union

/-! ### Union respects isomorphism -/

section congr

variable {ι ι' κ κ' : Type} {N : Net S ι} {N' : Net S ι'} {M : Net S κ} {M' : Net S κ'}
  (e : Iso N N') (f : Iso M M')

theorem Iso.union_label_agent (a : (N.union M).Agent) :
    (N'.union M').label (e.agent.sumCongr f.agent a) = (N.union M).label a := by
  rcases a with a | b
  exacts [e.label_agent a, f.label_agent b]

/-- Union respects isomorphism. -/
def Iso.union : Iso (N.union M) (N'.union M') where
  agent := e.agent.sumCongr f.agent
  wire := e.wire.sumCongr f.wire
  iface := e.iface.sumCongr f.iface
  label_agent := e.union_label_agent f
  link_map := by
    have hl (q : N.Port) : Port.map (e.agent.sumCongr f.agent) (e.union_label_agent f)
        (e.wire.sumCongr f.wire) (e.iface.sumCongr f.iface) (Union.inl N M q) =
        Union.inl N' M' (e.port q) := by
      cases q <;> rfl
    have hr (q : M.Port) : Port.map (e.agent.sumCongr f.agent) (e.union_label_agent f)
        (e.wire.sumCongr f.wire) (e.iface.sumCongr f.iface) (Union.inr N M q) =
        Union.inr N' M' (f.port q) := by
      cases q <;> rfl
    exact union_link_ext N M _ (fun q => by rw [hl, hl, union_link_inl, e.link_port])
      (fun q => by rw [hr, hr, union_link_inr, f.link_port])

end congr

/-! ### Commutativity and associativity -/

section laws

variable {ι ι' ι'' : Type} (N : Net S ι) (M : Net S ι') (K : Net S ι'')

theorem unionComm_label_agent (a : (N.union M).Agent) :
    (M.union N).label (Equiv.sumComm _ _ a) = (N.union M).label a := by
  rcases a with _ | _ <;> rfl

/-- Union is commutative up to isomorphism. -/
def unionComm : Iso (N.union M) (M.union N) where
  agent := Equiv.sumComm _ _
  wire := Equiv.sumComm _ _
  iface := Equiv.sumComm _ _
  label_agent := unionComm_label_agent N M
  link_map := by
    have hl (q : N.Port) : Port.map (Equiv.sumComm _ _) (unionComm_label_agent N M)
        (Equiv.sumComm _ _) (Equiv.sumComm _ _) (Union.inl N M q) = Union.inr M N q := by
      cases q <;> rfl
    have hr (q : M.Port) : Port.map (Equiv.sumComm _ _) (unionComm_label_agent N M)
        (Equiv.sumComm _ _) (Equiv.sumComm _ _) (Union.inr N M q) = Union.inl M N q := by
      cases q <;> rfl
    exact union_link_ext N M _ (fun q => by rw [hl, hl, union_link_inr])
      (fun q => by rw [hr, hr, union_link_inl])

theorem unionAssoc_label_agent (a : ((N.union M).union K).Agent) :
    (N.union (M.union K)).label (Equiv.sumAssoc _ _ _ a) = ((N.union M).union K).label a := by
  rcases a with (_ | _) | _ <;> rfl

/-- Union is associative up to isomorphism. -/
def unionAssoc : Iso ((N.union M).union K) (N.union (M.union K)) where
  agent := Equiv.sumAssoc _ _ _
  wire := Equiv.sumAssoc _ _ _
  iface := Equiv.sumAssoc _ _ _
  label_agent := unionAssoc_label_agent N M K
  link_map := by
    have h₁ (q : N.Port) : Port.map (Equiv.sumAssoc _ _ _) (unionAssoc_label_agent N M K)
        (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) (Union.inl (N.union M) K (Union.inl N M q)) =
        Union.inl N (M.union K) q := by
      cases q <;> rfl
    have h₂ (q : M.Port) : Port.map (Equiv.sumAssoc _ _ _) (unionAssoc_label_agent N M K)
        (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) (Union.inl (N.union M) K (Union.inr N M q)) =
        Union.inr N (M.union K) (Union.inl M K q) := by
      cases q <;> rfl
    have h₃ (q : K.Port) : Port.map (Equiv.sumAssoc _ _ _) (unionAssoc_label_agent N M K)
        (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) (Union.inr (N.union M) K q) =
        Union.inr N (M.union K) (Union.inr M K q) := by
      cases q <;> rfl
    exact union_link_ext (N.union M) K _
      (union_link_ext N M _ (fun q => by simp only [h₁, Union.link_inl])
        (fun q => by simp only [h₂, Union.link_inl, Union.link_inr]))
      (fun q => by simp only [h₃, Union.link_inr])

end laws

end Net

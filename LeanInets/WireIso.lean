module

public import LeanInets.Connect
public import LeanInets.Plug

/-!
# Isomorphism up to wires

Two nets are *isomorphic up to wires* if there are bijections between their agents and between
their interfaces that preserve labels and map partners to partners. Wires themselves are
ignored, so chains of wires, the orientation of wires and closed loops of wires do not matter.
Since partners are unique and always exist, a bijection that maps partners to partners also
reflects them (`WireIso.partner_port_iff`).

Nets with the same interface are *equivalent* (`≈`) if they are isomorphic up to wires by an
isomorphism that is the identity on the interface.

Isomorphic nets are isomorphic up to wires, and union and trace respect isomorphism up to wires
(`WireIso.union`, `WireIso.trace`). For the trace, the walk from a terminal port of `N.trace`
alternates between walks in `N` and jumps between the two ends of a traced pair of ports
(`Trace.Chain`); it is therefore determined by the partners in `N`.
-/

@[expose] public section

namespace Net

variable {S : Signature} {ι ι' ι'' : Type}

/-- An isomorphism up to wires between the nets `N` and `M`: a renaming that maps partners to
partners. -/
structure WireIso (N : Net S ι) (M : Net S ι') extends Renaming N M where
  partner_map : ∀ {x y : N.TPort}, N.Partner x y →
    M.Partner (x.map agent label_agent id iface) (y.map agent label_agent id iface)

namespace WireIso

variable {N : Net S ι} {M : Net S ι'} {K : Net S ι''}

/-- The bijection on terminal ports induced by an isomorphism up to wires. -/
abbrev port (e : WireIso N M) : N.TPort ≃ M.TPort := e.toRenaming.port (.refl Empty)

variable (e : WireIso N M)

theorem partner_port {x y : N.TPort} (h : N.Partner x y) : M.Partner (e.port x) (e.port y) :=
  e.partner_map h

/-- Isomorphisms up to wires preserve and reflect partners. -/
theorem partner_port_iff {x y : N.TPort} : M.Partner (e.port x) (e.port y) ↔ N.Partner x y :=
  ⟨partner_reflect e.port e.port.injective fun _ _ => e.partner_port, e.partner_port⟩

/-- The identity. -/
@[refl] protected def refl (N : Net S ι) : WireIso N N where
  toRenaming := .refl N
  partner_map {x y} h := by
    change N.Partner ((Renaming.refl N).port (.refl Empty) x)
      ((Renaming.refl N).port (.refl Empty) y)
    rwa [Renaming.refl_port, Renaming.refl_port]

/-- The inverse. -/
@[symm] protected def symm : WireIso M N where
  toRenaming := e.toRenaming.symm
  partner_map {x y} h := by
    change N.Partner (e.port.symm x) (e.port.symm y)
    rw [← e.partner_port_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact h

/-- The composition. -/
@[trans] protected def trans (e' : WireIso M K) : WireIso N K where
  toRenaming := e.toRenaming.trans e'.toRenaming
  partner_map {x y} h := by
    change K.Partner ((e.toRenaming.trans e'.toRenaming).port ((Equiv.refl _).trans (.refl _)) x)
      ((e.toRenaming.trans e'.toRenaming).port ((Equiv.refl _).trans (.refl _)) y)
    rw [Renaming.trans_port, Renaming.trans_port]
    exact e'.partner_port (e.partner_port h)

end WireIso

/-! ### Equivalence -/

/-- Nets are equivalent if they are isomorphic up to wires, by an isomorphism that is the
identity on the interface. -/
instance setoid (S : Signature) (ι : Type) : Setoid (Net S ι) where
  r N M := ∃ e : WireIso N M, ∀ i, e.iface i = i
  iseqv := ⟨fun N => ⟨.refl N, fun _ => rfl⟩,
    fun ⟨e, h⟩ => ⟨e.symm, fun i => e.iface.symm_apply_eq.mpr (h i).symm⟩,
    fun ⟨e, h⟩ ⟨e', h'⟩ => ⟨e.trans e', fun i => (h' _).trans (h i)⟩⟩

theorem equiv_def {N M : Net S ι} : N ≈ M ↔ ∃ e : WireIso N M, ∀ i, e.iface i = i := Iff.rfl

/-- An isomorphism up to wires that is the identity on the interface shows that two nets are
equivalent. The side condition is usually proved automatically. -/
theorem WireIso.equiv {N M : Net S ι} (e : WireIso N M)
    (h : ∀ i, e.iface i = i := by iface_rfl) : N ≈ M :=
  ⟨e, h⟩

theorem WireIso.symm_trans_iface {N M K : Net S ι} (e : WireIso N M) (e' : WireIso N K)
    (he : ∀ i, e.iface i = i) (he' : ∀ i, e'.iface i = i) (i : ι) :
    (e.symm.trans e').iface i = i := by
  change e'.iface (e.iface.symm i) = i
  rw [e.iface.symm_apply_eq.mpr (he i).symm, he']

/-! ### Isomorphisms are isomorphisms up to wires -/

namespace Iso

variable {N : Net S ι} {M : Net S ι'} (e : Iso N M)

theorem port_tport (x : N.TPort) :
    e.port (N.tport x) = M.tport (e.toRenaming.port (.refl Empty) x) := by
  rcases x with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl

/-- An isomorphism is an isomorphism up to wires. -/
def wireIso : WireIso N M where
  toRenaming := e.toRenaming
  partner_map h := Partner.map e.port e.wire e.link_port (fun _ _ => rfl) (port_tport e _)
    (port_tport e _) h

/-- An isomorphism that is the identity on the interface shows that two nets are equivalent. The
side condition is usually proved automatically. -/
theorem equiv {N M : Net S ι} (e : Iso N M) (h : ∀ i, e.iface i = i := by iface_rfl) :
    N ≈ M :=
  e.wireIso.equiv h

end Iso

/-- Swapping the interface twice gives back an equivalent net. -/
theorem swap_swap_equiv {α β : Type} (N : Net S (α ⊕ β)) : N.swap.swap ≈ N :=
  (swapSwap N).equiv

/-- Reindexing respects equivalence. -/
theorem reindex_equiv (σ : ι ≃ ι') {N M : Net S ι} (h : N ≈ M) : N.reindex σ ≈ M.reindex σ :=
  let ⟨e, he⟩ := h
  ⟨(reindexIso σ N).wireIso.symm.trans (e.trans (reindexIso σ M).wireIso), fun i => by
    change σ (e.iface (σ.symm i)) = i
    rw [he, Equiv.apply_symm_apply]⟩

/-! ### Union respects isomorphism up to wires -/

section union

variable (N : Net S ι) (M : Net S ι')

namespace Union

/-- The terminal ports of `N` as terminal ports of the union. -/
def inlT : N.TPort → (N.union M).TPort := Port.map Sum.inl (fun _ => rfl) id Sum.inl

/-- The terminal ports of `M` as terminal ports of the union. -/
def inrT : M.TPort → (N.union M).TPort := Port.map Sum.inr (fun _ => rfl) id Sum.inr

theorem casesT (x : (N.union M).TPort) : (∃ x', x = inlT N M x') ∨ ∃ x', x = inrT N M x' := by
  rcases x with (i | j) | (a | b) | ⟨a | b, k⟩ | ⟨⟨⟩, _⟩
  · exact .inl ⟨.free i, rfl⟩
  · exact .inr ⟨.free j, rfl⟩
  · exact .inl ⟨.pri a, rfl⟩
  · exact .inr ⟨.pri b, rfl⟩
  · exact .inl ⟨.aux a k, rfl⟩
  · exact .inr ⟨.aux b k, rfl⟩

variable {N M}

theorem partner_inlT {x y : N.TPort} (h : N.Partner x y) :
    (N.union M).Partner (inlT N M x) (inlT N M y) :=
  Partner.map (Union.inl N M) Sum.inl (union_link_inl N M) (fun _ _ => rfl)
    (by rcases x with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl) (by rcases y with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl) h

theorem partner_inrT {x y : M.TPort} (h : M.Partner x y) :
    (N.union M).Partner (inrT N M x) (inrT N M y) :=
  Partner.map (Union.inr N M) Sum.inr (union_link_inr N M) (fun _ _ => rfl)
    (by rcases x with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl) (by rcases y with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl) h

/-- The partner of a terminal port of `N` in the union is its partner in `N`. -/
theorem exists_of_partner_inlT {x : N.TPort} {y : (N.union M).TPort}
    (h : (N.union M).Partner (inlT N M x) y) : ∃ z, y = inlT N M z ∧ N.Partner x z := by
  obtain ⟨z, hz⟩ := Partner.exists x
  exact ⟨z, h.unique (partner_inlT hz), hz⟩

/-- The partner of a terminal port of `M` in the union is its partner in `M`. -/
theorem exists_of_partner_inrT {x : M.TPort} {y : (N.union M).TPort}
    (h : (N.union M).Partner (inrT N M x) y) : ∃ z, y = inrT N M z ∧ M.Partner x z := by
  obtain ⟨z, hz⟩ := Partner.exists x
  exact ⟨z, h.unique (partner_inrT hz), hz⟩

end Union

variable {κ κ' : Type} {N : Net S ι} {N' : Net S ι'} {M : Net S κ} {M' : Net S κ'}
  (e : WireIso N N') (f : WireIso M M')

/-- Union respects isomorphism up to wires. -/
def WireIso.union : WireIso (N.union M) (N'.union M') where
  toRenaming := e.toRenaming.union f.toRenaming
  partner_map {x y} h := by
    rcases Union.casesT N M x with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · obtain ⟨z, rfl, hz⟩ := Union.exists_of_partner_inlT h
      have := Union.partner_inlT (M := M') (e.partner_port hz)
      rcases x with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rcases z with _ | _ | _ | ⟨⟨⟩, _⟩ <;> exact this
    · obtain ⟨z, rfl, hz⟩ := Union.exists_of_partner_inrT h
      have := Union.partner_inrT (N := N') (f.partner_port hz)
      rcases x with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rcases z with _ | _ | _ | ⟨⟨⟩, _⟩ <;> exact this

end union

/-! ### Trace respects isomorphism up to wires -/

section trace

variable {κ : Type} (N : Net S ((ι ⊕ κ) ⊕ κ))

namespace Trace

/-- The terminal ports of the trace, as terminal ports of `N`. -/
def upT : N.trace.TPort → N.TPort := Port.map id (fun _ => rfl) id (Sum.inl ∘ Sum.inl)

theorem up_tport (x : N.trace.TPort) : up N (N.trace.tport x) = N.tport (upT N x) := by
  rcases x with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl

theorem back_tport_upT (x : N.trace.TPort) : back N (N.tport (upT N x)) = N.trace.tport x := by
  rcases x with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl

theorem reach_back {p q : N.Port} (h : Relation.ReflTransGen N.Step p q) :
    Relation.ReflTransGen N.trace.Step (back N p) (back N q) :=
  reach_map (M := N.trace) (back N) id (trace_link_back N) (fun _ _ => rfl) h

/-- The walk in `N.trace` from a terminal port, decomposed into walks in `N`. `Chain x y` says
that the walk from the terminal port `x` of `N` reaches `y`, jumping between the two ends of
traced pairs of ports any number of times. -/
inductive Chain : N.TPort → N.trace.TPort → Prop
  /-- The walk reaches a terminal port that is not traced. -/
  | stop {x y} : N.Partner x (upT N y) → Chain x y
  /-- The walk reaches the traced port `inl (inr k)` and continues from `inr k`. -/
  | jumpL {x k y} : N.Partner x (.free (.inl (.inr k))) → Chain (.free (.inr k)) y → Chain x y
  /-- The walk reaches the traced port `inr k` and continues from `inl (inr k)`. -/
  | jumpR {x k y} : N.Partner x (.free (.inr k)) → Chain (.free (.inl (.inr k))) y → Chain x y

variable {N}

theorem Chain.sound {x y} (h : Chain N x y) :
    Relation.ReflTransGen N.trace.Step (back N (N.link (N.tport x))) (N.trace.tport y) := by
  induction h with
  | stop h =>
    have := reach_back N h
    rwa [back_tport_upT] at this
  | @jumpL x k y h _ ih =>
    have := reach_back N h
    rw [tport_free, back_free_inl_inr] at this
    exact this.trans ih
  | @jumpR x k y h _ ih =>
    have := reach_back N h
    rw [tport_free, back_free_inr] at this
    exact this.trans ih

/-- A walk in `N.trace` from a port coming from a walk in `N` gives a chain. -/
theorem Chain.of_reach {u : N.trace.Port} {y : N.trace.TPort}
    (hE : ∀ x a, Relation.ReflTransGen N.Step (N.link (N.tport x)) a → a.IsEntity →
      u = back N a → Chain N x y)
    (hfree : ∀ x i, N.Partner x (upT N (.free i)) → u = .free i → Chain N x y)
    (x : N.TPort) (a : N.Port) (ha : Relation.ReflTransGen N.Step (N.link (N.tport x)) a)
    (hu : u = back N a) : Chain N x y := by
  rcases a with ((i | k) | k) | a
  · exact hfree x i ha hu
  · exact .jumpL ha (hE _ _ .refl (N.link_free _) (hu.trans (back_free_inl_inr N k)))
  · exact .jumpR ha (hE _ _ .refl (N.link_free _) (hu.trans (back_free_inr N k)))
  all_goals exact hE x _ ha trivial hu

theorem Chain.complete {u : N.trace.Port} {y : N.trace.TPort}
    (h : Relation.ReflTransGen N.trace.Step u (N.trace.tport y)) (x : N.TPort) (a : N.Port)
    (ha : Relation.ReflTransGen N.Step (N.link (N.tport x)) a) (hu : u = back N a) :
    Chain N x y := by
  induction h using Relation.ReflTransGen.head_induction_on generalizing x a with
  | refl =>
    refine Chain.of_reach (fun x a ha hE hu => ?_) (fun x i hx hu => ?_) x a ha hu
    · have : a = N.tport (upT N y) := by
        rcases a with _ | b | ⟨b, j⟩ | ⟨w, s⟩
        · exact absurd hE (Port.not_isEntity_free _)
        · rcases y with _ | _ | _ | ⟨⟨⟩, _⟩ <;> cases hu
          rfl
        · rcases y with _ | _ | _ | ⟨⟨⟩, _⟩ <;> cases hu
          rfl
        · exact absurd hu (tport_ne_wire (N := N.trace) y w s)
      exact .stop (by rw [Partner, ← this]; exact ha)
    · rcases y with _ | _ | _ | ⟨⟨⟩, _⟩ <;> cases hu
      exact .stop hx
  | head hstep _ ih =>
    refine Chain.of_reach (fun x a ha hE hu => ?_) (fun x i _ hu => ?_) x a ha hu
    · obtain ⟨w, s, hw, rfl⟩ := hstep.eq
      obtain rfl : a = .wire w s := by
        rcases a with _ | _ | _ | _
        · exact absurd hE (Port.not_isEntity_free _)
        all_goals cases hu.symm.trans hw
        rfl
      exact ih x _ (ha.tail (step_wire (N := N) w s)) rfl
    · obtain ⟨w, s, hw, -⟩ := hstep.eq
      cases hu.symm.trans hw

/-- The partners in a trace are given by chains. -/
theorem partner_iff_chain {x y : N.trace.TPort} : N.trace.Partner x y ↔ Chain N (upT N x) y := by
  unfold Partner
  constructor
  · intro h
    exact Chain.complete h _ _ .refl (by rw [← up_tport])
  · intro h
    have := h.sound
    rwa [← up_tport] at this

end Trace

variable {κ' : Type} {N} {N' : Net S ((ι' ⊕ κ') ⊕ κ')} (e : WireIso N N') {σ : ι ≃ ι'}
  {τ : κ ≃ κ'} (h : ∀ x, e.iface x = Equiv.sumCongr (Equiv.sumCongr σ τ) τ x)
include h

theorem WireIso.port_upT (x : N.trace.TPort) :
    e.port (Trace.upT N x) = Trace.upT N' ((e.toRenaming.trace σ).port (.refl Empty) x) := by
  rcases x with i | _ | _ | ⟨⟨⟩, _⟩
  · exact congrArg Port.free (h _)
  all_goals rfl

theorem Trace.Chain.map {x y} (hc : Chain N x y) :
    Chain N' (e.port x) ((e.toRenaming.trace σ).port (.refl Empty) y) := by
  induction hc with
  | stop hp =>
    have := e.partner_port hp
    rw [e.port_upT h] at this
    exact .stop this
  | @jumpL x k y hp _ ih =>
    have := e.partner_port hp
    rw [Renaming.port_free, h] at this
    rw [Renaming.port_free, h] at ih
    exact .jumpL this ih
  | @jumpR x k y hp _ ih =>
    have := e.partner_port hp
    rw [Renaming.port_free, h] at this
    rw [Renaming.port_free, h] at ih
    exact .jumpR this ih

/-- Trace respects isomorphism up to wires, if the isomorphism maps the traced ports to traced
ports. -/
def WireIso.trace : WireIso N.trace N'.trace where
  toRenaming := e.toRenaming.trace σ
  partner_map hp := by
    have := (Trace.partner_iff_chain.mp hp).map e h
    rw [e.port_upT h] at this
    exact Trace.partner_iff_chain.mpr this

end trace

/-- An isomorphism up to wires between nets with the same interface that is the identity on the
interface gives an isomorphism up to wires of their traces. -/
def WireIso.traceSelf {κ : Type} {N N' : Net S ((ι ⊕ κ) ⊕ κ)} (e : WireIso N N')
    (h : ∀ x, e.iface x = x := by iface_rfl) : WireIso N.trace N'.trace :=
  e.trace (σ := .refl _) (τ := .refl _) fun x => by rw [h]; rcases x with (_ | _) | _ <;> rfl

/-- Trace respects equivalence. -/
theorem trace_equiv {κ : Type} {N N' : Net S ((ι ⊕ κ) ⊕ κ)} (h : N ≈ N') : N.trace ≈ N'.trace :=
  let ⟨e, he⟩ := h
  ⟨e.traceSelf he, fun _ => rfl⟩

/-- Union respects equivalence. -/
theorem union_equiv {N N' : Net S ι} {M M' : Net S ι'} (hN : N ≈ N') (hM : M ≈ M') :
    N.union M ≈ N'.union M' :=
  let ⟨e, he⟩ := hN
  let ⟨f, hf⟩ := hM
  ⟨e.union f, by rintro (i | j); exacts [congrArg Sum.inl (he i), congrArg Sum.inr (hf j)]⟩

/-- Plugging respects isomorphism up to wires that is the identity on the interfaces. -/
def WireIso.plugSelf {κ : Type} {C C' : Net S (ι ⊕ κ)} {R R' : Net S κ} (e : WireIso C C')
    (f : WireIso R R') (he : ∀ x, e.iface x = x := by iface_rfl)
    (hf : ∀ k, f.iface k = k := by iface_rfl) :
    WireIso (C.plug R) (C'.plug R') :=
  (e.union f).traceSelf
    (by rintro (i | k); exacts [congrArg Sum.inl (he i), congrArg Sum.inr (hf k)])

/-- Plugging respects equivalence. -/
theorem plug_equiv {κ : Type} {C C' : Net S (ι ⊕ κ)} {R R' : Net S κ} (hC : C ≈ C')
    (hR : R ≈ R') : C.plug R ≈ C'.plug R' :=
  trace_equiv (union_equiv hC hR)

/-- Gluing respects equivalence. -/
theorem glue_equiv {κ : Type} {N N' : Net S (ι ⊕ κ)} {M M' : Net S (κ ⊕ ι')} (hN : N ≈ N')
    (hM : M ≈ M') : N.glue M ≈ N'.glue M' :=
  trace_equiv (reindex_equiv _ (union_equiv hN hM))

end Net

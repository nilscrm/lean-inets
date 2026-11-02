module

public import LeanInets.Union

/-!
# Trace

The trace of a net `N` with interface `(ι ⊕ κ) ⊕ κ` connects, for each `k : κ`, the free port
`inl (inr k)` with the free port `inr k`: the two ports linked to them become linked to each
other. Since free ports are only ever linked to entity ports, this never creates chains of
free ports that would have to be followed. The result has interface `ι`.

The ports of `N.trace` are the ports of `N` that are not traced; `Trace.back` sends every port
of `N` to the trace, a traced free port to the port linked to its mate. It commutes with links
(`trace_link_back`), which is all that is needed to work with traces.

Trace respects isomorphism (`Iso.trace`, which also covers renaming the interface and the traced
ports), and satisfies the two structural laws of a trace:

* superposing (`traceUnion`): a union with a trace is the trace of the union;
* vanishing (`traceTrace`): tracing twice is tracing once over both sets of ports.
-/

@[expose] public section

namespace Net

variable {S : Signature}

section trace

variable {ι κ : Type} (N : Net S ((ι ⊕ κ) ⊕ κ))

/-- The ports of the trace of `N`. -/
abbrev TracePort := _root_.Port N.label N.Wire ι

namespace Trace

/-- The ports of the trace, as ports of `N`. -/
def up : TracePort N → N.Port := Port.map id (fun _ => rfl) id (Sum.inl ∘ Sum.inl)

/-- Where a port of `N` ends up in the trace. A traced free port is identified with the port
that is linked to its mate. -/
def back : N.Port → TracePort N
  | .free (.inl (.inl i)) => .free i
  | .free (.inl (.inr k)) => (N.link (.free (.inr k))).ofEntity (N.link_free _)
  | .free (.inr k) => (N.link (.free (.inl (.inr k)))).ofEntity (N.link_free _)
  | .pri a => .pri a
  | .aux a j => .aux a j
  | .wire w s => .wire w s

@[simp] theorem back_up (p : TracePort N) : back N (up N p) = p := by
  cases p <;> rfl

theorem back_of_isEntity (q : N.Port) (h : q.IsEntity) : back N q = q.ofEntity h := by
  cases q
  · exact absurd h (Port.not_isEntity_free _)
  all_goals rfl

theorem up_back_of_isEntity (q : N.Port) (h : q.IsEntity) : up N (back N q) = q := by
  rw [back_of_isEntity N q h]
  exact Port.map_ofEntity _ _ _

theorem back_free_inl_inr (k : κ) :
    back N (.free (.inl (.inr k))) = back N (N.link (.free (.inr k))) :=
  (back_of_isEntity N _ _).symm

theorem back_free_inr (k : κ) :
    back N (.free (.inr k)) = back N (N.link (.free (.inl (.inr k)))) :=
  (back_of_isEntity N _ _).symm

theorem isEntity_back {q : N.Port} (h : q.IsEntity) : (back N q).IsEntity := by
  cases q
  · exact absurd h (Port.not_isEntity_free _)
  all_goals trivial

theorem back_link_up_back (q : N.Port) :
    back N (N.link (up N (back N q))) = back N (N.link q) := by
  rcases q with ((i | k) | k) | q
  · rfl
  · rw [back_free_inl_inr, up_back_of_isEntity _ _ (N.link_free _), N.link_link, back_free_inr]
  · rw [back_free_inr, up_back_of_isEntity _ _ (N.link_free _), N.link_link, back_free_inl_inr]
  all_goals rfl

/-- To compute a function on `back`, it suffices to know it on entity ports and on free ports
that are not traced, provided the other side identifies each traced port with the port linked to
its mate. -/
theorem back_ext {X : Type} (F : TracePort N → X) (G : N.Port → X)
    (hent : ∀ q, q.IsEntity → F (back N q) = G q)
    (hfree : ∀ i, F (.free i) = G (.free (.inl (.inl i))))
    (hl : ∀ k, G (.free (.inl (.inr k))) = G (N.link (.free (.inr k))))
    (hr : ∀ k, G (.free (.inr k)) = G (N.link (.free (.inl (.inr k))))) (q : N.Port) :
    F (back N q) = G q := by
  rcases q with ((i | k) | k) | q
  · exact hfree i
  · rw [back_free_inl_inr, hent _ (N.link_free _), hl]
  · rw [back_free_inr, hent _ (N.link_free _), hr]
  all_goals exact hent _ trivial

end Trace

/-- The trace of `N`: for each `k : κ`, the free ports `inl (inr k)` and `inr k` are connected
to each other. -/
@[reducible] def trace : Net S ι where
  Agent := N.Agent
  Wire := N.Wire
  label := N.label
  link p := Trace.back N (N.link (Trace.up N p))
  link_link p := by
    change Trace.back N (N.link (Trace.up N (Trace.back N (N.link (Trace.up N p))))) = p
    rw [Trace.back_link_up_back, N.link_link, Trace.back_up]
  link_ne p h := by
    generalize hq : N.link (Trace.up N p) = q at h
    subst h
    rcases q with ((i | k) | k) | q
    · exact N.link_ne _ hq
    · rw [Trace.back_free_inl_inr, Trace.up_back_of_isEntity _ _ (N.link_free _),
        N.link_link] at hq
      cases hq
    · rw [Trace.back_free_inr, Trace.up_back_of_isEntity _ _ (N.link_free _),
        N.link_link] at hq
      cases hq
    all_goals exact N.link_ne _ hq
  link_free _ := Trace.isEntity_back N (N.link_free _)

theorem trace_link_back (q : N.Port) :
    N.trace.link (Trace.back N q) = Trace.back N (N.link q) :=
  Trace.back_link_up_back N q

/-- To show that a map of ports out of a trace commutes with the links, it suffices to check
this on the images of the ports of `N`. -/
theorem trace_link_ext {ι' : Type} {X : Net S ι'} (F : N.trace.Port → X.Port)
    (h : ∀ q, X.link (F (Trace.back N q)) = F (Trace.back N (N.link q)))
    (p : N.trace.Port) : X.link (F p) = F (N.trace.link p) := by
  rw [← Trace.back_up N p, h, trace_link_back]

end trace

/-! ### Trace respects isomorphism -/

section congr

variable {ι κ ι' κ' : Type} {N : Net S ((ι ⊕ κ) ⊕ κ)} {N' : Net S ((ι' ⊕ κ') ⊕ κ')}

/-- A renaming of nets, as a renaming of their traces with interface map `σ`. -/
def Renaming.trace (e : Renaming N N') (σ : ι ≃ ι') : Renaming N.trace N'.trace where
  agent := e.agent
  iface := σ
  label_agent := e.label_agent

variable (e : Iso N N') (σ : ι ≃ ι') (τ : κ ≃ κ')

/-- The map of ports underlying `Iso.trace`. -/
abbrev Iso.tracePort : N.trace.Port → N'.trace.Port := (e.toRenaming.trace σ).port e.wire

variable {σ τ} (h : ∀ x, e.iface x = Equiv.sumCongr (Equiv.sumCongr σ τ) τ x)
include h

theorem Iso.tracePort_back (q : N.Port) :
    e.tracePort σ (Trace.back N q) = Trace.back N' (e.port q) := by
  refine Trace.back_ext N (e.tracePort σ) (fun q => Trace.back N' (e.port q)) ?_ ?_ ?_ ?_ q
  · intro q hq
    cases q
    · exact absurd hq (Port.not_isEntity_free _)
    all_goals rfl
  · intro i
    simp only [Renaming.port_free, h]
    rfl
  · intro k
    simp only [← e.link_port, Renaming.port_free, h]
    exact Trace.back_free_inl_inr N' (τ k)
  · intro k
    simp only [← e.link_port, Renaming.port_free, h]
    exact Trace.back_free_inr N' (τ k)

/-- Trace respects isomorphism, if the isomorphism maps the traced ports to traced ports. -/
def Iso.trace : Iso N.trace N'.trace where
  toRenaming := e.toRenaming.trace σ
  wire := e.wire
  link_map := trace_link_ext N (e.tracePort σ) fun q => by
    rw [tracePort_back e h, tracePort_back e h, trace_link_back, e.link_port]

end congr

/-! ### Superposing -/

section superpose

variable {ι κ ι' : Type} (N : Net S ((ι ⊕ κ) ⊕ κ)) (M : Net S ι')

/-- Moving the interface of `M` past the traced ports of `N`. -/
def traceUnionEquiv (ι κ ι' : Type) : ((ι ⊕ κ) ⊕ κ) ⊕ ι' ≃ ((ι ⊕ ι') ⊕ κ) ⊕ κ where
  toFun
    | .inl (.inl (.inl i)) => .inl (.inl (.inl i))
    | .inl (.inl (.inr k)) => .inl (.inr k)
    | .inl (.inr k) => .inr k
    | .inr j => .inl (.inl (.inr j))
  invFun
    | .inl (.inl (.inl i)) => .inl (.inl (.inl i))
    | .inl (.inl (.inr j)) => .inr j
    | .inl (.inr k) => .inl (.inl (.inr k))
    | .inr k => .inl (.inr k)
  left_inv x := by rcases x with ((_ | _) | _) | _ <;> rfl
  right_inv x := by rcases x with ((_ | _) | _) | _ <;> rfl

/-- The trace of the union of `N` and `M`, along the traced ports of `N`. -/
abbrev traceUnionNet : Net S (ι ⊕ ι') :=
  ((N.union M).reindex (traceUnionEquiv ι κ ι')).trace

namespace TraceUnion

/-- The ports of `N` in `traceUnionNet N M`. -/
def inl (q : N.Port) : (traceUnionNet N M).Port :=
  Trace.back ((N.union M).reindex (traceUnionEquiv ι κ ι'))
    ((N.union M).reindexPort (traceUnionEquiv ι κ ι') (Union.inl N M q))

/-- The ports of `M` in `traceUnionNet N M`. -/
def inr (q : M.Port) : (traceUnionNet N M).Port :=
  Trace.back ((N.union M).reindex (traceUnionEquiv ι κ ι'))
    ((N.union M).reindexPort (traceUnionEquiv ι κ ι') (Union.inr N M q))

theorem link_inl (q : N.Port) :
    (traceUnionNet N M).link (inl N M q) = inl N M (N.link q) := by
  unfold inl
  rw [trace_link_back, reindex_link, union_link_inl]

theorem link_inr (q : M.Port) :
    (traceUnionNet N M).link (inr N M q) = inr N M (M.link q) := by
  unfold inr
  rw [trace_link_back, reindex_link, union_link_inr]

theorem union_inl_back (q : N.Port) : Union.inl N.trace M (Trace.back N q) = inl N M q := by
  refine Trace.back_ext N _ (inl N M) (fun q hq => ?_) (fun _ => rfl) (fun k => ?_) (fun k => ?_) q
  · cases q
    · exact absurd hq (Port.not_isEntity_free _)
    all_goals rfl
  · exact (Trace.back_free_inl_inr _ k).trans (congrArg (Trace.back _)
      ((reindex_link _ (N.union M) (Union.inl N M (.free (.inr k)))).trans
        (congrArg _ (union_link_inl N M _))))
  · exact (Trace.back_free_inr _ k).trans (congrArg (Trace.back _)
      ((reindex_link _ (N.union M) (Union.inl N M (.free (.inl (.inr k))))).trans
        (congrArg _ (union_link_inl N M _))))

theorem union_inr (q : M.Port) : Union.inr N.trace M q = inr N M q := by
  cases q <;> rfl

end TraceUnion

/-- Superposing: the union of a trace with a net is the trace of the union. -/
def traceUnion : Iso (N.trace.union M) (traceUnionNet N M) where
  agent := .refl _
  wire := .refl _
  iface := .refl _
  label_agent _ := rfl
  link_map p := by
    simp only [Equiv.coe_refl, Port.map_id]
    refine union_link_ext N.trace M (X := traceUnionNet N M) (fun p => p) (fun q => ?_)
      (fun q => ?_) p
    · rw [← Trace.back_up N q, TraceUnion.union_inl_back, TraceUnion.link_inl, trace_link_back,
        TraceUnion.union_inl_back]
    · rw [TraceUnion.union_inr, TraceUnion.link_inr, TraceUnion.union_inr]

end superpose

/-! ### Vanishing -/

section vanish

variable {ι κ μ : Type} (N : Net S ((((ι ⊕ κ) ⊕ κ) ⊕ μ) ⊕ μ))

/-- Combining two sets of traced ports. -/
def traceTraceEquiv (ι κ μ : Type) : (((ι ⊕ κ) ⊕ κ) ⊕ μ) ⊕ μ ≃ (ι ⊕ (κ ⊕ μ)) ⊕ (κ ⊕ μ) where
  toFun
    | .inl (.inl (.inl (.inl i))) => .inl (.inl i)
    | .inl (.inl (.inl (.inr k))) => .inl (.inr (.inl k))
    | .inl (.inl (.inr k)) => .inr (.inl k)
    | .inl (.inr m) => .inl (.inr (.inr m))
    | .inr m => .inr (.inr m)
  invFun
    | .inl (.inl i) => .inl (.inl (.inl (.inl i)))
    | .inl (.inr (.inl k)) => .inl (.inl (.inl (.inr k)))
    | .inl (.inr (.inr m)) => .inl (.inr m)
    | .inr (.inl k) => .inl (.inl (.inr k))
    | .inr (.inr m) => .inr m
  left_inv x := by rcases x with (((_ | _) | _) | _) | _ <;> rfl
  right_inv x := by rcases x with (_ | _ | _) | _ | _ <;> rfl

/-- The trace of `N` along both sets of traced ports at once. -/
abbrev traceTraceNet : Net S ι := (N.reindex (traceTraceEquiv ι κ μ)).trace

/-- The ports of `N` in `traceTraceNet N`. -/
def TraceTrace.back (q : N.Port) : (traceTraceNet N).Port :=
  Trace.back (N.reindex (traceTraceEquiv ι κ μ)) (N.reindexPort (traceTraceEquiv ι κ μ) q)

theorem TraceTrace.link_back (q : N.Port) :
    (traceTraceNet N).link (back N q) = back N (N.link q) := by
  unfold back
  rw [trace_link_back, reindex_link]

theorem TraceTrace.back_back_of_isEntity (q : N.Port) (hq : q.IsEntity) :
    Trace.back N.trace (Trace.back N q) = back N q := by
  cases q
  · exact absurd hq (Port.not_isEntity_free _)
  all_goals rfl

theorem TraceTrace.back_back (q : N.Port) :
    Trace.back N.trace (Trace.back N q) = back N q := by
  have hR {x : (ι ⊕ (κ ⊕ μ)) ⊕ (κ ⊕ μ)} (y : (((ι ⊕ κ) ⊕ κ) ⊕ μ) ⊕ μ)
      (h : traceTraceEquiv ι κ μ y = x) :
      (N.reindex (traceTraceEquiv ι κ μ)).link (.free x) =
        N.reindexPort (traceTraceEquiv ι κ μ) (N.link (.free y)) := by
    subst h
    exact reindex_link _ N (.free y)
  refine Trace.back_ext N _ (back N) (back_back_of_isEntity N) (fun i => ?_) (fun m => ?_)
    (fun m => ?_) q
  · rcases i with (i | k) | k
    · rfl
    · rw [Trace.back_free_inl_inr,
        show (Port.free (.inr k) : N.trace.Port) = Trace.back N (.free (.inl (.inl (.inr k))))
          from rfl, trace_link_back, back_back_of_isEntity _ _ (N.link_free _)]
      exact ((Trace.back_free_inl_inr _ (.inl k)).trans
        (congrArg _ (hR (.inl (.inl (.inr k))) rfl))).symm
    · rw [Trace.back_free_inr,
        show (Port.free (.inl (.inr k)) : N.trace.Port) =
          Trace.back N (.free (.inl (.inl (.inl (.inr k))))) from rfl,
        trace_link_back, back_back_of_isEntity _ _ (N.link_free _)]
      exact ((Trace.back_free_inr _ (.inl k)).trans
        (congrArg _ (hR (.inl (.inl (.inl (.inr k)))) rfl))).symm
  · exact (Trace.back_free_inl_inr _ (.inr m)).trans (congrArg _ (hR (.inr m) rfl))
  · exact (Trace.back_free_inr _ (.inr m)).trans (congrArg _ (hR (.inl (.inr m)) rfl))

/-- Vanishing: tracing twice is tracing once, along both sets of traced ports. -/
def traceTrace : Iso N.trace.trace (traceTraceNet N) where
  agent := .refl _
  wire := .refl _
  iface := .refl _
  label_agent _ := rfl
  link_map p := by
    simp only [Equiv.coe_refl, Port.map_id]
    refine trace_link_ext N.trace (X := traceTraceNet N) (fun p => p) (fun q => ?_) p
    rw [← Trace.back_up N q, trace_link_back, TraceTrace.back_back, TraceTrace.back_back,
      TraceTrace.link_back]

end vanish

end Net

module

public import LeanInets.InteractionSystem

/-!
# Active pairs up to wires

Reduction replaces an active pair `α ⋈ β` in a context `C` (`C.plug (activePair α β)`) by the
right-hand side of its rule.

Two agents form an *active pair up to wires* (`Net.IsActivePairW`) if their principal ports
are connected, possibly through wires. Unlike `Net.IsActivePair`, this is invariant under
`≈`.

The main result of this file is that every active pair up to wires can be cut out of its net:
removing the two agents leaves a context `N.removePair a b` with
`N ≈ (N.removePair a b).plug (activePair (N.label a) (N.label b))`
(`Net.equiv_plug_removePair`). In the context, the auxiliary ports of `a` and `b` are replaced
by new wires leading to the hole, and the two principal ports by a single new wire, so that the
path between them becomes a closed loop of wires, which `≈` ignores.
-/

@[expose] public section

namespace Net

variable {S : Signature} {ι : Type}

/-! ### Active pairs up to wires -/

/-- Two agents form an active pair up to wires if they are distinct and their principal ports
are connected, possibly through wires. -/
def IsActivePairW (N : Net S ι) (a b : N.Agent) : Prop :=
  a ≠ b ∧ N.Partner (.pri a) (.pri b)

variable {N : Net S ι}

theorem IsActivePairW.symm {a b : N.Agent} (h : N.IsActivePairW a b) : N.IsActivePairW b a :=
  ⟨h.1.symm, h.2.symm⟩

/-- An agent is part of at most one active pair up to wires. -/
theorem IsActivePairW.unique {a b c : N.Agent} (hb : N.IsActivePairW a b)
    (hc : N.IsActivePairW a c) : b = c :=
  Port.pri.inj (hb.2.unique hc.2 : (Port.pri b : N.TPort) = .pri c)

theorem IsActivePair.isActivePairW {a b : N.Agent} (h : N.IsActivePair a b) :
    N.IsActivePairW a b := by
  refine ⟨h.ne, ?_⟩
  unfold Partner
  rw [tport_pri, h]
  rfl

/-- In a net without wires, active pairs up to wires are just active pairs. -/
theorem isActivePairW_iff_of_isEmpty [IsEmpty N.Wire] {a b : N.Agent} :
    N.IsActivePairW a b ↔ N.IsActivePair a b := by
  refine ⟨fun ⟨_, h⟩ => ?_, IsActivePair.isActivePairW⟩
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, -⟩
  · exact h
  · obtain ⟨w, -, -, -⟩ := hc.eq
    exact isEmptyElim w

/-- Isomorphisms up to wires preserve and reflect active pairs up to wires. -/
theorem WireIso.isActivePairW_iff {M : Net S ι} (e : WireIso N M) {a b : N.Agent} :
    M.IsActivePairW (e.agent a) (e.agent b) ↔ N.IsActivePairW a b :=
  and_congr e.agent.injective.ne_iff (e.partner_port_iff (x := .pri a) (y := .pri b))

/-- The active pair in `C.plug (activePair α β)`. -/
theorem isActivePair_plug_activePair {α β : S.Sym}
    (C : Net S (ι ⊕ (Fin (S.arity α) ⊕ Fin (S.arity β)))) :
    (C.plug (activePair α β)).IsActivePair (.inr .left) (.inr .right) :=
  rfl

/-! ### Removing an active pair -/

namespace RemovePair

variable (N) (a b : N.Agent)

/-- The agents of `N` other than `a` and `b`: the agents of the context. -/
abbrev Agent : Type := {c : N.Agent // c ≠ a ∧ c ≠ b}

/-- The hole of the context: the auxiliary ports of `a`, followed by those of `b`. -/
abbrev Hole : Type := Fin (S.arity (N.label a)) ⊕ Fin (S.arity (N.label b))

/-- The wires of the context: the wires of `N`, a wire replacing the two principal ports
(`none`), and a wire for each auxiliary port of `a` and `b`, leading to the hole. -/
abbrev Wire : Type := N.Wire ⊕ Option (Hole N a b)

/-- The labels of the agents of the context. -/
abbrev label (c : Agent N a b) : S.Sym := N.label c.1

/-- The labels of the agents of the plugged net. -/
abbrev plugLabel : Agent N a b ⊕ ActivePair.Agent → S.Sym :=
  Sum.elim (label N a b) (ActivePair.label (N.label a) (N.label b))

/-- The ports of the context. -/
abbrev CPort : Type := _root_.Port (label N a b) (Wire N a b) (ι ⊕ Hole N a b)

variable {N a b}

open Classical in
/-- Where an agent of `N` ends up in the plugged net. -/
noncomputable def classify (c : N.Agent) : Agent N a b ⊕ ActivePair.Agent :=
  if h : c ≠ a ∧ c ≠ b then .inl ⟨c, h⟩ else if c = a then .inr .left else .inr .right

/-- The agent of `N` corresponding to an agent of the plugged net. -/
def unclassify : Agent N a b ⊕ ActivePair.Agent → N.Agent
  | .inl c => c.1
  | .inr .left => a
  | .inr .right => b

theorem unclassify_classify (c : N.Agent) : unclassify (classify (a := a) (b := b) c) = c := by
  unfold classify
  split_ifs with h h'
  · rfl
  · exact h'.symm
  · simp only [ne_eq, not_and_or, not_not] at h
    exact (h.resolve_left h').symm

theorem classify_a : classify (a := a) (b := b) a = .inr .left := by
  simp [classify]

theorem classify_b (hab : a ≠ b) : classify (a := a) (b := b) b = .inr .right := by
  simp [classify, hab.symm]

theorem label_classify (c : N.Agent) : plugLabel N a b (classify c) = N.label c := by
  have h := unclassify_classify (a := a) (b := b) c
  generalize classify c = z at h
  subst h
  rcases z with c | _ | _ <;> rfl

theorem classify_val (c : Agent N a b) : classify c.1 = .inl c := by
  simp [classify, c.2]

/-- The agents of `N` are those of the context and those of the active pair. -/
noncomputable def agentEquiv (hab : a ≠ b) : N.Agent ≃ Agent N a b ⊕ ActivePair.Agent where
  toFun := classify
  invFun := unclassify
  left_inv := unclassify_classify
  right_inv
    | .inl c => classify_val c
    | .inr .left => classify_a
    | .inr .right => classify_b hab

theorem label_unclassify (z : Agent N a b ⊕ ActivePair.Agent) :
    plugLabel N a b z = N.label (unclassify z) := by
  rcases z with c | _ | _ <;> rfl

/-- The port of the context replacing the principal port of an agent of `N`. -/
def priPort : Agent N a b ⊕ ActivePair.Agent → CPort N a b
  | .inl c => .pri c
  | .inr .left => .wire (.inr none) .l
  | .inr .right => .wire (.inr none) .r

/-- The port of the context replacing an auxiliary port of an agent of `N`. -/
def auxPort : (z : Agent N a b ⊕ ActivePair.Agent) → Fin (S.arity (plugLabel N a b z)) →
    CPort N a b
  | .inl c, k => .aux c k
  | .inr .left, k => .wire (.inr (some (.inl k))) .l
  | .inr .right, k => .wire (.inr (some (.inr k))) .l

/-- The port of the context replacing a port of `N`. -/
noncomputable def port : N.Port → CPort N a b
  | .free i => .free (.inl i)
  | .pri c => priPort (classify c)
  | .aux c k => auxPort (classify c) (k.cast (congrArg S.arity (label_classify c).symm))
  | .wire w s => .wire (.inl w) s

theorem port_pri (c : N.Agent) : port (a := a) (b := b) (.pri c) = priPort (classify c) := rfl

theorem port_aux (c : N.Agent) (k : Fin (S.arity (N.label c))) (z) (hz : classify c = z) :
    port (a := a) (b := b) (.aux c k) =
      auxPort z (k.cast (congrArg S.arity (hz ▸ label_classify c).symm)) := by
  subst hz
  rfl

/-- A left inverse of `port`. The ports of the context that do not come from `N` (the ends of
the new wires at the hole, and the hole itself) are sent to arbitrary ports. -/
def back : CPort N a b → N.Port
  | .free (.inl i) => .free i
  | .free (.inr (.inl k)) => .aux a k
  | .free (.inr (.inr k)) => .aux b k
  | .pri c => .pri c.1
  | .aux c k => .aux c.1 k
  | .wire (.inl w) s => .wire w s
  | .wire (.inr none) .l => .pri a
  | .wire (.inr none) .r => .pri b
  | .wire (.inr (some (.inl k))) _ => .aux a k
  | .wire (.inr (some (.inr k))) _ => .aux b k

theorem back_priPort (z : Agent N a b ⊕ ActivePair.Agent) :
    back (priPort z) = .pri (unclassify z) := by
  rcases z with c | _ | _ <;> rfl

theorem back_auxPort (z : Agent N a b ⊕ ActivePair.Agent) (k) :
    back (auxPort z k) = .aux (unclassify z) (k.cast (congrArg S.arity (label_unclassify z))) := by
  rcases z with c | _ | _ <;> rfl

theorem back_port (p : N.Port) : back (port (a := a) (b := b) p) = p := by
  rcases p with i | c | ⟨c, k⟩ | ⟨w, s⟩
  · rfl
  · rw [port_pri, back_priPort, unclassify_classify]
  · rw [port_aux c k _ rfl, back_auxPort]
    exact Port.aux_congr (unclassify_classify c) rfl
  · rfl

theorem port_injective : Function.Injective (port (N := N) (a := a) (b := b)) :=
  Function.LeftInverse.injective back_port

theorem isEntity_auxPort (z : Agent N a b ⊕ ActivePair.Agent) (k) : (auxPort z k).IsEntity := by
  rcases z with c | _ | _ <;> trivial

theorem isEntity_port {p : N.Port} (h : p.IsEntity) : (port (a := a) (b := b) p).IsEntity := by
  rcases p with i | c | ⟨c, k⟩ | ⟨w, s⟩
  · exact absurd h (Port.not_isEntity_free _)
  · rw [port_pri]
    rcases classify (a := a) (b := b) c with c | _ | _ <;> trivial
  · rw [port_aux c k _ rfl]
    exact isEntity_auxPort _ _
  · trivial

/-- Every port of the context comes from `N`, or is the hole, or is the end of a new wire at
the hole. -/
theorem cases_cport (hab : a ≠ b) (p : CPort N a b) :
    (∃ x, p = port x) ∨ (∃ k, p = .free (.inr k)) ∨ ∃ k, p = .wire (.inr (some k)) .r := by
  rcases p with (i | k) | c | ⟨c, k⟩ | ⟨w | (_ | k | k), _ | _⟩
  · exact .inl ⟨.free i, rfl⟩
  · exact .inr (.inl ⟨k, rfl⟩)
  · exact .inl ⟨.pri c.1, by rw [port_pri, classify_val]; rfl⟩
  · exact .inl ⟨.aux c.1 k, by rw [port_aux c.1 k _ (classify_val c)]; rfl⟩
  · exact .inl ⟨.wire w .l, rfl⟩
  · exact .inl ⟨.wire w .r, rfl⟩
  · exact .inl ⟨.pri a, by rw [port_pri, classify_a]; rfl⟩
  · exact .inl ⟨.pri b, by rw [port_pri, classify_b hab]; rfl⟩
  · exact .inl ⟨.aux a k, by rw [port_aux a k _ classify_a]; rfl⟩
  · exact .inr (.inr ⟨.inl k, rfl⟩)
  · exact .inl ⟨.aux b k, by rw [port_aux b k _ (classify_b hab)]; rfl⟩
  · exact .inr (.inr ⟨.inr k, rfl⟩)

/-- The links of the context. -/
noncomputable def link : CPort N a b → CPort N a b
  | .free (.inl i) => port (N.link (.free i))
  | .free (.inr k) => .wire (.inr (some k)) .r
  | .pri c => port (N.link (.pri c.1))
  | .aux c k => port (N.link (.aux c.1 k))
  | .wire (.inl w) s => port (N.link (.wire w s))
  | .wire (.inr none) .l => port (N.link (.pri a))
  | .wire (.inr none) .r => port (N.link (.pri b))
  | .wire (.inr (some (.inl k))) .l => port (N.link (.aux a k))
  | .wire (.inr (some (.inr k))) .l => port (N.link (.aux b k))
  | .wire (.inr (some k)) .r => .free (.inr k)

theorem link_priPort (z : Agent N a b ⊕ ActivePair.Agent) :
    link (priPort z) = port (N.link (.pri (unclassify z))) := by
  rcases z with c | _ | _ <;> rfl

theorem link_auxPort (z : Agent N a b ⊕ ActivePair.Agent) (k) :
    link (auxPort z k) =
      port (N.link (.aux (unclassify z) (k.cast (congrArg S.arity (label_unclassify z))))) := by
  rcases z with c | _ | _ <;> rfl

theorem link_port (p : N.Port) : link (port (a := a) (b := b) p) = port (N.link p) := by
  rcases p with i | c | ⟨c, k⟩ | ⟨w, s⟩
  · rfl
  · rw [port_pri, link_priPort, unclassify_classify]
  · rw [port_aux c k _ rfl, link_auxPort]
    exact congrArg (fun p => port (N.link p)) (Port.aux_congr (unclassify_classify c) rfl)
  · rfl

end RemovePair

open RemovePair in
open Classical in
/-- The context obtained by removing the agents `a` and `b` from `N`. Its interface consists
of that of `N`, and a hole with the auxiliary ports of `a` and `b`. -/
@[reducible] noncomputable def removePair (N : Net S ι) (a b : N.Agent) (hab : a ≠ b) :
    Net S (ι ⊕ Hole N a b) where
  Agent := RemovePair.Agent N a b
  Wire := RemovePair.Wire N a b
  label := RemovePair.label N a b
  link := RemovePair.link
  link_link p := by
    rcases cases_cport hab p with ⟨x, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [link_port, link_port, N.link_link]
    all_goals rcases k with k | k <;> rfl
  link_ne p := by
    rcases cases_cport hab p with ⟨x, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [link_port]
      exact port_injective.ne (N.link_ne x)
    all_goals rcases k with k | k <;> nofun
  link_free
    | .inl i => isEntity_port (N.link_free i)
    | .inr _ => trivial

/-! ### Cutting out an active pair -/

namespace RemovePair

variable {N : Net S ι} {a b : N.Agent} (hab : a ≠ b)

/-- The net `N` with the active pair `a`, `b` cut out and plugged back in. -/
noncomputable abbrev plugged : Net S ι :=
  (N.removePair a b hab).plug (activePair (N.label a) (N.label b))

theorem label_agentEquiv (c : N.Agent) :
    (plugged hab).label (agentEquiv hab c) = N.label c :=
  label_classify c

/-- The terminal ports of `N` as terminal ports of the plugged net. -/
noncomputable abbrev tportMap (x : N.TPort) : (plugged hab).TPort :=
  x.map (agentEquiv hab) (label_agentEquiv hab) id id

/-- A port of `N` as a port of the context, inside the plugged net. -/
noncomputable def toPlug (p : N.Port) : (plugged hab).Port := Plug.inl _ _ (port p)

theorem link_toPlug (p : N.Port) : (plugged hab).link (toPlug hab p) = toPlug hab (N.link p) := by
  unfold toPlug
  rw [Plug.link_inl]
  rw [show (N.removePair a b hab).link (port p) = port (N.link p) from link_port p]

theorem reach_toPlug_of_reach {p q : N.Port} (h : Relation.ReflTransGen N.Step p q) :
    Relation.ReflTransGen (plugged hab).Step (toPlug hab p) (toPlug hab q) :=
  reach_map (toPlug hab) (fun w => .inl (.inl w)) (link_toPlug hab) (fun _ _ => rfl) h

theorem reach_auxPort (z : RemovePair.Agent N a b ⊕ ActivePair.Agent)
    (k : Fin (S.arity (plugLabel N a b z))) :
    Relation.ReflTransGen (plugged hab).Step (Plug.inl _ _ (auxPort z k))
      ((plugged hab).tport (.aux z k)) := by
  rcases z with c | _ | _
  · exact .refl
  · exact .single rfl
  · exact .single rfl

/-- The walk from a port of `N` that is not one of the two principal ports, mapped into the
plugged net, ends at the corresponding port of the plugged net. -/
theorem reach_toPlug (y : N.TPort) (ha : y ≠ .pri a) (hb : y ≠ .pri b) :
    Relation.ReflTransGen (plugged hab).Step (toPlug hab (N.tport y))
      ((plugged hab).tport (tportMap hab y)) := by
  rcases y with i | c | ⟨c, k⟩ | ⟨⟨⟩, _⟩
  · exact .refl
  · have hc : c ≠ a ∧ c ≠ b := ⟨fun h => ha (h ▸ rfl), fun h => hb (h ▸ rfl)⟩
    change Relation.ReflTransGen _ (toPlug hab (.pri c)) (.pri (classify c))
    unfold toPlug
    rw [port_pri, classify_val ⟨c, hc⟩]
    exact .refl
  · exact reach_auxPort hab (classify c) _

end RemovePair

open RemovePair in
/-- Cutting out an active pair and plugging it back in gives the same net, up to wires. -/
noncomputable def wireIsoPlugRemovePair {N : Net S ι} {a b : N.Agent} (h : N.IsActivePairW a b) :
    WireIso N ((N.removePair a b h.1).plug (activePair (N.label a) (N.label b))) where
  agent := agentEquiv h.1
  iface := .refl ι
  label_agent := label_agentEquiv h.1
  partner_map {x y} hxy := by
    change (plugged h.1).Partner (tportMap h.1 x) (tportMap h.1 y)
    by_cases hxa : x = .pri a
    · subst hxa
      obtain rfl := hxy.unique h.2
      change (plugged h.1).Partner (.pri (classify a)) (.pri (classify b))
      rw [classify_a, classify_b h.1]
      exact (isActivePair_plug_activePair _).isActivePairW.2
    by_cases hxb : x = .pri b
    · subst hxb
      obtain rfl := hxy.unique h.2.symm
      change (plugged h.1).Partner (.pri (classify b)) (.pri (classify a))
      rw [classify_a, classify_b h.1]
      exact (isActivePair_plug_activePair _).symm.isActivePairW.2
    have hya : y ≠ .pri a := by
      rintro rfl
      exact hxb (hxy.symm.unique h.2)
    have hyb : y ≠ .pri b := by
      rintro rfl
      exact hxa (hxy.symm.unique h.2.symm)
    have h1 := reflTransGen_step_reverse (reach_toPlug h.1 x hxa hxb)
    rw [link_toPlug] at h1
    exact h1.trans ((reach_toPlug_of_reach h.1 hxy).trans (reach_toPlug h.1 y hya hyb))

/-- Every active pair up to wires can be cut out of its net: `N` is, up to wires, the active
pair plugged into the context `N.removePair a b`. -/
theorem equiv_plug_removePair {N : Net S ι} {a b : N.Agent} (h : N.IsActivePairW a b) :
    N ≈ (N.removePair a b h.1).plug (activePair (N.label a) (N.label b)) :=
  (wireIsoPlugRemovePair h).equiv

end Net

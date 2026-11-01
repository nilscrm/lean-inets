module

public import LeanInets.Connect

/-!
# Isomorphism up to wires

Two nets are *isomorphic up to wires* if there is a label-preserving bijection between their
agents whose induced map of terminal ports preserves and reflects `Connected`. Wires
themselves are ignored, so chains of wires, the orientation of wires and closed loops of
wires do not matter. This is the equivalence `≈` on nets.

Since two distinct terminal ports are connected iff they are partners, it suffices to show
that partners are mapped to partners (`WireIso.ofPartner`).

Isomorphic nets are isomorphic up to wires, and reindexing and gluing respect `≈`. For gluing,
the walk from a terminal port of the glued net alternates between walks in the two parts,
crossing the glued interface in between (`GlueChain`).
-/

@[expose] public section

namespace Net

variable {S : Signature} {ι : Type}

/-- An isomorphism up to wires between nets `N` and `M` with the same interface: a
label-preserving bijection of agents whose induced map of terminal ports preserves and
reflects connectedness. -/
structure WireIso (N M : Net S ι) where
  /-- The bijection on agents. -/
  agent : N.Agent ≃ M.Agent
  label_agent : ∀ a, M.label (agent a) = N.label a
  connected_iff : ∀ x y : N.TPort,
    M.Connected (M.tport (x.map agent label_agent id id))
      (M.tport (y.map agent label_agent id id)) ↔ N.Connected (N.tport x) (N.tport y)

namespace WireIso

variable {N M K : Net S ι}

/-- To build an isomorphism up to wires, it suffices to show that partners are mapped to
partners. -/
def ofPartner (agent : N.Agent ≃ M.Agent) (label_agent : ∀ a, M.label (agent a) = N.label a)
    (partner_map : ∀ x y, N.Partner x y →
      M.Partner (x.map agent label_agent id id) (y.map agent label_agent id id)) :
    WireIso N M where
  agent := agent
  label_agent := label_agent
  connected_iff x y := by
    have hinj : Function.Injective fun z : N.TPort => z.map agent label_agent id id :=
      Port.map_injective _ _ _ _ agent.injective Function.injective_id Function.injective_id
    rw [connected_tport_iff, connected_tport_iff, hinj.eq_iff]
    exact or_congr_right ⟨partner_reflect _ hinj partner_map, partner_map x y⟩

/-- The bijection on terminal ports induced by an isomorphism up to wires. -/
def port (e : WireIso N M) : N.TPort ≃ M.TPort :=
  Port.mapEquiv e.agent e.label_agent (.refl Empty) (.refl ι)

variable (e : WireIso N M)

@[simp] theorem port_free (i : ι) : e.port (.free i) = .free i := rfl

theorem connected_port_iff {x y : N.TPort} :
    M.Connected (M.tport (e.port x)) (M.tport (e.port y)) ↔
      N.Connected (N.tport x) (N.tport y) :=
  e.connected_iff x y

/-- Isomorphisms up to wires map partners to partners. -/
theorem partner_port {x y : N.TPort} (h : N.Partner x y) : M.Partner (e.port x) (e.port y) := by
  rcases connected_tport_iff.mp (e.connected_port_iff.mpr h.connected) with hxy | hxy
  · obtain rfl := e.port.injective hxy
    obtain ⟨z, hz⟩ := Partner.exists (e.port x)
    obtain ⟨w, rfl⟩ := e.port.surjective z
    rcases connected_tport_iff.mp (e.connected_port_iff.mp hz.connected) with rfl | hw
    · exact hz
    · rwa [← h.unique hw] at hz
  · exact hxy

theorem partner_port_iff {x y : N.TPort} : M.Partner (e.port x) (e.port y) ↔ N.Partner x y :=
  ⟨partner_reflect e.port e.port.injective fun _ _ => e.partner_port, e.partner_port⟩

/-- The identity. -/
@[refl] protected def refl (N : Net S ι) : WireIso N N :=
  .ofPartner (.refl _) (fun _ => rfl) fun x y h => by simpa using h

/-- The inverse. -/
@[symm] protected def symm : WireIso M N :=
  .ofPartner e.agent.symm (fun a => by rw [← e.label_agent, e.agent.apply_symm_apply])
    fun x y h => by
      change N.Partner (e.port.symm x) (e.port.symm y)
      rw [← e.partner_port_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact h

/-- The composition. -/
@[trans] protected def trans (e' : WireIso M K) : WireIso N K :=
  .ofPartner (e.agent.trans e'.agent) (fun a => (e'.label_agent _).trans (e.label_agent a))
    fun x y h => by
      have hp (z : N.TPort) : z.map (e.agent.trans e'.agent)
          (fun a => (e'.label_agent _).trans (e.label_agent a)) id id = e'.port (e.port z) := by
        cases z <;> rfl
      rw [hp, hp]
      exact e'.partner_port (e.partner_port h)

end WireIso

/-! ### Equivalence -/

/-- Nets are equivalent if they are isomorphic up to wires. -/
instance setoid (S : Signature) (ι : Type) : Setoid (Net S ι) where
  r N M := Nonempty (WireIso N M)
  iseqv := ⟨fun N => ⟨.refl N⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩

theorem equiv_def {N M : Net S ι} : N ≈ M ↔ Nonempty (WireIso N M) := Iff.rfl

theorem WireIso.equiv {N M : Net S ι} (e : WireIso N M) : N ≈ M := ⟨e⟩

/-! ### Isomorphisms are isomorphisms up to wires -/

namespace Iso

variable {N M : Net S ι} (e : Iso N M)

theorem port_tport (x : N.TPort) :
    e.port (N.tport x) = M.tport (x.map e.agent e.label_agent id id) := by
  rcases x with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl

theorem step_port {p q : N.Port} (h : N.Step p q) : M.Step (e.port p) (e.port q) := by
  obtain ⟨w, s, rfl, rfl⟩ := h.eq
  rw [← link_port]
  exact step_wire _ _

/-- An isomorphism is an isomorphism up to wires. -/
def wireIso : WireIso N M :=
  .ofPartner e.agent e.label_agent fun x y h => by
    have := reflTransGen_map e.port (fun _ _ => e.step_port) h
    rwa [← link_port, port_tport, port_tport] at this

theorem equiv (e : Iso N M) : N ≈ M := e.wireIso.equiv

end Iso

theorem Isomorphic.equiv {N M : Net S ι} : N.Isomorphic M → N ≈ M
  | ⟨e⟩ => e.equiv

/-! ### Reindexing respects equivalence -/

section reindex

variable {ι' : Type} (σ : ι ≃ ι') (N : Net S ι)

/-- The terminal ports of `N`, with the interface renamed along `σ`. -/
def reindexTPort : N.TPort ≃ (N.reindex σ).TPort :=
  Port.mapEquiv (.refl _) (fun _ => rfl) (.refl _) σ

theorem reindexPort_tport (x : N.TPort) :
    N.reindexPort σ (N.tport x) = (N.reindex σ).tport (N.reindexTPort σ x) := by
  rcases x with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl

theorem step_reindex {p q : N.Port} (h : N.Step p q) :
    (N.reindex σ).Step (N.reindexPort σ p) (N.reindexPort σ q) := by
  obtain ⟨w, s, rfl, rfl⟩ := h.eq
  rw [← reindex_link]
  exact step_wire (N := N.reindex σ) w s

theorem partner_reindex {x y : N.TPort} (h : N.Partner x y) :
    (N.reindex σ).Partner (N.reindexTPort σ x) (N.reindexTPort σ y) := by
  have := reflTransGen_map (M := N.reindex σ) (N.reindexPort σ) (fun _ _ h => step_reindex σ N h) h
  rwa [← reindex_link, reindexPort_tport, reindexPort_tport] at this

theorem partner_reindex_iff {x y : N.TPort} :
    (N.reindex σ).Partner (N.reindexTPort σ x) (N.reindexTPort σ y) ↔ N.Partner x y :=
  ⟨partner_reflect _ (N.reindexTPort σ).injective fun _ _ => partner_reindex σ N,
    partner_reindex σ N⟩

variable {N} {M : Net S ι}

/-- Reindexing respects isomorphisms up to wires. -/
def WireIso.reindex (e : WireIso N M) : WireIso (N.reindex σ) (M.reindex σ) :=
  .ofPartner e.agent e.label_agent fun x y h => by
    obtain ⟨x, rfl⟩ := (N.reindexTPort σ).surjective x
    obtain ⟨y, rfl⟩ := (N.reindexTPort σ).surjective y
    have hp (z : N.TPort) : (N.reindexTPort σ z).map (label' := M.label) e.agent e.label_agent
        id id = M.reindexTPort σ (e.port z) := by
      rcases z with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl
    rw [hp, hp, partner_reindex_iff]
    exact e.partner_port ((partner_reindex_iff σ N).mp h)

theorem reindex_equiv {N M : Net S ι} (h : N ≈ M) : N.reindex σ ≈ M.reindex σ :=
  let ⟨e⟩ := h; (e.reindex σ).equiv

end reindex

/-! ### Gluing respects equivalence -/

section glue

variable {κ ι' : Type} (N : Net S (ι ⊕ κ)) (M : Net S (κ ⊕ ι'))

namespace Glue

/-- The terminal ports of `N` that are not glued. -/
def liftLT (b : _root_.Port N.label Empty ι) : N.TPort :=
  b.map (label := N.label) id (fun _ => rfl) id Sum.inl

/-- The terminal ports of `M` that are not glued. -/
def liftRT (b : _root_.Port M.label Empty ι') : M.TPort :=
  b.map (label := M.label) id (fun _ => rfl) id Sum.inr

/-- The terminal ports of the glued net coming from `N`. -/
def embLT (b : _root_.Port N.label Empty ι) : (N.glue M).TPort :=
  b.map (label := N.label) Sum.inl (fun _ => rfl) id Sum.inl

/-- The terminal ports of the glued net coming from `M`. -/
def embRT (b : _root_.Port M.label Empty ι') : (N.glue M).TPort :=
  b.map (label := M.label) Sum.inr (fun _ => rfl) id Sum.inr

theorem tport_embLT (b : _root_.Port N.label Empty ι) :
    (N.glue M).tport (embLT N M b) = Glue.inl N M (N.tport (liftLT N b)) := by
  rcases b with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl

theorem tport_embRT (b : _root_.Port M.label Empty ι') :
    (N.glue M).tport (embRT N M b) = Glue.inr N M (M.tport (liftRT M b)) := by
  rcases b with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl

/-- Every terminal port of the glued net comes from a terminal port of `N` or of `M` that is
not glued. -/
theorem cases_tport (x : (N.glue M).TPort) :
    (∃ b, x = embLT N M b) ∨ ∃ b, x = embRT N M b := by
  rcases x with (i | j) | (a | b) | ⟨a | b, k⟩ | ⟨⟨⟩, _⟩
  · exact .inl ⟨.free i, rfl⟩
  · exact .inr ⟨.free j, rfl⟩
  · exact .inl ⟨.pri a, rfl⟩
  · exact .inr ⟨.pri b, rfl⟩
  · exact .inl ⟨.aux a k, rfl⟩
  · exact .inr ⟨.aux b k, rfl⟩

theorem step_inl {p q : N.Port} (h : N.Step p q) :
    (N.glue M).Step (Glue.inl N M p) (Glue.inl N M q) := by
  obtain ⟨w, s, rfl, rfl⟩ := h.eq
  exact step_wire (N := N.glue M) (.inl w) s

theorem step_inr {p q : M.Port} (h : M.Step p q) :
    (N.glue M).Step (Glue.inr N M p) (Glue.inr N M q) := by
  obtain ⟨w, s, rfl, rfl⟩ := h.eq
  exact step_wire (N := N.glue M) (.inr w) s

theorem step_inl_of_isEntity {p : N.Port} (hp : p.IsEntity) {c : (N.glue M).Port}
    (h : (N.glue M).Step (Glue.inl N M p) c) : ∃ q, N.Step p q ∧ c = Glue.inl N M q := by
  rcases p with _ | _ | _ | ⟨w, s⟩
  · exact absurd hp (Port.not_isEntity_free _)
  · exact h.elim
  · exact h.elim
  · exact ⟨_, rfl, h⟩

theorem step_inr_of_isEntity {p : M.Port} (hp : p.IsEntity) {c : (N.glue M).Port}
    (h : (N.glue M).Step (Glue.inr N M p) c) : ∃ q, M.Step p q ∧ c = Glue.inr N M q := by
  rcases p with _ | _ | _ | ⟨w, s⟩
  · exact absurd hp (Port.not_isEntity_free _)
  · exact h.elim
  · exact h.elim
  · exact ⟨_, rfl, h⟩

end Glue

open Glue

/-- The walk from a terminal port of the glued net, decomposed into walks in `N` and in `M`.
`GlueChain (.inl x) y` says that the walk from the terminal port `x` of `N` reaches `y`,
crossing the glued interface any number of times. -/
inductive GlueChain : N.TPort ⊕ M.TPort → (N.glue M).TPort → Prop
  /-- The walk reaches a terminal port of `N` that is not glued. -/
  | stopL {x : N.TPort} {b} : N.Partner x (liftLT N b) → GlueChain (.inl x) (embLT N M b)
  /-- The walk reaches a terminal port of `M` that is not glued. -/
  | stopR {x : M.TPort} {b} : M.Partner x (liftRT M b) → GlueChain (.inr x) (embRT N M b)
  /-- The walk reaches the glued port `k` of `N` and continues in `M`. -/
  | crossL {x : N.TPort} {k : κ} {y} : N.Partner x (.free (.inr k)) →
      GlueChain (.inr (.free (.inl k))) y → GlueChain (.inl x) y
  /-- The walk reaches the glued port `k` of `M` and continues in `N`. -/
  | crossR {x : M.TPort} {k : κ} {y} : M.Partner x (.free (.inl k)) →
      GlueChain (.inl (.free (.inr k))) y → GlueChain (.inr x) y

/-- The starting point of a `GlueChain`, as a port of the glued net. -/
def gluePos : N.TPort ⊕ M.TPort → (N.glue M).Port
  | .inl x => Glue.inl N M (N.tport x)
  | .inr x => Glue.inr N M (M.tport x)

variable {N M}

/-- A `GlueChain` is a walk in the glued net. -/
theorem GlueChain.sound {z y} (h : GlueChain N M z y) :
    Relation.ReflTransGen (N.glue M).Step ((N.glue M).link (gluePos N M z))
      ((N.glue M).tport y) := by
  induction h with
  | @stopL x b h =>
    rw [gluePos, glue_link_inl, tport_embLT]
    exact reflTransGen_map _ (fun _ _ => step_inl N M) h
  | @stopR x b h =>
    rw [gluePos, glue_link_inr, tport_embRT]
    exact reflTransGen_map _ (fun _ _ => step_inr N M) h
  | @crossL x k y h _ ih =>
    rw [gluePos, glue_link_inl]
    refine (reflTransGen_map _ (fun _ _ => step_inl N M) h).trans ?_
    rw [gluePos, glue_link_inr, tport_free, ← Glue.inl_free_inr] at ih
    exact ih
  | @crossR x k y h _ ih =>
    rw [gluePos, glue_link_inr]
    refine (reflTransGen_map _ (fun _ _ => step_inr N M) h).trans ?_
    rw [gluePos, glue_link_inl, tport_free, ← Glue.inr_free_inl] at ih
    exact ih

/-- The end of a walk at an entity port of `N`. -/
theorem GlueChain.of_end_inl {x : N.TPort} {a : N.Port} {y : (N.glue M).TPort}
    (hpre : Relation.ReflTransGen N.Step (N.link (N.tport x)) a) (ha : a.IsEntity)
    (hy : (N.glue M).tport y = Glue.inl N M a) : GlueChain N M (.inl x) y := by
  rcases a with _ | a | ⟨a, k⟩ | ⟨w, s⟩
  · exact absurd ha (Port.not_isEntity_free _)
  · obtain rfl : y = embLT N M (.pri a) := tport_injective hy
    exact .stopL hpre
  · obtain rfl : y = embLT N M (.aux a k) := tport_injective hy
    exact .stopL hpre
  · exact absurd hy (tport_ne_wire _ _ _)

/-- The end of a walk at an entity port of `M`. -/
theorem GlueChain.of_end_inr {x : M.TPort} {b : M.Port} {y : (N.glue M).TPort}
    (hpre : Relation.ReflTransGen M.Step (M.link (M.tport x)) b) (hb : b.IsEntity)
    (hy : (N.glue M).tport y = Glue.inr N M b) : GlueChain N M (.inr x) y := by
  rcases b with _ | b | ⟨b, k⟩ | ⟨w, s⟩
  · exact absurd hb (Port.not_isEntity_free _)
  · obtain rfl : y = embRT N M (.pri b) := tport_injective hy
    exact .stopR hpre
  · obtain rfl : y = embRT N M (.aux b k) := tport_injective hy
    exact .stopR hpre
  · exact absurd hy (tport_ne_wire _ _ _)

/-- Every walk in the glued net that ends at a terminal port decomposes into a `GlueChain`.
The walk may start in the middle of a walk in `N` or in `M`, given by `hpre`. -/
theorem GlueChain.complete {u : (N.glue M).Port} {y : (N.glue M).TPort}
    (h : Relation.ReflTransGen (N.glue M).Step u ((N.glue M).tport y)) :
    (∀ x a, Relation.ReflTransGen N.Step (N.link (N.tport x)) a → u = Glue.inl N M a →
      GlueChain N M (.inl x) y) ∧
    (∀ x b, Relation.ReflTransGen M.Step (M.link (M.tport x)) b → u = Glue.inr N M b →
      GlueChain N M (.inr x) y) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    constructor
    · rintro x ((i | k) | a) hpre hu
      · obtain rfl : y = embLT N M (.free i) := tport_injective hu
        exact .stopL hpre
      · rw [Glue.inl_free_inr] at hu
        exact .crossL hpre (.of_end_inr .refl (M.link_free _) hu)
      all_goals exact .of_end_inl hpre trivial hu
    · rintro x ((k | j) | b) hpre hu
      · rw [Glue.inr_free_inl] at hu
        exact .crossR hpre (.of_end_inl .refl (N.link_free _) hu)
      · obtain rfl : y = embRT N M (.free j) := tport_injective hu
        exact .stopR hpre
      all_goals exact .of_end_inr hpre trivial hu
  | @head u c hstep _ ih =>
    have hL (x : N.TPort) (a : N.Port) (hpre : Relation.ReflTransGen N.Step (N.link (N.tport x)) a)
        (ha : a.IsEntity) (hu : u = Glue.inl N M a) : GlueChain N M (.inl x) y := by
      subst hu
      obtain ⟨q, hq, rfl⟩ := step_inl_of_isEntity N M ha hstep
      exact ih.1 x q (hpre.tail hq) rfl
    have hR (x : M.TPort) (b : M.Port) (hpre : Relation.ReflTransGen M.Step (M.link (M.tport x)) b)
        (hb : b.IsEntity) (hu : u = Glue.inr N M b) : GlueChain N M (.inr x) y := by
      subst hu
      obtain ⟨q, hq, rfl⟩ := step_inr_of_isEntity N M hb hstep
      exact ih.2 x q (hpre.tail hq) rfl
    constructor
    · rintro x ((i | k) | a) hpre hu
      · subst hu
        exact hstep.elim
      · rw [Glue.inl_free_inr] at hu
        exact .crossL hpre (hR _ _ .refl (M.link_free _) hu)
      all_goals exact hL x _ hpre trivial hu
    · rintro x ((k | j) | b) hpre hu
      · rw [Glue.inr_free_inl] at hu
        exact .crossR hpre (hL _ _ .refl (N.link_free _) hu)
      · subst hu
        exact hstep.elim
      all_goals exact hR x _ hpre trivial hu

theorem GlueChain.of_partner_embLT {b : _root_.Port N.label Empty ι} {y : (N.glue M).TPort}
    (h : (N.glue M).Partner (embLT N M b) y) : GlueChain N M (.inl (liftLT N b)) y := by
  rw [Partner, tport_embLT, glue_link_inl] at h
  exact (GlueChain.complete h).1 _ _ .refl rfl

theorem GlueChain.of_partner_embRT {b : _root_.Port M.label Empty ι'} {y : (N.glue M).TPort}
    (h : (N.glue M).Partner (embRT N M b) y) : GlueChain N M (.inr (liftRT M b)) y := by
  rw [Partner, tport_embRT, glue_link_inr] at h
  exact (GlueChain.complete h).2 _ _ .refl rfl

theorem GlueChain.partner_embLT {b : _root_.Port N.label Empty ι} {y : (N.glue M).TPort}
    (h : GlueChain N M (.inl (liftLT N b)) y) : (N.glue M).Partner (embLT N M b) y := by
  rw [Partner, tport_embLT]
  exact h.sound

theorem GlueChain.partner_embRT {b : _root_.Port M.label Empty ι'} {y : (N.glue M).TPort}
    (h : GlueChain N M (.inr (liftRT M b)) y) : (N.glue M).Partner (embRT N M b) y := by
  rw [Partner, tport_embRT]
  exact h.sound

/-! #### Transporting chains along isomorphisms up to wires -/

variable {N' : Net S (ι ⊕ κ)} {M' : Net S (κ ⊕ ι')} (e : WireIso N N') (e' : WireIso M M')

theorem WireIso.glue_label_agent (a : (N.glue M).Agent) :
    (N'.glue M').label (e.agent.sumCongr e'.agent a) = (N.glue M).label a := by
  rcases a with a | b
  exacts [e.label_agent a, e'.label_agent b]

/-- The map of terminal ports underlying `WireIso.glue`. -/
abbrev WireIso.glueTPort : (N.glue M).TPort → (N'.glue M').TPort :=
  Port.map (e.agent.sumCongr e'.agent) (e.glue_label_agent e') id id

theorem WireIso.port_liftLT (b : _root_.Port N.label Empty ι) :
    e.port (liftLT N b) = liftLT N' (b.map e.agent e.label_agent id id) := by
  rcases b with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl

theorem WireIso.port_liftRT (b : _root_.Port M.label Empty ι') :
    e'.port (liftRT M b) = liftRT M' (b.map e'.agent e'.label_agent id id) := by
  rcases b with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl

theorem WireIso.glueTPort_embLT (b : _root_.Port N.label Empty ι) :
    e.glueTPort e' (embLT N M b) = embLT N' M' (b.map e.agent e.label_agent id id) := by
  rcases b with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl

theorem WireIso.glueTPort_embRT (b : _root_.Port M.label Empty ι') :
    e.glueTPort e' (embRT N M b) = embRT N' M' (b.map e'.agent e'.label_agent id id) := by
  rcases b with _ | _ | _ | ⟨⟨⟩, _⟩ <;> rfl

theorem GlueChain.map {z y} (h : GlueChain N M z y) :
    GlueChain N' M' (Sum.map e.port e'.port z) (e.glueTPort e' y) := by
  induction h with
  | @stopL x b h =>
    rw [WireIso.glueTPort_embLT]
    have := e.partner_port h
    rw [WireIso.port_liftLT] at this
    exact .stopL this
  | @stopR x b h =>
    rw [WireIso.glueTPort_embRT]
    have := e'.partner_port h
    rw [WireIso.port_liftRT] at this
    exact .stopR this
  | crossL h _ ih => exact .crossL (e.partner_port h) ih
  | crossR h _ ih => exact .crossR (e'.partner_port h) ih

/-- Gluing respects isomorphisms up to wires. -/
def WireIso.glue : WireIso (N.glue M) (N'.glue M') :=
  .ofPartner (e.agent.sumCongr e'.agent) (e.glue_label_agent e') fun x y h => by
    change (N'.glue M').Partner (e.glueTPort e' x) (e.glueTPort e' y)
    rcases cases_tport N M x with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have := (GlueChain.of_partner_embLT h).map e e'
      rw [Sum.map_inl, WireIso.port_liftLT] at this
      rw [WireIso.glueTPort_embLT]
      exact this.partner_embLT
    · have := (GlueChain.of_partner_embRT h).map e e'
      rw [Sum.map_inr, WireIso.port_liftRT] at this
      rw [WireIso.glueTPort_embRT]
      exact this.partner_embRT

/-- Gluing respects equivalence. -/
theorem glue_equiv {N N' : Net S (ι ⊕ κ)} {M M' : Net S (κ ⊕ ι')} (hN : N ≈ N') (hM : M ≈ M') :
    N.glue M ≈ N'.glue M' :=
  let ⟨e⟩ := hN; let ⟨e'⟩ := hM; (e.glue e').equiv

end glue

end Net

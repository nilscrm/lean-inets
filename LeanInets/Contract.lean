module

public import LeanInets.Glue
public import Mathlib.Logic.Relation

/-!
# Wire contraction and equivalence of nets

Contracting a wire `w` removes it and links its two neighbours directly. This is allowed
unless both ends of `w` are free ports, since free ports may not be linked to each other.
A wire whose two ends are linked to each other (a vicious circle) simply disappears.

Rather than only working with the contracted net `N.contract w h`, we describe contractions
relationally: a `Contraction N M` identifies `M` with `N` minus one wire, up to isomorphism.
The wiring of `M` is that of `N`, except that whenever a link of `N` reaches an end of the
removed wire, `skip` jumps over it to the port at its other end.

Nets are *equivalent*, `N ≈ M`, if they are related by the equivalence closure of
isomorphism and contraction. Reindexing and gluing respect `≈`.
-/

@[expose] public section

namespace Net

variable {S : Signature} {ι : Type}

/-! ### Skipping over a wire -/

section skip

variable (N : Net S ι) (w : N.Wire)

/-- A port avoids the wire `w` if it is not one of its two ends. -/
def Avoids (p : N.Port) : Prop := ∀ s, p ≠ .wire w s

open Classical in
/-- Skip over the wire `w`: an end of `w` is replaced by the port linked to the other end of
`w`; all other ports are left unchanged. -/
noncomputable def skip : N.Port → N.Port
  | .free i => .free i
  | .pri a => .pri a
  | .aux a k => .aux a k
  | .wire v s => if v = w then N.link (.wire w s.flip) else .wire v s

variable {N w}

@[simp] theorem avoids_free (i : ι) : N.Avoids w (.free i) := fun _ => nofun
@[simp] theorem avoids_pri (a : N.Agent) : N.Avoids w (.pri a) := fun _ => nofun
@[simp] theorem avoids_aux (a : N.Agent) (k) : N.Avoids w (.aux a k) := fun _ => nofun
@[simp] theorem avoids_wire {v : N.Wire} {s : Side} : N.Avoids w (.wire v s) ↔ v ≠ w := by
  refine ⟨fun h e => h s (e ▸ rfl), fun h s' e => h ?_⟩
  cases e
  rfl

@[simp] theorem skip_free (i : ι) : N.skip w (.free i) = .free i := rfl
@[simp] theorem skip_pri (a : N.Agent) : N.skip w (.pri a) = .pri a := rfl
@[simp] theorem skip_aux (a : N.Agent) (k) : N.skip w (.aux a k) = .aux a k := rfl
@[simp] theorem skip_wire_self (s : Side) : N.skip w (.wire w s) = N.link (.wire w s.flip) := by
  simp [skip]

theorem skip_wire_of_ne {v : N.Wire} (h : v ≠ w) (s : Side) :
    N.skip w (.wire v s) = .wire v s := by
  simp [skip, h]

theorem skip_of_avoids {p : N.Port} (hp : N.Avoids w p) : N.skip w p = p := by
  cases p with
  | wire v s => exact skip_wire_of_ne (avoids_wire.mp hp) s
  | _ => rfl

theorem not_avoids {p : N.Port} (hp : ¬ N.Avoids w p) : ∃ s, p = .wire w s := by
  simpa [Avoids] using hp

/-- If one end of `w` is linked to an end of `w`, it is linked to the other end. -/
theorem eq_flip_of_link_wire {s s' : Side} (h : N.link (.wire w s) = .wire w s') :
    s' = s.flip := by
  cases s <;> cases s' <;> first | rfl | exact absurd h (N.link_ne _)

/-- Skipping after following a link never lands on the skipped wire. -/
theorem avoids_skip_link {q : N.Port} (hq : N.Avoids w q) :
    N.Avoids w (N.skip w (N.link q)) := by
  by_cases hl : N.Avoids w (N.link q)
  · rwa [skip_of_avoids hl]
  obtain ⟨s, hs⟩ := not_avoids hl
  rw [hs, skip_wire_self]
  intro s' h
  cases eq_flip_of_link_wire h
  rw [Side.flip_flip, N.link_eq_comm] at h
  exact hq s.flip ((N.link_eq_comm.mp hs).symm.trans h)

/-- Following a link and skipping over `w` is an involution on the ports avoiding `w`. -/
theorem skip_link_skip_link {q : N.Port} (hq : N.Avoids w q) :
    N.skip w (N.link (N.skip w (N.link q))) = q := by
  by_cases hl : N.Avoids w (N.link q)
  · rw [skip_of_avoids hl, N.link_link, skip_of_avoids hq]
  obtain ⟨s, hs⟩ := not_avoids hl
  rw [hs, skip_wire_self, N.link_link, skip_wire_self, Side.flip_flip, ← hs, N.link_link]

theorem skip_link_ne (q : N.Port) : N.skip w (N.link q) ≠ q := by
  by_cases hl : N.Avoids w (N.link q)
  · rw [skip_of_avoids hl]
    exact N.link_ne q
  obtain ⟨s, hs⟩ := not_avoids hl
  rw [hs, skip_wire_self]
  intro h
  rw [N.link_eq_comm, hs] at h
  exact s.flip_ne (Port.wire.inj h).2.symm

/-- Skipping before following a link makes no difference after skipping again, as long as
the port or its partner avoids `w`. -/
theorem skip_link_skip {x : N.Port} (h : N.Avoids w x ∨ N.Avoids w (N.link x)) :
    N.skip w (N.link (N.skip w x)) = N.skip w (N.link x) := by
  by_cases hx : N.Avoids w x
  · rw [skip_of_avoids hx]
  have hl := h.resolve_left hx
  obtain ⟨s, rfl⟩ := not_avoids hx
  rw [skip_wire_self, N.link_link, skip_wire_self, Side.flip_flip, skip_of_avoids hl]

end skip

/-! ### Contracting a wire -/

section contract

variable (N : Net S ι) (w : N.Wire)

/-- The ports of `N` with the wire `w` removed. -/
abbrev ContractPort := _root_.Port N.label {v : N.Wire // v ≠ w} ι

namespace ContractPort

variable {N w}

/-- A port of the contracted net as a port of `N`. -/
def emb (p : N.ContractPort w) : N.Port := p.map id (fun _ => rfl) Subtype.val id

/-- A port of `N` that avoids `w`, as a port of the contracted net. -/
def res : (q : N.Port) → N.Avoids w q → N.ContractPort w
  | .free i, _ => .free i
  | .pri a, _ => .pri a
  | .aux a k, _ => .aux a k
  | .wire v s, h => .wire ⟨v, avoids_wire.mp h⟩ s

theorem avoids_emb (p : N.ContractPort w) : N.Avoids w p.emb := by
  cases p with
  | wire v s => simpa [emb] using v.2
  | _ => simp [emb]

@[simp] theorem emb_res (q : N.Port) (h : N.Avoids w q) : (res q h).emb = q := by
  cases q <;> rfl

theorem emb_injective : Function.Injective (emb (N := N) (w := w)) :=
  Port.map_injective id (fun _ => rfl) Subtype.val id Function.injective_id
    Subtype.val_injective Function.injective_id

theorem isEntity_res (q : N.Port) (h : N.Avoids w q) : (res q h).IsEntity ↔ q.IsEntity := by
  cases q <;> rfl

end ContractPort

open ContractPort

variable {N w} in
theorem isEntity_skip_link_free (h : (N.link (.wire w .l)).IsEntity ∨
    (N.link (.wire w .r)).IsEntity) (i : ι) : (N.skip w (N.link (.free i))).IsEntity := by
  by_cases hl : N.Avoids w (N.link (.free i))
  · rw [skip_of_avoids hl]
    exact N.link_free i
  obtain ⟨s, hs⟩ := not_avoids hl
  have hs' : N.link (.wire w s) = .free i := N.link_eq_comm.mp hs
  rw [hs, skip_wire_self]
  cases s
  · exact h.resolve_left (by rw [hs']; exact id)
  · exact h.resolve_right (by rw [hs']; exact id)

/-- Contract the wire `w`, linking its two neighbours directly. This requires that not both
ends of `w` are free ports. -/
noncomputable def contract
    (h : (N.link (.wire w .l)).IsEntity ∨ (N.link (.wire w .r)).IsEntity) : Net S ι where
  Agent := N.Agent
  Wire := {v : N.Wire // v ≠ w}
  wireFintype := by classical infer_instance
  label := N.label
  link p := res (N.skip w (N.link (emb p))) (avoids_skip_link (avoids_emb p))
  link_link p := emb_injective (by simp only [emb_res, skip_link_skip_link (avoids_emb p)])
  link_ne p e := skip_link_ne (w := w) (emb p) (by simpa using congrArg emb e)
  link_free i := (isEntity_res _ _).mpr (isEntity_skip_link_free h i)

end contract

/-! ### Contractions -/

/-- A contraction of `N` to `M`: `M` is, up to isomorphism, `N` with the wire `removed`
contracted. Ports of `M` correspond to the ports of `N` avoiding `removed`, and the links of
`M` are those of `N`, skipping over `removed`. -/
structure Contraction (N M : Net S ι) where
  /-- The wire that is contracted. -/
  removed : N.Wire
  /-- The bijection on agents. -/
  agent : M.Agent ≃ N.Agent
  /-- The bijection between the wires of `M` and the remaining wires of `N`. -/
  wire : M.Wire ≃ {v : N.Wire // v ≠ removed}
  label_agent : ∀ a, N.label (agent a) = M.label a
  link_map : ∀ p, N.skip removed (N.link (p.map agent label_agent (fun v => (wire v).1) id)) =
    (M.link p).map agent label_agent (fun v => (wire v).1) id

namespace Contraction

variable {N M : Net S ι} (c : Contraction N M)

/-- The ports of `M` as ports of `N`. -/
def port (p : M.Port) : N.Port := p.map c.agent c.label_agent (fun v => (c.wire v).1) id

@[simp] theorem port_free (i : ι) : c.port (.free i) = .free i := rfl

theorem link_port (p : M.Port) : N.skip c.removed (N.link (c.port p)) = c.port (M.link p) :=
  c.link_map p

theorem avoids_port (p : M.Port) : N.Avoids c.removed (c.port p) := by
  cases p with
  | wire v s => exact avoids_wire.mpr (c.wire v).2
  | _ => simp [port]

end Contraction

open ContractPort in
/-- Contracting a wire is a contraction. -/
noncomputable def contraction (N : Net S ι) (w : N.Wire)
    (h : (N.link (.wire w .l)).IsEntity ∨ (N.link (.wire w .r)).IsEntity) :
    Contraction N (N.contract w h) where
  removed := w
  agent := Equiv.refl N.Agent
  wire := Equiv.refl {v : N.Wire // v ≠ w}
  label_agent _ := rfl
  link_map p :=
    (emb_res (N.skip w (N.link (emb p))) (avoids_skip_link (avoids_emb (N := N) (w := w) p))).symm

/-! ### Equivalence -/

/-- One generating step of the equivalence of nets: an isomorphism or a contraction. -/
def EquivStep (N M : Net S ι) : Prop := N.Isomorphic M ∨ Nonempty (Contraction N M)

/-- Equivalence of nets: the equivalence relation generated by isomorphism and contraction
of wires. -/
instance setoid (S : Signature) (ι : Type) : Setoid (Net S ι) :=
  Relation.EqvGen.setoid EquivStep

theorem equiv_def {N M : Net S ι} : N ≈ M ↔ Relation.EqvGen EquivStep N M := Iff.rfl

theorem Isomorphic.equiv {N M : Net S ι} (h : N.Isomorphic M) : N ≈ M :=
  .rel _ _ (.inl h)

theorem Iso.equiv {N M : Net S ι} (e : Iso N M) : N ≈ M := Isomorphic.equiv ⟨e⟩

theorem Contraction.equiv {N M : Net S ι} (c : Contraction N M) : N ≈ M :=
  .rel _ _ (.inr ⟨c⟩)

theorem equiv_contract (N : Net S ι) (w : N.Wire)
    (h : (N.link (.wire w .l)).IsEntity ∨ (N.link (.wire w .r)).IsEntity) :
    N ≈ N.contract w h :=
  (N.contraction w h).equiv

/-- A map between nets respects `≈` if it respects isomorphisms and contractions. -/
theorem map_equiv {ι' : Type} (F : Net S ι → Net S ι')
    (hiso : ∀ {N M}, Iso N M → F N ≈ F M) (hc : ∀ {N M}, Contraction N M → F N ≈ F M)
    {N M : Net S ι} (h : N ≈ M) : F N ≈ F M := by
  induction h with
  | rel _ _ h => exact h.elim (fun ⟨e⟩ => hiso e) (fun ⟨c⟩ => hc c)
  | refl => exact Setoid.refl _
  | symm _ _ _ ih => exact Setoid.symm ih
  | trans _ _ _ _ _ ih ih' => exact Setoid.trans ih ih'

/-! ### Reindexing respects equivalence -/

section reindex

variable {ι' : Type} (σ : ι ≃ ι')

theorem skip_reindex (N : Net S ι) (w : N.Wire) (q : N.Port) :
    (N.reindex σ).skip w (N.reindexPort σ q) = N.reindexPort σ (N.skip w q) := by
  cases q with
  | wire v s =>
    by_cases hv : v = w
    · subst hv
      rw [skip_wire_self, reindexPort_wire, skip_wire_self, ← reindexPort_wire, reindex_link]
    · rw [reindexPort_wire, skip_wire_of_ne hv]
      exact skip_wire_of_ne (N := N.reindex σ) hv s
  | _ => rfl

variable {N M : Net S ι}

/-- Reindexing respects contractions. -/
def Contraction.reindex (c : Contraction N M) : Contraction (N.reindex σ) (M.reindex σ) where
  removed := c.removed
  agent := c.agent
  wire := c.wire
  label_agent := c.label_agent
  link_map p := by
    obtain ⟨q, rfl⟩ := (M.reindexPort σ).surjective p
    have h (q : M.Port) : (M.reindexPort σ q).map (label' := N.label) c.agent c.label_agent
        (fun v => (c.wire v).1) id = N.reindexPort σ (c.port q) := by
      cases q <;> rfl
    rw [h, reindex_link, skip_reindex, c.link_port, reindex_link, h]

theorem reindex_equiv (h : N ≈ M) : N.reindex σ ≈ M.reindex σ :=
  map_equiv (Net.reindex σ) (fun e => (e.reindex σ).equiv) (fun c => (c.reindex σ).equiv) h

end reindex

/-! ### Gluing respects equivalence -/

section glue

variable {κ ι' : Type}

theorem avoids_glue_inr_liftR (N : Net S (ι ⊕ κ)) (M : Net S (κ ⊕ ι')) (w : N.Wire)
    (y : _root_.Port M.label M.Wire ι') :
    (N.glue M).Avoids (.inl w) (Glue.inr N M (Glue.liftR M y)) := by
  rw [Glue.inr_liftR]
  cases y <;> intro s h <;> cases h

theorem avoids_glue_inr_of_isEntity (N : Net S (ι ⊕ κ)) (M : Net S (κ ⊕ ι')) (w : N.Wire)
    {r : M.Port} (h : r.IsEntity) : (N.glue M).Avoids (.inl w) (Glue.inr N M r) := by
  obtain ⟨y, rfl⟩ := Glue.exists_map_of_isEntity_right M h
  exact avoids_glue_inr_liftR N M w y

/-- Skipping over a wire of `N` in the glued net. -/
theorem skip_glue_inl (N : Net S (ι ⊕ κ)) (M : Net S (κ ⊕ ι')) (w : N.Wire) (q : N.Port) :
    (N.glue M).skip (.inl w) (Glue.inl N M q) = Glue.inl N M (N.skip w q) := by
  rcases q with (i | k) | a | ⟨a, j⟩ | ⟨v, s⟩
  · rfl
  · rw [skip_free, Glue.inl_free_inr,
      skip_of_avoids (avoids_glue_inr_of_isEntity N M w (M.link_free _))]
  · rfl
  · rfl
  · by_cases hv : v = w
    · subst hv
      rw [skip_wire_self]
      exact skip_wire_self (N := N.glue M) s
    · rw [skip_wire_of_ne hv]
      exact skip_wire_of_ne (N := N.glue M) (fun e => hv (Sum.inl_injective e)) s

variable {N N' : Net S (ι ⊕ κ)} (c : Contraction N N') (M : Net S (κ ⊕ ι'))

/-- The wires of `N' ⊕ M` correspond to the wires of `N ⊕ M` other than the removed one. -/
def Contraction.glueWire :
    N'.Wire ⊕ M.Wire ≃ {v : N.Wire ⊕ M.Wire // v ≠ .inl c.removed} where
  toFun
    | .inl v => ⟨.inl (c.wire v).1, fun e => (c.wire v).2 (Sum.inl_injective e)⟩
    | .inr v => ⟨.inr v, nofun⟩
  invFun
    | ⟨.inl v, h⟩ => .inl (c.wire.symm ⟨v, fun e => h (e ▸ rfl)⟩)
    | ⟨.inr v, _⟩ => .inr v
  left_inv v := by rcases v with v | v <;> simp
  right_inv v := by rcases v with ⟨v | v, h⟩ <;> simp

/-- Gluing respects contractions of the left net. -/
def Contraction.glueLeft : Contraction (N.glue M) (N'.glue M) where
  removed := .inl c.removed
  agent := c.agent.sumCongr (.refl _)
  wire := c.glueWire M
  label_agent := by rintro (a | b); exacts [c.label_agent a, rfl]
  link_map p := by
    -- The map on ports, on the images of `Glue.inl` and `Glue.inr`.
    let F : (N'.glue M).Port → (N.glue M).Port := fun p =>
      p.map (c.agent.sumCongr (.refl _)) (by rintro (a | b); exacts [c.label_agent a, rfl])
        (fun v => (c.glueWire M v).1) id
    have hr (r : M.Port) (h : r.IsEntity) : F (Glue.inr N' M r) = Glue.inr N M r := by
      cases r
      · exact absurd h (Port.not_isEntity_free _)
      all_goals rfl
    have hl (q : N'.Port) : F (Glue.inl N' M q) = Glue.inl N M (c.port q) := by
      rcases q with (i | k) | q
      · rfl
      · rw [Glue.inl_free_inr, hr _ (M.link_free _), c.port_free, Glue.inl_free_inr]
      all_goals rfl
    have hr' (q : M.Port) :
        F (Glue.inr N' M q) = (N.glue M).skip (.inl c.removed) (Glue.inr N M q) := by
      have hent (r : M.Port) (h : r.IsEntity) :
          F (Glue.inr N' M r) = (N.glue M).skip (.inl c.removed) (Glue.inr N M r) :=
        (hr r h).trans (skip_of_avoids (avoids_glue_inr_of_isEntity N M _ h)).symm
      rcases q with (k | j) | b | ⟨b, j⟩ | ⟨v, s⟩
      · rw [Glue.inr_free_inl, Glue.inr_free_inl, hl, skip_glue_inl, ← c.link_port]
        rfl
      · rfl
      exacts [hent (.pri b) trivial, hent (.aux b j) trivial, hent (.wire v s) trivial]
    change (N.glue M).skip _ ((N.glue M).link (F p)) = F ((N'.glue M).link p)
    rcases Glue.cases_glue N' M p with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · rw [← Glue.inl_liftL, hl, glue_link_inl, skip_glue_inl, c.link_port, glue_link_inl, hl]
    · rw [← Glue.inr_liftR, hr', skip_link_skip (.inl (avoids_glue_inr_liftR N M _ y)),
        glue_link_inr, glue_link_inr, hr']

theorem glue_equiv_left {M M' : Net S (ι ⊕ κ)} (h : M ≈ M') (K : Net S (κ ⊕ ι')) :
    M.glue K ≈ M'.glue K :=
  map_equiv (fun X => X.glue K) (fun e => (e.glue (.refl K)).equiv)
    (fun c => (c.glueLeft K).equiv) h

theorem glue_equiv_right (K : Net S (ι ⊕ κ)) {M M' : Net S (κ ⊕ ι')} (h : M ≈ M') :
    K.glue M ≈ K.glue M' :=
  Setoid.trans (glueComm K M).equiv <| Setoid.trans
    (reindex_equiv _ (glue_equiv_left (reindex_equiv _ h) _)) (glueComm K M').equiv.symm

/-- Gluing respects equivalence. -/
theorem glue_equiv {K K' : Net S (ι ⊕ κ)} {M M' : Net S (κ ⊕ ι')} (hK : K ≈ K')
    (hM : M ≈ M') : K.glue M ≈ K'.glue M' :=
  Setoid.trans (glue_equiv_left hK M) (glue_equiv_right K' hM)

end glue

end Net

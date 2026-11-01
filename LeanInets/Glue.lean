module

public import LeanInets.Iso

/-!
# Gluing nets

`glue N M` connects a net `N` with interface `ι ⊕ κ` to a net `M` with interface `κ ⊕ ι'`
along `κ`: the port of `N` linked to the free port `inr k` is linked directly to the port
of `M` linked to the free port `inl k`. Since free ports are only ever linked to entity
ports, no chains of free ports have to be followed. The result has interface `ι ⊕ ι'`.

Gluing is associative up to isomorphism, and commutative up to isomorphism after swapping
the interfaces with `reindex`. Its unit, the net of wires `κ ⊕ κ`, is a unit only up to wire
contraction, so the unit laws are deferred to the equivalence `≈`.
-/

@[expose] public section

namespace Net

variable {S : Signature}

/-! ### Reindexing the interface -/

section reindex

variable {ι ι' : Type}

/-- The ports of `N`, with the interface renamed along `σ`. -/
def reindexPort (σ : ι ≃ ι') (N : Net S ι) : N.Port ≃ _root_.Port N.label N.Wire ι' :=
  Port.mapEquiv (.refl _) (fun _ => rfl) (.refl _) σ

/-- Rename the free ports of a net along a bijection of interfaces.

This is reducible (as is `glue`) so that the ports of the result unfold to a plain `Port`
type, which `rw` needs in order to see that lemmas about the underlying ports apply. -/
@[reducible] def reindex (σ : ι ≃ ι') (N : Net S ι) : Net S ι' where
  Agent := N.Agent
  Wire := N.Wire
  label := N.label
  link p := N.reindexPort σ (N.link ((N.reindexPort σ).symm p))
  link_link p := by simp [N.link_link]
  link_ne p h := N.link_ne _ ((Equiv.eq_symm_apply _).mpr h)
  link_free i := (Port.isEntity_map _ (fun _ => rfl) _ _ _).mpr (N.link_free (σ.symm i))

variable (σ : ι ≃ ι') (N : Net S ι)

@[simp] theorem reindexPort_free (i : ι) : N.reindexPort σ (.free i) = .free (σ i) := rfl
@[simp] theorem reindexPort_pri (a : N.Agent) : N.reindexPort σ (.pri a) = .pri a := rfl
@[simp] theorem reindexPort_aux (a : N.Agent) (k) : N.reindexPort σ (.aux a k) = .aux a k :=
  rfl
@[simp] theorem reindexPort_wire (w : N.Wire) (s : Side) :
    N.reindexPort σ (.wire w s) = .wire w s := rfl

theorem reindex_link (p : N.Port) :
    (N.reindex σ).link (N.reindexPort σ p) = N.reindexPort σ (N.link p) := by
  change N.reindexPort σ (N.link ((N.reindexPort σ).symm (N.reindexPort σ p))) = _
  rw [Equiv.symm_apply_apply]

variable {N} {M : Net S ι}

/-- Reindexing respects isomorphism. -/
def Iso.reindex (e : Iso N M) : Iso (N.reindex σ) (M.reindex σ) where
  agent := e.agent
  wire := e.wire
  label_agent := e.label_agent
  link_map p := by
    obtain ⟨q, rfl⟩ := (N.reindexPort σ).surjective p
    have h (q : N.Port) : Port.map e.agent e.label_agent e.wire id (N.reindexPort σ q) =
        M.reindexPort σ (e.port q) := by
      cases q <;> rfl
    exact (congrArg (M.reindex σ).link (h q)).trans <| (reindex_link σ M _).trans <|
      (congrArg _ (e.link_port q)).trans <| (h _).symm.trans <|
        congrArg (Port.map e.agent e.label_agent e.wire id) (reindex_link σ N q).symm

/-- Swap the two halves of an interface. -/
abbrev swap {α β : Type} (N : Net S (α ⊕ β)) : Net S (β ⊕ α) :=
  N.reindex (Equiv.sumComm _ _)

/-- The ports of `N.swap`. -/
abbrev swapPort {α β : Type} (N : Net S (α ⊕ β)) : N.Port → N.swap.Port :=
  N.reindexPort (Equiv.sumComm _ _)

theorem swap_link {α β : Type} (N : Net S (α ⊕ β)) (p : N.Port) :
    N.swap.link (N.swapPort p) = N.swapPort (N.link p) :=
  reindex_link _ N p

end reindex

/-! ### Gluing -/

section glue

variable {ι κ ι' : Type} (N : Net S (ι ⊕ κ)) (M : Net S (κ ⊕ ι'))

/-- The ports of the net obtained by gluing `N` and `M`. -/
abbrev GluePort := _root_.Port (Sum.elim N.label M.label) (N.Wire ⊕ M.Wire) (ι ⊕ ι')

namespace Glue

/-- Where a port of `N` ends up after gluing. The glued free port `inr k` is identified with
the port of `M` that is linked to `inl k`. -/
def inl : N.Port → GluePort N M
  | .free (.inl i) => .free (.inl i)
  | .free (.inr k) =>
    ((M.link (.free (.inl k))).ofEntity (M.link_free _)).map Sum.inr (fun _ => rfl) Sum.inr id
  | .pri a => .pri (.inl a)
  | .aux a j => .aux (.inl a) j
  | .wire w s => .wire (.inl w) s

/-- Where a port of `M` ends up after gluing. The glued free port `inl k` is identified with
the port of `N` that is linked to `inr k`. -/
def inr : M.Port → GluePort N M
  | .free (.inl k) =>
    ((N.link (.free (.inr k))).ofEntity (N.link_free _)).map Sum.inl (fun _ => rfl) Sum.inl id
  | .free (.inr j) => .free (.inr j)
  | .pri b => .pri (.inr b)
  | .aux b j => .aux (.inr b) j
  | .wire w s => .wire (.inr w) s

/-- The links of the glued net. -/
def link : GluePort N M → GluePort N M
  | .free (.inl i) => inl N M (N.link (.free (.inl i)))
  | .free (.inr j) => inr N M (M.link (.free (.inr j)))
  | .pri (.inl a) => inl N M (N.link (.pri a))
  | .pri (.inr b) => inr N M (M.link (.pri b))
  | .aux (.inl a) k => inl N M (N.link (.aux a k))
  | .aux (.inr b) k => inr N M (M.link (.aux b k))
  | .wire (.inl w) s => inl N M (N.link (.wire w s))
  | .wire (.inr w) s => inr N M (M.link (.wire w s))

/-! The ports of `N` that are not glued are those with interface `ι`, and similarly for
`M`. -/

/-- The ports of `N` that are not glued. -/
def liftL (x : _root_.Port N.label N.Wire ι) : N.Port :=
  x.map (label := N.label) id (fun _ => rfl) id Sum.inl

/-- The ports of `M` that are not glued. -/
def liftR (y : _root_.Port M.label M.Wire ι') : M.Port :=
  y.map (label := M.label) id (fun _ => rfl) id Sum.inr

/-- The ports of the glued net coming from `N`. -/
def embL (x : _root_.Port N.label N.Wire ι) : GluePort N M :=
  x.map (label := N.label) Sum.inl (fun _ => rfl) Sum.inl Sum.inl

/-- The ports of the glued net coming from `M`. -/
def embR (y : _root_.Port M.label M.Wire ι') : GluePort N M :=
  y.map (label := M.label) Sum.inr (fun _ => rfl) Sum.inr Sum.inr

variable {N M} in
theorem isEntity_liftL {x : _root_.Port N.label N.Wire ι} : (liftL N x).IsEntity ↔ x.IsEntity :=
  Port.isEntity_map _ (fun _ => rfl) _ _ _

variable {N M} in
theorem isEntity_liftR {y : _root_.Port M.label M.Wire ι'} : (liftR M y).IsEntity ↔ y.IsEntity :=
  Port.isEntity_map _ (fun _ => rfl) _ _ _

variable {N M} in
theorem isEntity_embL {x : _root_.Port N.label N.Wire ι} :
    (embL N M x).IsEntity ↔ x.IsEntity :=
  Port.isEntity_map _ (fun _ => rfl) _ _ _

variable {N M} in
theorem isEntity_embR {y : _root_.Port M.label M.Wire ι'} :
    (embR N M y).IsEntity ↔ y.IsEntity :=
  Port.isEntity_map _ (fun _ => rfl) _ _ _

theorem embL_injective : Function.Injective (embL N M) :=
  Port.map_injective (label := N.label) (label' := Sum.elim N.label M.label) Sum.inl
    (fun _ => rfl) Sum.inl Sum.inl Sum.inl_injective Sum.inl_injective Sum.inl_injective

theorem embR_injective : Function.Injective (embR N M) :=
  Port.map_injective (label := M.label) (label' := Sum.elim N.label M.label) Sum.inr
    (fun _ => rfl) Sum.inr Sum.inr Sum.inr_injective Sum.inr_injective Sum.inr_injective

theorem inl_liftL (x : _root_.Port N.label N.Wire ι) :
    inl N M (liftL N x) = embL N M x := by
  cases x <;> rfl

theorem inr_liftR (y : _root_.Port M.label M.Wire ι') :
    inr N M (liftR M y) = embR N M y := by
  cases y <;> rfl

theorem link_embL (x : _root_.Port N.label N.Wire ι) :
    link N M (embL N M x) = inl N M (N.link (liftL N x)) := by
  cases x <;> rfl

theorem link_embR (y : _root_.Port M.label M.Wire ι') :
    link N M (embR N M y) = inr N M (M.link (liftR M y)) := by
  cases y <;> rfl

theorem inl_free_inr (k : κ) : inl N M (.free (.inr k)) = inr N M (M.link (.free (.inl k))) := by
  have (r : M.Port) (h : r.IsEntity) :
      (r.ofEntity h).map Sum.inr (fun _ => rfl) Sum.inr id = inr N M r := by
    cases r
    · exact absurd h (Port.not_isEntity_free _)
    all_goals rfl
  exact this _ _

theorem inr_free_inl (k : κ) : inr N M (.free (.inl k)) = inl N M (N.link (.free (.inr k))) := by
  have (r : N.Port) (h : r.IsEntity) :
      (r.ofEntity h).map Sum.inl (fun _ => rfl) Sum.inl id = inl N M r := by
    cases r
    · exact absurd h (Port.not_isEntity_free _)
    all_goals rfl
  exact this _ _

/-- A port of `N` is either not glued, or a glued free port. -/
theorem cases_left (q : N.Port) :
    (∃ x : _root_.Port N.label N.Wire ι, q = liftL N x) ∨
      ∃ k, q = .free (.inr k) := by
  rcases q with (i | k) | a | ⟨a, j⟩ | ⟨w, s⟩
  · exact .inl ⟨.free i, rfl⟩
  · exact .inr ⟨k, rfl⟩
  · exact .inl ⟨.pri a, rfl⟩
  · exact .inl ⟨.aux a j, rfl⟩
  · exact .inl ⟨.wire w s, rfl⟩

/-- A port of `M` is either not glued, or a glued free port. -/
theorem cases_right (q : M.Port) :
    (∃ y : _root_.Port M.label M.Wire ι', q = liftR M y) ∨
      ∃ k, q = .free (.inl k) := by
  rcases q with (k | j) | b | ⟨b, j⟩ | ⟨w, s⟩
  · exact .inr ⟨k, rfl⟩
  · exact .inl ⟨.free j, rfl⟩
  · exact .inl ⟨.pri b, rfl⟩
  · exact .inl ⟨.aux b j, rfl⟩
  · exact .inl ⟨.wire w s, rfl⟩

/-- Every port of the glued net comes from a port of `N` or of `M` that is not glued. -/
theorem cases_glue (p : GluePort N M) :
    (∃ x : _root_.Port N.label N.Wire ι, p = embL N M x) ∨
      ∃ y : _root_.Port M.label M.Wire ι', p = embR N M y := by
  rcases p with (i | j) | (a | b) | ⟨a | b, k⟩ | ⟨w | w, s⟩
  · exact .inl ⟨.free i, rfl⟩
  · exact .inr ⟨.free j, rfl⟩
  · exact .inl ⟨.pri a, rfl⟩
  · exact .inr ⟨.pri b, rfl⟩
  · exact .inl ⟨.aux a k, rfl⟩
  · exact .inr ⟨.aux b k, rfl⟩
  · exact .inl ⟨.wire w s, rfl⟩
  · exact .inr ⟨.wire w s, rfl⟩

/-- An entity port of `N` is not glued. -/
theorem exists_map_of_isEntity_left {q : N.Port} (h : q.IsEntity) :
    ∃ x : _root_.Port N.label N.Wire ι, q = liftL N x :=
  ⟨q.ofEntity h, (Port.map_ofEntity _ _ _).symm⟩

/-- An entity port of `M` is not glued. -/
theorem exists_map_of_isEntity_right {q : M.Port} (h : q.IsEntity) :
    ∃ y : _root_.Port M.label M.Wire ι', q = liftR M y :=
  ⟨q.ofEntity h, (Port.map_ofEntity _ _ _).symm⟩

theorem link_inl (q : N.Port) : link N M (inl N M q) = inl N M (N.link q) := by
  rcases cases_left N q with ⟨x, rfl⟩ | ⟨k, rfl⟩
  · rw [inl_liftL, link_embL]
  · obtain ⟨y, hy⟩ := exists_map_of_isEntity_right M (M.link_free (.inl k))
    rw [inl_free_inr, hy, inr_liftR, link_embR, ← hy, M.link_link, inr_free_inl]

theorem link_inr (q : M.Port) : link N M (inr N M q) = inr N M (M.link q) := by
  rcases cases_right M q with ⟨y, rfl⟩ | ⟨k, rfl⟩
  · rw [inr_liftR, link_embR]
  · obtain ⟨x, hx⟩ := exists_map_of_isEntity_left N (N.link_free (.inr k))
    rw [inr_free_inl, hx, inl_liftL, link_embL, ← hx, N.link_link, inl_free_inr]

theorem embL_ne_embR (x : _root_.Port N.label N.Wire ι)
    (y : _root_.Port M.label M.Wire ι') :
    embL N M x ≠ embR N M y := by
  cases x <;> cases y <;> nofun

theorem link_embL_ne (x : _root_.Port N.label N.Wire ι) :
    link N M (embL N M x) ≠ embL N M x := by
  rw [← inl_liftL, link_inl]
  rcases cases_left N (N.link (liftL N x)) with ⟨x', hx'⟩ | ⟨k, hk⟩
  · rw [hx', inl_liftL, inl_liftL]
    intro h
    apply N.link_ne (liftL N x)
    rw [hx', embL_injective N M h]
  · obtain ⟨y, hy⟩ := exists_map_of_isEntity_right M (M.link_free (.inl k))
    rw [hk, inl_free_inr, hy, inr_liftR, inl_liftL]
    exact (embL_ne_embR N M x y).symm

theorem link_embR_ne (y : _root_.Port M.label M.Wire ι') :
    link N M (embR N M y) ≠ embR N M y := by
  rw [← inr_liftR, link_inr]
  rcases cases_right M (M.link (liftR M y)) with ⟨y', hy'⟩ | ⟨k, hk⟩
  · rw [hy', inr_liftR, inr_liftR]
    intro h
    apply M.link_ne (liftR M y)
    rw [hy', embR_injective N M h]
  · obtain ⟨x, hx⟩ := exists_map_of_isEntity_left N (N.link_free (.inr k))
    rw [hk, inr_free_inl, hx, inl_liftL, inr_liftR]
    exact embL_ne_embR N M x y

end Glue

open Glue in
/-- Glue `N` and `M` along `κ`. -/
@[reducible] def glue : Net S (ι ⊕ ι') where
  Agent := N.Agent ⊕ M.Agent
  Wire := N.Wire ⊕ M.Wire
  label := Sum.elim N.label M.label
  link := Glue.link N M
  link_link p := by
    rcases cases_glue N M p with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · rw [← inl_liftL, link_inl, link_inl, N.link_link]
    · rw [← inr_liftR, link_inr, link_inr, M.link_link]
  link_ne p := by
    rcases cases_glue N M p with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact link_embL_ne N M x
    · exact link_embR_ne N M y
  link_free
    | .inl i => by
      obtain ⟨x, hx⟩ := exists_map_of_isEntity_left N (N.link_free (.inl i))
      have := N.link_free (.inl i)
      change (inl N M (N.link (.free (.inl i)))).IsEntity
      rw [hx, isEntity_liftL] at this
      rw [hx, inl_liftL, isEntity_embL]
      exact this
    | .inr j => by
      obtain ⟨y, hy⟩ := exists_map_of_isEntity_right M (M.link_free (.inr j))
      have := M.link_free (.inr j)
      change (inr N M (M.link (.free (.inr j)))).IsEntity
      rw [hy, isEntity_liftR] at this
      rw [hy, inr_liftR, isEntity_embR]
      exact this

theorem glue_link_inl (q : N.Port) :
    (N.glue M).link (Glue.inl N M q) = Glue.inl N M (N.link q) :=
  Glue.link_inl N M q

theorem glue_link_inr (q : M.Port) :
    (N.glue M).link (Glue.inr N M q) = Glue.inr N M (M.link q) :=
  Glue.link_inr N M q

/-- To show that a map of ports out of a glued net commutes with the links, it suffices to
check this on the ports of the two parts. -/
theorem glue_link_ext {ι'' : Type} {X : Net S ι''} (F : (N.glue M).Port → X.Port)
    (hl : ∀ q, X.link (F (Glue.inl N M q)) = F (Glue.inl N M (N.link q)))
    (hr : ∀ q, X.link (F (Glue.inr N M q)) = F (Glue.inr N M (M.link q)))
    (p : (N.glue M).Port) : X.link (F p) = F ((N.glue M).link p) := by
  rcases Glue.cases_glue N M p with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · rw [← Glue.inl_liftL, hl, glue_link_inl]
  · rw [← Glue.inr_liftR, hr, glue_link_inr]

theorem glue_link_free_inl (i : ι) :
    (N.glue M).link (.free (.inl i)) = Glue.inl N M (N.link (.free (.inl i))) := rfl

theorem glue_link_free_inr (j : ι') :
    (N.glue M).link (.free (.inr j)) = Glue.inr N M (M.link (.free (.inr j))) := rfl

end glue

/-! ### Gluing respects isomorphism -/

section congr

variable {ι κ ι' : Type} {N N' : Net S (ι ⊕ κ)} {M M' : Net S (κ ⊕ ι')}
  (e : Iso N N') (e' : Iso M M')

theorem Iso.glue_label_agent (a : (N.glue M).Agent) :
    (N'.glue M').label (e.agent.sumCongr e'.agent a) = (N.glue M).label a := by
  rcases a with a | b
  exacts [e.label_agent a, e'.label_agent b]

/-- The map of ports underlying `Iso.glue`. -/
abbrev Iso.gluePort : (N.glue M).Port → (N'.glue M').Port :=
  Port.map (e.agent.sumCongr e'.agent) (e.glue_label_agent e') (e.wire.sumCongr e'.wire) id

theorem Iso.gluePort_inl (q : N.Port) :
    e.gluePort e' (Glue.inl N M q) = Glue.inl N' M' (e.port q) := by
  rcases q with (i | k) | a | ⟨a, j⟩ | ⟨w, s⟩
  · rfl
  · have (r : M.Port) (h : r.IsEntity) :
        e.gluePort e' (Glue.inr N M r) = Glue.inr N' M' (e'.port r) := by
      cases r
      · exact absurd h (Port.not_isEntity_free _)
      all_goals rfl
    rw [Glue.inl_free_inr, this _ (M.link_free _), ← e'.link_port]
    exact (Glue.inl_free_inr N' M' k).symm
  all_goals rfl

theorem Iso.gluePort_inr (q : M.Port) :
    e.gluePort e' (Glue.inr N M q) = Glue.inr N' M' (e'.port q) := by
  rcases q with (k | j) | b | ⟨b, j⟩ | ⟨w, s⟩
  · have (r : N.Port) (h : r.IsEntity) :
        e.gluePort e' (Glue.inl N M r) = Glue.inl N' M' (e.port r) := by
      cases r
      · exact absurd h (Port.not_isEntity_free _)
      all_goals rfl
    rw [Glue.inr_free_inl, this _ (N.link_free _), ← e.link_port]
    exact (Glue.inr_free_inl N' M' k).symm
  all_goals rfl

/-- Gluing respects isomorphism. -/
def Iso.glue : Iso (N.glue M) (N'.glue M') where
  agent := e.agent.sumCongr e'.agent
  wire := e.wire.sumCongr e'.wire
  label_agent := e.glue_label_agent e'
  link_map := glue_link_ext N M (e.gluePort e')
    (fun q => by rw [gluePort_inl, gluePort_inl, glue_link_inl, link_port])
    (fun q => by rw [gluePort_inr, gluePort_inr, glue_link_inr, link_port])

end congr

/-! ### Associativity -/

section assoc

variable {ι κ μ ι' : Type} (N : Net S (ι ⊕ κ)) (M : Net S (κ ⊕ μ))
  (K : Net S (μ ⊕ ι'))

theorem glueAssoc_label_agent (a : ((N.glue M).glue K).Agent) :
    (N.glue (M.glue K)).label (Equiv.sumAssoc _ _ _ a) = ((N.glue M).glue K).label a := by
  rcases a with (a | b) | c <;> rfl

/-- The map of ports underlying `glueAssoc`. -/
abbrev glueAssocPort : ((N.glue M).glue K).Port → (N.glue (M.glue K)).Port :=
  Port.map (Equiv.sumAssoc _ _ _) (glueAssoc_label_agent N M K) (Equiv.sumAssoc _ _ _) id

theorem glueAssocPort_entity_left (q : N.Port) (h : q.IsEntity) :
    glueAssocPort N M K (Glue.inl _ K (Glue.inl N M q)) = Glue.inl N (M.glue K) q := by
  cases q
  · exact absurd h (Port.not_isEntity_free _)
  all_goals rfl

theorem glueAssocPort_entity_mid (q : M.Port) (h : q.IsEntity) :
    glueAssocPort N M K (Glue.inl _ K (Glue.inr N M q)) =
      Glue.inr N (M.glue K) (Glue.inl M K q) := by
  cases q
  · exact absurd h (Port.not_isEntity_free _)
  all_goals rfl

theorem glueAssocPort_entity_right (q : K.Port) (h : q.IsEntity) :
    glueAssocPort N M K (Glue.inr (N.glue M) K q) =
      Glue.inr N (M.glue K) (Glue.inr M K q) := by
  cases q
  · exact absurd h (Port.not_isEntity_free _)
  all_goals rfl

theorem glueAssocPort_left (q : N.Port) :
    glueAssocPort N M K (Glue.inl _ K (Glue.inl N M q)) = Glue.inl N (M.glue K) q := by
  rcases q with (i | k) | q
  · rfl
  · rw [Glue.inl_free_inr N M k, glueAssocPort_entity_mid _ _ _ _ (M.link_free _),
      Glue.inl_free_inr N (M.glue K) k, glue_link_free_inl]
  all_goals exact glueAssocPort_entity_left N M K _ trivial

theorem glueAssocPort_mid (q : M.Port) :
    glueAssocPort N M K (Glue.inl _ K (Glue.inr N M q)) =
      Glue.inr N (M.glue K) (Glue.inl M K q) := by
  rcases q with (k | l) | q
  · rw [Glue.inr_free_inl N M k, glueAssocPort_entity_left _ _ _ _ (N.link_free _)]
    exact (Glue.inr_free_inl N (M.glue K) k).symm
  · change glueAssocPort N M K (Glue.inl _ K (.free (.inr l))) = _
    rw [Glue.inl_free_inr _ K l, glueAssocPort_entity_right _ _ _ _ (K.link_free _),
      Glue.inl_free_inr M K l]
  all_goals exact glueAssocPort_entity_mid N M K _ trivial

theorem glueAssocPort_right (q : K.Port) :
    glueAssocPort N M K (Glue.inr (N.glue M) K q) =
      Glue.inr N (M.glue K) (Glue.inr M K q) := by
  rcases q with (l | j) | q
  · rw [Glue.inr_free_inl _ K l, glue_link_free_inr,
      glueAssocPort_entity_mid _ _ _ _ (M.link_free _), Glue.inr_free_inl M K l]
  · rfl
  all_goals exact glueAssocPort_entity_right N M K _ trivial

/-- Gluing is associative up to isomorphism. -/
def glueAssoc : Iso ((N.glue M).glue K) (N.glue (M.glue K)) where
  agent := Equiv.sumAssoc _ _ _
  wire := Equiv.sumAssoc _ _ _
  label_agent := glueAssoc_label_agent N M K
  link_map := glue_link_ext (N.glue M) K (glueAssocPort N M K)
    (glue_link_ext N M (fun q => glueAssocPort N M K (Glue.inl _ K q))
      (fun q => by rw [glueAssocPort_left, glueAssocPort_left, glue_link_inl])
      (fun q => by
        rw [glueAssocPort_mid, glueAssocPort_mid, glue_link_inr, glue_link_inl]))
    (fun q => by
      rw [glueAssocPort_right, glueAssocPort_right, glue_link_inr, glue_link_inr])

end assoc

/-! ### Commutativity -/

section comm

variable {ι κ ι' : Type} (N : Net S (ι ⊕ κ)) (M : Net S (κ ⊕ ι'))

/-- `glue N M` the other way round: glue `M` to `N`, swapping all interfaces. -/
abbrev glueSwap : Net S (ι ⊕ ι') := (M.swap.glue N.swap).swap

theorem glueComm_label_agent (a : (N.glue M).Agent) :
    (glueSwap N M).label (Equiv.sumComm _ _ a) = (N.glue M).label a := by
  rcases a with a | b <;> rfl

/-- The map of ports underlying `glueComm`. -/
abbrev glueCommPort : (N.glue M).Port → (glueSwap N M).Port :=
  Port.map (Equiv.sumComm _ _) (glueComm_label_agent N M) (Equiv.sumComm _ _) id

theorem glueCommPort_entity_inl (q : N.Port) (h : q.IsEntity) :
    glueCommPort N M (Glue.inl N M q) =
      (M.swap.glue N.swap).swapPort (Glue.inr M.swap N.swap (N.swapPort q)) := by
  cases q
  · exact absurd h (Port.not_isEntity_free _)
  all_goals rfl

theorem glueCommPort_entity_inr (q : M.Port) (h : q.IsEntity) :
    glueCommPort N M (Glue.inr N M q) =
      (M.swap.glue N.swap).swapPort (Glue.inl M.swap N.swap (M.swapPort q)) := by
  cases q
  · exact absurd h (Port.not_isEntity_free _)
  all_goals rfl

theorem glueCommPort_inl (q : N.Port) :
    glueCommPort N M (Glue.inl N M q) =
      (M.swap.glue N.swap).swapPort (Glue.inr M.swap N.swap (N.swapPort q)) := by
  rcases q with (i | k) | q
  · rfl
  · rw [Glue.inl_free_inr N M k, glueCommPort_entity_inr _ _ _ (M.link_free _),
      ← swap_link]
    exact congrArg _ (Glue.inr_free_inl M.swap N.swap k).symm
  all_goals exact glueCommPort_entity_inl N M _ trivial

theorem glueCommPort_inr (q : M.Port) :
    glueCommPort N M (Glue.inr N M q) =
      (M.swap.glue N.swap).swapPort (Glue.inl M.swap N.swap (M.swapPort q)) := by
  rcases q with (k | j) | q
  · rw [Glue.inr_free_inl N M k, glueCommPort_entity_inl _ _ _ (N.link_free _),
      ← swap_link]
    exact congrArg _ (Glue.inl_free_inr M.swap N.swap k).symm
  · rfl
  all_goals exact glueCommPort_entity_inr N M _ trivial

/-- Gluing is commutative up to isomorphism, after swapping the interfaces. -/
def glueComm : Iso (N.glue M) (glueSwap N M) where
  agent := Equiv.sumComm _ _
  wire := Equiv.sumComm _ _
  label_agent := glueComm_label_agent N M
  link_map := glue_link_ext N M (glueCommPort N M)
    (fun q => by rw [glueCommPort_inl, glueCommPort_inl, swap_link, glue_link_inr, swap_link])
    (fun q => by rw [glueCommPort_inr, glueCommPort_inr, swap_link, glue_link_inl, swap_link])

end comm

end Net

module

public import LeanInets.Contract

/-!
# The identity net is a unit for gluing

The identity net `idNet S κ` consists of one wire for each `k : κ`, connecting the free
ports `inl k` and `inr k`. Gluing it onto a net puts a wire in front of each glued free
port, so it is a unit for gluing only up to wire contraction, i.e. up to `≈`.

To contract the wires one at a time we use an auxiliary construction: `N.extend s T` puts a
new wire in front of each free port in the finite set `T`, with its end `s` facing the free
port. By induction on `T`, `N.extend s T ≈ N`, and gluing the identity net on either side is
isomorphic to such an extension.
-/

@[expose] public section

namespace Net

variable {S : Signature}

/-- The identity net on `κ`: a wire for each `k : κ`, with its left end linked to the free
port `inl k` and its right end linked to the free port `inr k`. -/
def idNet (S : Signature) (κ : Type) [Fintype κ] : Net S (κ ⊕ κ) where
  Agent := Empty
  Wire := κ
  label := Empty.elim
  link
    | .free (.inl k) => .wire k .l
    | .free (.inr k) => .wire k .r
    | .wire k .l => .free (.inl k)
    | .wire k .r => .free (.inr k)
    | .pri a => a.elim
    | .aux a _ => a.elim
  link_link p := by rcases p with (_ | _) | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨_, _ | _⟩ <;> rfl
  link_ne p := by rcases p with (_ | _) | ⟨⟨⟩⟩ | ⟨⟨⟩, _⟩ | ⟨_, _ | _⟩ <;> nofun
  link_free := by rintro (_ | _) <;> trivial

/-! ### Extending a net by wires at its free ports -/

section extend

variable {ι : Type} (N : Net S ι) (s : Side) (T : Finset ι)

namespace Extend

/-- The ports of `N.extend s T`. -/
abbrev EPort := _root_.Port N.label (N.Wire ⊕ T) ι

open Classical in
/-- Where a port of `N` ends up: a free port in `T` is replaced by the inner end of its new
wire. -/
noncomputable def ext : N.Port → EPort N T
  | .free i => if h : i ∈ T then .wire (.inr ⟨i, h⟩) s.flip else .free i
  | .pri a => .pri a
  | .aux a k => .aux a k
  | .wire v s' => .wire (.inl v) s'

/-- A left inverse of `ext`. -/
def unext : EPort N T → N.Port
  | .free i => .free i
  | .pri a => .pri a
  | .aux a k => .aux a k
  | .wire (.inl v) s' => .wire v s'
  | .wire (.inr i) _ => .free i.1

open Classical in
/-- The links of `N.extend s T`. -/
noncomputable def link : EPort N T → EPort N T
  | .free i => if h : i ∈ T then .wire (.inr ⟨i, h⟩) s else ext N s T (N.link (.free i))
  | .pri a => ext N s T (N.link (.pri a))
  | .aux a k => ext N s T (N.link (.aux a k))
  | .wire (.inl v) s' => ext N s T (N.link (.wire v s'))
  | .wire (.inr i) s' => if s' = s then .free i.1 else ext N s T (N.link (.free i.1))

variable {N s T}

theorem ext_free_mem {i : ι} (h : i ∈ T) :
    ext N s T (.free i) = .wire (.inr ⟨i, h⟩) s.flip := by
  simp [ext, h]

theorem ext_free_not_mem {i : ι} (h : i ∉ T) : ext N s T (.free i) = .free i := by
  simp [ext, h]

theorem unext_ext (q : N.Port) : unext N T (ext N s T q) = q := by
  cases q with
  | free i =>
    by_cases h : i ∈ T
    · rw [ext_free_mem h]; rfl
    · rw [ext_free_not_mem h]; rfl
  | _ => rfl

theorem ext_injective : Function.Injective (ext N s T) :=
  Function.LeftInverse.injective unext_ext

theorem isEntity_ext {q : N.Port} (h : q.IsEntity) : (ext N s T q).IsEntity := by
  cases q
  · exact absurd h (Port.not_isEntity_free _)
  all_goals trivial

theorem link_free_mem {i : ι} (h : i ∈ T) :
    link N s T (.free i) = .wire (.inr ⟨i, h⟩) s := by
  simp [link, h]

theorem link_free_not_mem {i : ι} (h : i ∉ T) :
    link N s T (.free i) = ext N s T (N.link (.free i)) := by
  simp [link, h]

theorem link_wire_inr_self (i : T) : link N s T (.wire (.inr i) s) = .free i.1 := by
  simp [link]

theorem link_wire_inr_flip (i : T) :
    link N s T (.wire (.inr i) s.flip) = ext N s T (N.link (.free i.1)) := by
  simp [link, Side.flip_ne]

theorem link_ext (q : N.Port) : link N s T (ext N s T q) = ext N s T (N.link q) := by
  cases q with
  | free i =>
    by_cases h : i ∈ T
    · rw [ext_free_mem h, link_wire_inr_flip]
    · rw [ext_free_not_mem h, link_free_not_mem h]
  | _ => rfl

/-- Every port of the extension comes from `N`, or is a free port in `T`, or is the outer end
of a new wire. -/
theorem cases_port (p : EPort N T) :
    (∃ q, p = ext N s T q) ∨ (∃ i ∈ T, p = .free i) ∨
      ∃ i : T, p = .wire (.inr i) s := by
  rcases p with i | a | ⟨a, k⟩ | ⟨v | ⟨i, h⟩, s'⟩
  · by_cases h : i ∈ T
    · exact .inr (.inl ⟨i, h, rfl⟩)
    · exact .inl ⟨.free i, (ext_free_not_mem h).symm⟩
  · exact .inl ⟨.pri a, rfl⟩
  · exact .inl ⟨.aux a k, rfl⟩
  · exact .inl ⟨.wire v s', rfl⟩
  · by_cases hs : s' = s
    · exact .inr (.inr ⟨⟨i, h⟩, hs ▸ rfl⟩)
    · refine .inl ⟨.free i, ?_⟩
      rw [ext_free_mem h]
      cases s <;> cases s' <;> first | rfl | exact absurd rfl hs

end Extend

open Extend in
/-- Put a new wire in front of each free port in `T`. The end `s` of the new wire is linked to
the free port, and its other end to the port of `N` that was linked to the free port. -/
@[reducible] noncomputable def extend : Net S ι where
  Agent := N.Agent
  Wire := N.Wire ⊕ T
  label := N.label
  link := Extend.link N s T
  link_link p := by
    rcases cases_port (s := s) p with ⟨q, rfl⟩ | ⟨i, h, rfl⟩ | ⟨i, rfl⟩
    · rw [link_ext, link_ext, N.link_link]
    · rw [link_free_mem h, link_wire_inr_self]
    · rw [link_wire_inr_self, link_free_mem i.2]
  link_ne p := by
    rcases cases_port (s := s) p with ⟨q, rfl⟩ | ⟨i, h, rfl⟩ | ⟨i, rfl⟩
    · rw [link_ext]
      exact fun e => N.link_ne q (ext_injective e)
    · rw [link_free_mem h]
      nofun
    · rw [link_wire_inr_self]
      nofun
  link_free i := by
    by_cases h : i ∈ T
    · rw [link_free_mem h]
      trivial
    · rw [link_free_not_mem h]
      exact isEntity_ext (N.link_free i)

open Extend

/-- Extending by no wires changes nothing. -/
noncomputable def extendEmpty : Iso N (N.extend s ∅) where
  agent := Equiv.refl N.Agent
  wire := (Equiv.sumEmpty N.Wire (∅ : Finset ι)).symm
  label_agent _ := rfl
  link_map p := by
    have h (q : N.Port) : q.map (label' := N.label) (Equiv.refl N.Agent) (fun _ => rfl)
        (Equiv.sumEmpty N.Wire (∅ : Finset ι)).symm id = ext N s ∅ q := by
      cases q with
      | free i => exact (ext_free_not_mem (Finset.notMem_empty i)).symm
      | _ => rfl
    exact (congrArg (Extend.link N s ∅) (h p)).trans ((link_ext p).trans (h _).symm)

variable {N s T}

/-- The wires of the smaller extension, as the wires of the larger one other than the new wire
at `k`. -/
def extendInsertWire [DecidableEq ι] {k : ι} (hk : k ∉ T) :
    N.Wire ⊕ T ≃
      {v : N.Wire ⊕ (insert k T : Finset ι) // v ≠ .inr ⟨k, Finset.mem_insert_self k T⟩} where
  toFun
    | .inl v => ⟨.inl v, nofun⟩
    | .inr ⟨i, h⟩ => ⟨.inr ⟨i, Finset.mem_insert_of_mem h⟩, fun e => by
        cases e
        exact hk h⟩
  invFun
    | ⟨.inl v, _⟩ => .inl v
    | ⟨.inr ⟨i, h⟩, hne⟩ => .inr ⟨i, (Finset.mem_insert.mp h).resolve_left fun e => by
        subst e
        exact hne rfl⟩
  left_inv v := by rcases v with v | ⟨i, h⟩ <;> rfl
  right_inv v := by rcases v with ⟨v | ⟨i, h⟩, hne⟩ <;> rfl

section insert

variable [DecidableEq ι] {k : ι}

/-- The new wire at `k`. -/
abbrev newWire (N : Net S ι) (s : Side) (T : Finset ι) (k : ι) :
    (N.extend s (insert k T)).Wire :=
  .inr ⟨k, Finset.mem_insert_self k T⟩

theorem newWire_ne {i : ι} (hk : k ∉ T) (hi : i ∈ T) {h} :
    (.inr ⟨i, h⟩ : (N.extend s (insert k T)).Wire) ≠ newWire N s T k := fun e => by
  have : i = k := congrArg Subtype.val (Sum.inr_injective e)
  exact hk (this ▸ hi)

/-- Ports of `N` avoid the new wire at `k`, except for the free port `k`. -/
theorem avoids_newWire (q : N.Port) (hq : q ≠ .free k) :
    (N.extend s (insert k T)).Avoids (newWire N s T k) (ext N s (insert k T) q) := by
  cases q with
  | free i =>
    by_cases hi : i ∈ insert k T
    · rw [ext_free_mem hi]
      refine avoids_wire.mpr fun e => hq ?_
      have : i = k := congrArg Subtype.val (Sum.inr_injective e)
      rw [this]
    · rw [ext_free_not_mem hi]
      exact avoids_free _
  | pri a => exact fun _ => nofun
  | aux a j => exact fun _ => nofun
  | wire v s' => exact avoids_wire.mpr nofun

/-- Entity ports of `N` avoid the new wire at `k`. -/
theorem avoids_newWire_link (q : N.Port) (hq : q.IsEntity) :
    (N.extend s (insert k T)).Avoids (newWire N s T k) (ext N s (insert k T) q) := by
  cases q with
  | free i => exact absurd hq (Port.not_isEntity_free _)
  | pri a => exact fun _ => nofun
  | aux a j => exact fun _ => nofun
  | wire v s' => exact avoids_wire.mpr nofun

/-- The ports of the smaller extension as ports of the larger one. -/
noncomputable def extendInsertPort (hk : k ∉ T) (p : (N.extend s T).Port) :
    (N.extend s (insert k T)).Port :=
  p.map (Equiv.refl _) (fun _ => rfl) (fun v => (extendInsertWire hk v).1) id

theorem extendInsertPort_ext (hk : k ∉ T) (q : N.Port) :
    extendInsertPort hk (ext N s T q) =
      (N.extend s (insert k T)).skip (newWire N s T k) (ext N s (insert k T) q) := by
  by_cases hq : q = .free k
  · subst hq
    rw [ext_free_not_mem hk, ext_free_mem (Finset.mem_insert_self k T), skip_wire_self,
      Side.flip_flip]
    exact (link_wire_inr_self (N := N) (s := s) (T := insert k T)
      ⟨k, Finset.mem_insert_self k T⟩).symm
  rw [skip_of_avoids (avoids_newWire q hq)]
  cases q with
  | free i =>
    by_cases hi : i ∈ T
    · rw [ext_free_mem hi, ext_free_mem (Finset.mem_insert_of_mem hi)]
      rfl
    · have hi' : i ∉ insert k T := by
        rw [Finset.mem_insert, not_or]
        exact ⟨fun e => hq (e ▸ rfl), hi⟩
      rw [ext_free_not_mem hi, ext_free_not_mem hi']
      rfl
  | _ => rfl

theorem extendInsertPort_link (hk : k ∉ T) (p : (N.extend s T).Port) :
    (N.extend s (insert k T)).skip (newWire N s T k)
      ((N.extend s (insert k T)).link (extendInsertPort hk p)) =
      extendInsertPort hk ((N.extend s T).link p) := by
  rcases cases_port (N := N) (s := s) (T := T) p with ⟨q, rfl⟩ | ⟨i, h, rfl⟩ | ⟨⟨i, h⟩, rfl⟩
  · have h : (N.extend s (insert k T)).Avoids (newWire N s T k) (ext N s (insert k T) q) ∨
        (N.extend s (insert k T)).Avoids (newWire N s T k)
          ((N.extend s (insert k T)).link (ext N s (insert k T) q)) := by
      by_cases hq : q = .free k
      · subst hq
        refine .inr ?_
        change (N.extend s (insert k T)).Avoids _ (Extend.link N s _ _)
        rw [link_ext]
        exact avoids_newWire_link _ (N.link_free k)
      · exact .inl (avoids_newWire q hq)
    rw [extendInsertPort_ext, skip_link_skip h]
    change _ = extendInsertPort hk (Extend.link N s T (ext N s T q))
    change (N.extend s (insert k T)).skip _ (Extend.link N s _ _) = _
    rw [link_ext, link_ext, extendInsertPort_ext]
  · change (N.extend s (insert k T)).skip _ (Extend.link N s _ (.free i)) =
      extendInsertPort hk (Extend.link N s T (.free i))
    rw [link_free_mem (Finset.mem_insert_of_mem h), link_free_mem h,
      skip_wire_of_ne (newWire_ne hk h)]
    rfl
  · change (N.extend s (insert k T)).skip _
        (Extend.link N s _ (.wire (.inr ⟨i, Finset.mem_insert_of_mem h⟩) s)) =
      extendInsertPort hk (Extend.link N s T (.wire (.inr ⟨i, h⟩) s))
    rw [link_wire_inr_self, link_wire_inr_self]
    rfl

/-- Contracting one of the new wires of an extension. -/
noncomputable def extendInsert (hk : k ∉ T) :
    Contraction (N.extend s (insert k T)) (N.extend s T) where
  removed := newWire N s T k
  agent := .refl _
  wire := extendInsertWire hk
  label_agent _ := rfl
  link_map := extendInsertPort_link hk

end insert

/-- Extending a net by wires at its free ports does not change it up to `≈`. -/
theorem extend_equiv (N : Net S ι) (s : Side) (T : Finset ι) : N.extend s T ≈ N := by
  classical
  induction T using Finset.induction_on with
  | empty => exact Setoid.symm (extendEmpty N s).equiv
  | insert k T hk ih => exact Setoid.trans (extendInsert hk).equiv ih

end extend

/-! ### The unit laws -/

section unit

open Extend

variable {κ ι : Type} [Fintype κ]

/-- The left half of an interface `κ ⊕ ι`, as a finite set. -/
def leftPorts (κ ι : Type) [Fintype κ] : Finset (κ ⊕ ι) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

/-- The right half of an interface `ι ⊕ κ`, as a finite set. -/
def rightPorts (ι κ : Type) [Fintype κ] : Finset (ι ⊕ κ) :=
  Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

theorem inl_mem_leftPorts (k : κ) : (.inl k : κ ⊕ ι) ∈ leftPorts κ ι := by simp [leftPorts]
theorem inr_not_mem_leftPorts (i : ι) : (.inr i : κ ⊕ ι) ∉ leftPorts κ ι := by simp [leftPorts]
theorem inr_mem_rightPorts (k : κ) : (.inr k : ι ⊕ κ) ∈ rightPorts ι κ := by simp [rightPorts]
theorem inl_not_mem_rightPorts (i : ι) : (.inl i : ι ⊕ κ) ∉ rightPorts ι κ := by
  simp [rightPorts]

/-- `κ` as the left half of `κ ⊕ ι`. -/
def leftPortsEquiv : κ ≃ leftPorts κ ι where
  toFun k := ⟨.inl k, inl_mem_leftPorts k⟩
  invFun
    | ⟨.inl k, _⟩ => k
    | ⟨.inr i, h⟩ => absurd h (inr_not_mem_leftPorts i)
  left_inv _ := rfl
  right_inv
    | ⟨.inl _, _⟩ => rfl
    | ⟨.inr i, h⟩ => absurd h (inr_not_mem_leftPorts i)

/-- `κ` as the right half of `ι ⊕ κ`. -/
def rightPortsEquiv : κ ≃ rightPorts ι κ where
  toFun k := ⟨.inr k, inr_mem_rightPorts k⟩
  invFun
    | ⟨.inr k, _⟩ => k
    | ⟨.inl i, h⟩ => absurd h (inl_not_mem_rightPorts i)
  left_inv _ := rfl
  right_inv
    | ⟨.inr _, _⟩ => rfl
    | ⟨.inl i, h⟩ => absurd h (inl_not_mem_rightPorts i)

/-! #### Left unit -/

section left

variable (N : Net S (κ ⊕ ι))

theorem idNetGlue_label (a : ((idNet S κ).glue N).Agent) :
    (N.extend .l (leftPorts κ ι)).label
      ((Equiv.emptySum Empty N.Agent : (idNet S κ).Agent ⊕ N.Agent ≃ N.Agent) a) =
      ((idNet S κ).glue N).label a := by
  rcases a with a | a
  exacts [(a : Empty).elim, rfl]

/-- The map of ports underlying `idNetGlueIso`. -/
noncomputable abbrev idNetGluePort :
    ((idNet S κ).glue N).Port → (N.extend .l (leftPorts κ ι)).Port :=
  Port.map (Equiv.emptySum Empty N.Agent : (idNet S κ).Agent ⊕ N.Agent ≃ N.Agent)
    (idNetGlue_label N) ((Equiv.sumComm _ _).trans ((Equiv.refl _).sumCongr leftPortsEquiv)) id

theorem idNetGluePort_inr (q : N.Port) :
    idNetGluePort N (Glue.inr (idNet S κ) N q) = ext N .l (leftPorts κ ι) q := by
  rcases q with (k | j) | q
  · rw [ext_free_mem (inl_mem_leftPorts k)]
    rfl
  · rw [ext_free_not_mem (inr_not_mem_leftPorts j)]
    rfl
  all_goals rfl

theorem idNetGluePort_link_inl (q : (idNet S κ).Port) :
    (N.extend .l (leftPorts κ ι)).link (idNetGluePort N (Glue.inl (idNet S κ) N q)) =
      idNetGluePort N (Glue.inl (idNet S κ) N ((idNet S κ).link q)) := by
  rcases q with (k | k) | a | ⟨a, _⟩ | ⟨k, _ | _⟩
  · exact link_free_mem (inl_mem_leftPorts k)
  · rw [Glue.inl_free_inr, idNetGluePort_inr]
    refine (link_ext (N := N) (s := .l) _).trans ?_
    rw [N.link_link, ext_free_mem (inl_mem_leftPorts k)]
    rfl
  · exact (a : Empty).elim
  · exact (a : Empty).elim
  · exact link_wire_inr_self (N := N) (s := .l) (leftPortsEquiv k)
  · refine (link_wire_inr_flip (N := N) (s := .l) (leftPortsEquiv k)).trans ?_
    exact ((congrArg (idNetGluePort N) (Glue.inl_free_inr (idNet S κ) N k)).trans
      (idNetGluePort_inr N _)).symm

/-- Gluing the identity net on the left puts a wire in front of each left free port. -/
noncomputable def idNetGlueIso : Iso ((idNet S κ).glue N) (N.extend .l (leftPorts κ ι)) where
  agent := (Equiv.emptySum Empty N.Agent : (idNet S κ).Agent ⊕ N.Agent ≃ N.Agent)
  wire := (Equiv.sumComm _ _).trans ((Equiv.refl _).sumCongr leftPortsEquiv)
  label_agent := idNetGlue_label N
  link_map := glue_link_ext _ _ (idNetGluePort N) (idNetGluePort_link_inl N) fun q => by
    rw [idNetGluePort_inr, idNetGluePort_inr]
    exact link_ext q

/-- The identity net is a left unit for gluing, up to `≈`. -/
theorem idNet_glue : (idNet S κ).glue N ≈ N :=
  Setoid.trans (idNetGlueIso N).equiv (extend_equiv _ _ _)

end left

/-! #### Right unit -/

section right

variable (N : Net S (ι ⊕ κ))

theorem glueIdNet_label (a : (N.glue (idNet S κ)).Agent) :
    (N.extend .r (rightPorts ι κ)).label
      ((Equiv.sumEmpty N.Agent Empty : N.Agent ⊕ (idNet S κ).Agent ≃ N.Agent) a) =
      (N.glue (idNet S κ)).label a := by
  rcases a with a | a
  exacts [rfl, (a : Empty).elim]

/-- The map of ports underlying `glueIdNetIso`. -/
noncomputable abbrev glueIdNetPort :
    (N.glue (idNet S κ)).Port → (N.extend .r (rightPorts ι κ)).Port :=
  Port.map (Equiv.sumEmpty N.Agent Empty : N.Agent ⊕ (idNet S κ).Agent ≃ N.Agent)
    (glueIdNet_label N) ((Equiv.refl _).sumCongr rightPortsEquiv) id

theorem glueIdNetPort_inl (q : N.Port) :
    glueIdNetPort N (Glue.inl N (idNet S κ) q) = ext N .r (rightPorts ι κ) q := by
  rcases q with (i | k) | q
  · rw [ext_free_not_mem (inl_not_mem_rightPorts i)]
    rfl
  · rw [ext_free_mem (inr_mem_rightPorts k)]
    rfl
  all_goals rfl

theorem glueIdNetPort_link_inr (q : (idNet S κ).Port) :
    (N.extend .r (rightPorts ι κ)).link (glueIdNetPort N (Glue.inr N (idNet S κ) q)) =
      glueIdNetPort N (Glue.inr N (idNet S κ) ((idNet S κ).link q)) := by
  rcases q with (k | k) | a | ⟨a, _⟩ | ⟨k, _ | _⟩
  · rw [Glue.inr_free_inl, glueIdNetPort_inl]
    refine (link_ext (N := N) (s := .r) _).trans ?_
    rw [N.link_link, ext_free_mem (inr_mem_rightPorts k)]
    rfl
  · exact link_free_mem (inr_mem_rightPorts k)
  · exact (a : Empty).elim
  · exact (a : Empty).elim
  · refine (link_wire_inr_flip (N := N) (s := .r) (rightPortsEquiv k)).trans ?_
    exact ((congrArg (glueIdNetPort N) (Glue.inr_free_inl N (idNet S κ) k)).trans
      (glueIdNetPort_inl N _)).symm
  · exact link_wire_inr_self (N := N) (s := .r) (rightPortsEquiv k)

/-- Gluing the identity net on the right puts a wire in front of each right free port. -/
noncomputable def glueIdNetIso : Iso (N.glue (idNet S κ)) (N.extend .r (rightPorts ι κ)) where
  agent := (Equiv.sumEmpty N.Agent Empty : N.Agent ⊕ (idNet S κ).Agent ≃ N.Agent)
  wire := (Equiv.refl _).sumCongr rightPortsEquiv
  label_agent := glueIdNet_label N
  link_map := glue_link_ext _ _ (glueIdNetPort N) (fun q => by
    rw [glueIdNetPort_inl, glueIdNetPort_inl]
    exact link_ext q) (glueIdNetPort_link_inr N)

/-- The identity net is a right unit for gluing, up to `≈`. -/
theorem glue_idNet : N.glue (idNet S κ) ≈ N :=
  Setoid.trans (glueIdNetIso N).equiv (extend_equiv _ _ _)

end right

end unit

end Net

module

public import LeanInets.Glue
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option

/-!
# Connections between terminal ports

The *terminal* ports of a net are its free ports and the ports of its agents, i.e. all ports
except the ends of wires. Starting at a terminal port, follow its link; whenever this reaches
an end of a wire, pass through the wire and follow the link of its other end. This always
ends at another terminal port, to which the first one is *connected*.

Connections are what matters about a net: two nets that differ only in their wires (chains
of wires, the orientation of wires, closed loops of wires) have the same connections.
-/

@[expose] public section

namespace Net

variable {S : Signature} {ι : Type} (N : Net S ι)

/-! ### Terminal ports -/

/-- The terminal ports of `N`: its free ports and agent ports. -/
abbrev TPort := _root_.Port N.label Empty ι

/-- A terminal port as a port of `N`. -/
def tport (x : N.TPort) : N.Port := x.map id (fun _ => rfl) Empty.elim id

variable {N}

@[simp] theorem tport_free (i : ι) : N.tport (.free i) = .free i := rfl
@[simp] theorem tport_pri (a : N.Agent) : N.tport (.pri a) = .pri a := rfl
@[simp] theorem tport_aux (a : N.Agent) (k) : N.tport (.aux a k) = .aux a k := rfl

theorem tport_injective : Function.Injective N.tport :=
  Port.map_injective id (fun _ => rfl) Empty.elim id Function.injective_id (fun a => a.elim)
    Function.injective_id

theorem tport_ne_wire (x : N.TPort) (w : N.Wire) (s : Side) : N.tport x ≠ .wire w s := by
  rcases x with _ | _ | _ | ⟨⟨⟩, _⟩ <;> nofun

/-- Every port that is not the end of a wire is terminal. -/
theorem exists_tport (p : N.Port) (h : ∀ w s, p ≠ .wire w s) : ∃ x, p = N.tport x := by
  rcases p with i | a | ⟨a, k⟩ | ⟨w, s⟩
  · exact ⟨.free i, rfl⟩
  · exact ⟨.pri a, rfl⟩
  · exact ⟨.aux a k, rfl⟩
  · exact absurd rfl (h w s)

/-! ### Passing through wires -/

variable (N) in
/-- Passing through a wire: from one end of a wire to the port linked to its other end. -/
def Step : N.Port → N.Port → Prop
  | .free _, _ => False
  | .pri _, _ => False
  | .aux _ _, _ => False
  | .wire w s, q => q = N.link (.wire w s.flip)

theorem step_wire (w : N.Wire) (s : Side) : N.Step (.wire w s) (N.link (.wire w s.flip)) := rfl

theorem Step.eq {p q : N.Port} (h : N.Step p q) :
    ∃ w s, p = .wire w s ∧ q = N.link (.wire w s.flip) := by
  cases p with
  | wire w s => exact ⟨w, s, rfl, h⟩
  | _ => exact h.elim

theorem not_step_tport (x : N.TPort) (q : N.Port) : ¬ N.Step (N.tport x) q := fun h => by
  obtain ⟨w, s, h, -⟩ := h.eq
  exact tport_ne_wire x w s h

theorem step_rightUnique : Relator.RightUnique N.Step := fun p q q' h h' => by
  obtain ⟨w, s, rfl, rfl⟩ := h.eq
  exact h'.symm

/-- Passing through a wire, backwards. -/
theorem Step.reverse {p q : N.Port} (h : N.Step p q) : N.Step (N.link q) (N.link p) := by
  obtain ⟨w, s, rfl, rfl⟩ := h.eq
  rw [N.link_link]
  show _ = N.link (.wire w s.flip.flip)
  rw [Side.flip_flip]

theorem reflTransGen_step_reverse {p q : N.Port} (h : Relation.ReflTransGen N.Step p q) :
    Relation.ReflTransGen N.Step (N.link q) (N.link p) := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.head hbc.reverse

/-! ### Connections -/

variable (N) in
/-- Following the link of `x` and passing through wires leads to `y`. -/
def Conn (x y : N.TPort) : Prop :=
  Relation.ReflTransGen N.Step (N.link (N.tport x)) (N.tport y)

theorem Conn.symm {x y : N.TPort} (h : N.Conn x y) : N.Conn y x := by
  have := reflTransGen_step_reverse h
  rwa [N.link_link] at this

/-- Each terminal port is connected to at most one terminal port. -/
theorem Conn.unique {x y z : N.TPort} (hy : N.Conn x y) (hz : N.Conn x z) : y = z := by
  have stuck {u v : N.TPort} (h : Relation.ReflTransGen N.Step (N.tport u) (N.tport v)) :
      u = v := by
    rcases h.cases_head with h | ⟨c, hc, -⟩
    · exact tport_injective h
    · exact absurd hc (not_step_tport u c)
  rcases Relation.ReflTransGen.total_of_right_unique step_rightUnique hy hz with h | h
  exacts [stuck h, (stuck h).symm]

/-- The partner of a wire end after passing through its wire. -/
def throughWire : N.Port → N.Port
  | .wire w s => N.link (.wire w s.flip)
  | p => p

/-- The wire end of a port, if it is one. -/
def wireEnd : N.Port → Option (N.Wire × Side)
  | .wire w s => some (w, s)
  | _ => none

/-- Each terminal port is connected to some terminal port: the walk through wires cannot go
on forever, since it never visits a wire end twice. -/
theorem Conn.exists (x : N.TPort) : ∃ y, N.Conn x y := by
  by_contra hne
  set a := N.link (N.tport x)
  have wireEnd_of_reach {p} (hp : Relation.ReflTransGen N.Step a p) : ∃ w s, p = .wire w s := by
    by_contra h
    obtain ⟨y, rfl⟩ := exists_tport p fun w s e => h ⟨w, s, e⟩
    exact hne ⟨y, hp⟩
  -- The walk `a, throughWire a, throughWire (throughWire a), ...` only visits wire ends.
  have reach (n : ℕ) : Relation.ReflTransGen N.Step a (throughWire^[n] a) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      obtain ⟨w, s, hw⟩ := wireEnd_of_reach ih
      rw [Function.iterate_succ_apply']
      refine ih.tail ?_
      rw [hw]
      exact step_wire w s
  -- It never revisits a wire end.
  have ne (i j : ℕ) (hij : i < j) : throughWire^[i] a ≠ throughWire^[j] a := by
    induction i generalizing j with
    | zero =>
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨w, s, hw⟩ := wireEnd_of_reach (reach j)
      rw [Function.iterate_succ_apply', hw]
      intro h
      exact tport_ne_wire x w s.flip (N.link_injective h)
    | succ i ih =>
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨w, s, hw⟩ := wireEnd_of_reach (reach i)
      obtain ⟨w', s', hw'⟩ := wireEnd_of_reach (reach j)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hw, hw']
      intro h
      have h := N.link_injective h
      simp only [Port.wire.injEq] at h
      apply ih j (by omega)
      rw [hw, hw', h.1, (by simpa using congrArg Side.flip h.2 : s = s')]
  have inj : Function.Injective fun n => wireEnd (throughWire^[n] a) := by
    intro i j h
    by_contra hij
    obtain ⟨w, s, hw⟩ := wireEnd_of_reach (reach i)
    obtain ⟨w', s', hw'⟩ := wireEnd_of_reach (reach j)
    simp only [hw, hw', wireEnd, Option.some.injEq, Prod.mk.injEq] at h
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · exact ne i j hlt (by rw [hw, hw', h.1, h.2])
    · exact ne j i hlt (by rw [hw, hw', h.1, h.2])
  exact not_injective_infinite_finite _ inj

/-- Connections are preserved by maps of ports that pass through wires. -/
theorem reflTransGen_map {ι' : Type} {M : Net S ι'} (f : N.Port → M.Port)
    (hf : ∀ p q, N.Step p q → M.Step (f p) (f q)) {p q : N.Port}
    (h : Relation.ReflTransGen N.Step p q) : Relation.ReflTransGen M.Step (f p) (f q) :=
  Relation.ReflTransGen.lift f hf p q h

/-- A bijection of terminal ports that maps connections to connections also reflects them. -/
theorem conn_reflect {ι' : Type} {M : Net S ι'} (f : N.TPort → M.TPort)
    (hf : Function.Injective f) (h : ∀ x y, N.Conn x y → M.Conn (f x) (f y)) {x y : N.TPort}
    (hxy : M.Conn (f x) (f y)) : N.Conn x y := by
  obtain ⟨z, hz⟩ := Conn.exists x
  rwa [hf (hxy.unique (h x z hz))]

end Net

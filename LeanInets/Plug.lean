module

public import LeanInets.Trace

/-!
# Plugging and gluing

Plugging and gluing are derived from union and trace:

* `C.plug R` plugs a net `R : Net S κ` into the hole `κ` of a context `C : Net S (ι ⊕ κ)`: it is
  the trace of `C.union R`, connecting each hole port of `C` with the corresponding free port of
  `R`.
* `N.glue M` connects a net `N` with interface `ι ⊕ κ` to a net `M` with interface `κ ⊕ ι'`
  along `κ`; it is a trace of `N.union M` as well. It is used to compose contexts.

The structural laws of plugging follow from those of union and trace: plugging respects
isomorphism (`Iso.plug`), plugging into a plugged net is plugging into the glued context
(`plugPlug`), and plugging twice into a context with two holes is plugging the union of the two
nets (`plugUnion`).
-/

@[expose] public section

namespace Net

variable {S : Signature}

/-- An isomorphism between nets with the same interface that is the identity on the interface
gives an isomorphism of their traces. -/
def Iso.traceSelf {ι κ : Type} {N N' : Net S ((ι ⊕ κ) ⊕ κ)} (e : Iso N N')
    (h : ∀ x, e.iface x = x := by iface_rfl) : Iso N.trace N'.trace :=
  e.trace (σ := .refl _) (τ := .refl _) fun x => by rw [h]; rcases x with (_ | _) | _ <;> rfl

/-! ### Plugging -/

section plug

variable {ι κ : Type}

/-- Plug the net `R` into the context `C`: connect the hole ports `inr k` of `C` with the free
ports `k` of `R`. -/
abbrev plug (C : Net S (ι ⊕ κ)) (R : Net S κ) : Net S ι := (C.union R).trace

namespace Plug

variable (C : Net S (ι ⊕ κ)) (R : Net S κ)

/-- Where a port of the context ends up in `C.plug R`. -/
def inl (q : C.Port) : (C.plug R).Port := Trace.back (C.union R) (Union.inl C R q)

/-- Where a port of the plugged net ends up in `C.plug R`. -/
def inr (q : R.Port) : (C.plug R).Port := Trace.back (C.union R) (Union.inr C R q)

theorem link_inl (q : C.Port) : (C.plug R).link (inl C R q) = inl C R (C.link q) := by
  unfold inl
  rw [trace_link_back, union_link_inl]

theorem link_inr (q : R.Port) : (C.plug R).link (inr C R q) = inr C R (R.link q) := by
  unfold inr
  rw [trace_link_back, union_link_inr]

theorem inl_free_inl (i : ι) : inl C R (.free (.inl i)) = .free i := rfl

theorem inl_free_inr (k : κ) : inl C R (.free (.inr k)) = inr C R (R.link (.free k)) := by
  unfold inr
  rw [← union_link_inr]
  exact Trace.back_free_inl_inr _ k

theorem inr_free (k : κ) : inr C R (.free k) = inl C R (C.link (.free (.inr k))) := by
  unfold inl
  rw [← union_link_inl]
  exact Trace.back_free_inr _ k

theorem link_free (i : ι) : (C.plug R).link (.free i) = inl C R (C.link (.free (.inl i))) := by
  rw [← inl_free_inl C R i, link_inl]

/-- Every port of a plugged net comes from the context or from the plugged net. -/
theorem cases (p : (C.plug R).Port) : (∃ q, p = inl C R q) ∨ ∃ q, p = inr C R q := by
  rw [← Trace.back_up (C.union R) p]
  rcases Union.cases C R (Trace.up (C.union R) p) with ⟨q, hq⟩ | ⟨q, hq⟩
  · exact .inl ⟨q, by rw [hq]; rfl⟩
  · exact .inr ⟨q, by rw [hq]; rfl⟩

/-- To show that a map of ports out of a plugged net commutes with the links, it suffices to
check this on the ports of the two parts. -/
theorem link_ext {ι' : Type} {X : Net S ι'} (F : (C.plug R).Port → X.Port)
    (hl : ∀ q, X.link (F (inl C R q)) = F (inl C R (C.link q)))
    (hr : ∀ q, X.link (F (inr C R q)) = F (inr C R (R.link q)))
    (p : (C.plug R).Port) : X.link (F p) = F ((C.plug R).link p) := by
  rcases cases C R p with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · rw [hl, link_inl]
  · rw [hr, link_inr]

end Plug

variable {ι' κ' : Type} {C : Net S (ι ⊕ κ)} {C' : Net S (ι' ⊕ κ')} {R : Net S κ} {R' : Net S κ'}

/-- Plugging respects isomorphism, if the isomorphism of contexts maps the hole along the
isomorphism of the plugged nets. -/
def Iso.plug (e : Iso C C') (f : Iso R R') (σ : ι ≃ ι')
    (he : ∀ x, e.iface x = Equiv.sumCongr σ f.iface x := by iface_rfl) :
    Iso (C.plug R) (C'.plug R') :=
  (e.union f).trace (σ := σ) (τ := f.iface) fun x => by
    rcases x with (i | k) | k
    · exact congrArg Sum.inl (he (.inl i))
    · exact congrArg Sum.inl (he (.inr k))
    · rfl

end plug

/-! ### Gluing -/

section glue

variable {ι κ ι' : Type}

/-- Arranging the interface of `N.union M` for gluing along `κ`. -/
def glueEquiv (ι κ ι' : Type) : (ι ⊕ κ) ⊕ (κ ⊕ ι') ≃ ((ι ⊕ ι') ⊕ κ) ⊕ κ where
  toFun
    | .inl (.inl i) => .inl (.inl (.inl i))
    | .inl (.inr k) => .inl (.inr k)
    | .inr (.inl k) => .inr k
    | .inr (.inr j) => .inl (.inl (.inr j))
  invFun
    | .inl (.inl (.inl i)) => .inl (.inl i)
    | .inl (.inl (.inr j)) => .inr (.inr j)
    | .inl (.inr k) => .inl (.inr k)
    | .inr k => .inr (.inl k)
  left_inv x := by rcases x with (_ | _) | (_ | _) <;> rfl
  right_inv x := by rcases x with ((_ | _) | _) | _ <;> rfl

/-- Glue `N` and `M` along `κ`: connect the free port `inr k` of `N` with the free port `inl k`
of `M`. -/
abbrev glue (N : Net S (ι ⊕ κ)) (M : Net S (κ ⊕ ι')) : Net S (ι ⊕ ι') :=
  ((N.union M).reindex (glueEquiv ι κ ι')).trace

end glue

/-! ### Plugging twice -/

section plugUnion

variable {ι κ₁ κ₂ : Type} (D : Net S ((ι ⊕ κ₁) ⊕ κ₂)) (X : Net S κ₁) (Y : Net S κ₂)

/-- Plugging `Y` and then `X` into a context with two holes is plugging their union. -/
def plugUnion :
    Iso ((D.plug Y).plug X) ((D.reindex (Equiv.sumAssoc ι κ₁ κ₂)).plug (X.union Y)) :=
  (traceUnion (D.union Y) X).traceSelf.trans <| (traceTrace _).trans <|
    Iso.traceSelf ((reindexIso _ _).symm.trans <| (reindexIso _ _).symm.trans <|
      (unionAssoc D Y X).trans ((reindexIso _ D).union (unionComm Y X)))

end plugUnion

section plugPlug

variable {ι κ H : Type} (C : Net S (ι ⊕ κ)) (C' : Net S (κ ⊕ H)) (X : Net S H)

/-- Plugging into a plugged net is plugging into the glued context. -/
def plugPlug : Iso (C.plug (C'.plug X)) ((C.glue C').plug X) :=
  let ρ : ((κ ⊕ (ι ⊕ κ)) ⊕ H) ⊕ H ≃ (((ι ⊕ κ) ⊕ κ) ⊕ H) ⊕ H :=
    .sumCongr (.sumCongr (Equiv.sumComm _ _) (.refl _)) (.refl _)
  -- Move the inner trace of the left-hand side outwards.
  let a : Iso (C.union (C'.plug X)) (((((C'.union X).union C).reindex
      (traceUnionEquiv κ H (ι ⊕ κ))).reindex ρ).trace) :=
    (unionComm C _).trans <| (traceUnion (C'.union X) C).trans <|
      (reindexIso ρ _).trace (σ := Equiv.sumComm _ _) (τ := .refl _) (by iface_rfl)
  a.traceSelf.trans <| (traceTrace _).trans <|
    (Iso.trace (σ := .refl _) (τ := Equiv.sumComm _ _)
      ((reindexIso _ _).symm.trans <| (reindexIso _ _).symm.trans <| (reindexIso _ _).symm.trans <|
        (unionComm _ C).trans <| (unionAssoc C C' X).symm.trans <|
          ((reindexIso _ (C.union C')).union (.refl X)).trans <|
            (reindexIso _ _).trans (reindexIso _ _)) (by iface_rfl)).trans <|
    (traceTrace _).symm.trans (traceUnion _ X).traceSelf.symm

end plugPlug

end Net

module

public import LeanInets.Reduction
public import LeanInets.Context

/-!
# Confluence

Reduction is strongly confluent modulo `≈` (`InteractionSystem.Step.strong_confluence`): if `N`
reduces in one step to `N₁` and to `N₂`, then either `N₁ ≈ N₂`, or both reduce in one step to a
common net. The two steps either reduce the same active pair, possibly seen from the other side,
or two disjoint active pairs, which can be reduced in either order.

Consequences:
* Church–Rosser (`InteractionSystem.Reduces.church_rosser`): two reducts of a net reduce to a
  common net.
* Uniqueness of normal forms (`InteractionSystem.Reduces.normal_unique`).
* All reductions of a net to normal form have the same length
  (`InteractionSystem.ReducesIn.length_eq`), and if a net has a normal form reached in `n` steps,
  then no reduction of it is longer than `n` steps (`InteractionSystem.ReducesIn.le_of_normal`).
-/

@[expose] public section

namespace InteractionSystem

open Net

variable {S : Signature} {I : InteractionSystem S} {ι : Type}

/-! ### Strong confluence -/

/-- The active pair in a decomposition `N ≈ C.plug (α ⋈ β)`. -/
theorem exists_activePair_of_wireIso {N : Net S ι} {α β : S.Sym}
    {C : Net S (ι ⊕ (Fin (S.arity α) ⊕ Fin (S.arity β)))}
    (e : WireIso N (C.plug (activePair α β))) :
    ∃ a b, e.agent a = .inr .left ∧ e.agent b = .inr .right ∧ N.IsActivePairW a b ∧
      N.label a = α ∧ N.label b = β := by
  refine ⟨e.agent.symm (.inr .left), e.agent.symm (.inr .right), e.agent.apply_symm_apply _,
    e.agent.apply_symm_apply _, ?_, (e.symm.label_agent (.inr .left)),
    (e.symm.label_agent (.inr .right))⟩
  exact e.symm.isActivePairW_iff.mpr (isActivePair_plug_activePair C).isActivePairW

/-- Reduction is strongly confluent modulo `≈`. -/
theorem Step.strong_confluence {N N₁ N₂ : Net S ι} (h₁ : I.Step N N₁) (h₂ : I.Step N N₂) :
    N₁ ≈ N₂ ∨ ∃ N₃, I.Step N₁ N₃ ∧ I.Step N₂ N₃ := by
  obtain ⟨α₁, β₁, R₁, C₁, hR₁, ⟨e₁⟩, hN₁⟩ := h₁
  obtain ⟨α₂, β₂, R₂, C₂, hR₂, ⟨e₂⟩, hN₂⟩ := h₂
  obtain ⟨a₁, b₁, ea₁, eb₁, p₁, la₁, lb₁⟩ := exists_activePair_of_wireIso e₁
  obtain ⟨a₂, b₂, ea₂, eb₂, p₂, la₂, lb₂⟩ := exists_activePair_of_wireIso e₂
  have hsymm₁ (t) : e₁.agent.symm (.inr t) = match t with | .left => a₁ | .right => b₁ := by
    cases t
    exacts [e₁.agent.symm_apply_eq.mpr ea₁.symm, e₁.agent.symm_apply_eq.mpr eb₁.symm]
  -- The two active pairs are equal, swapped, or disjoint.
  have cases : (a₂ = a₁ ∧ b₂ = b₁) ∨ (a₂ = b₁ ∧ b₂ = a₁) ∨
      ∃ c d, e₁.agent a₂ = .inl c ∧ e₁.agent b₂ = .inl d := by
    rcases hc : e₁.agent a₂ with c | (_ | _)
    · rcases hd : e₁.agent b₂ with d | (_ | _)
      · exact .inr (.inr ⟨c, d, rfl, rfl⟩)
      · have hb : b₂ = a₁ := e₁.agent.injective (hd.trans ea₁.symm)
        rw [hb] at p₂
        rw [← p₁.unique p₂.symm, eb₁] at hc
        cases hc
      · have hb : b₂ = b₁ := e₁.agent.injective (hd.trans eb₁.symm)
        rw [hb] at p₂
        rw [← p₁.symm.unique p₂.symm, ea₁] at hc
        cases hc
    · obtain rfl : a₂ = a₁ := e₁.agent.injective (hc.trans ea₁.symm)
      exact .inl ⟨rfl, p₂.unique p₁⟩
    · obtain rfl : a₂ = b₁ := e₁.agent.injective (hc.trans eb₁.symm)
      exact .inr (.inl ⟨rfl, p₂.unique p₁.symm⟩)
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨c, d, hc, hd⟩
  · -- The same active pair: the contexts agree, and so do the rules.
    subst la₁ lb₁
    subst la₂ lb₂
    obtain rfl := Option.some.inj (hR₁.symm.trans hR₂)
    refine .inl (Setoid.trans hN₁ (Setoid.trans ?_ (Setoid.symm hN₂)))
    refine plug_equiv (WireIso.equiv (.ofPlugActivePair (e₁.symm.trans e₂) fun t => ?_))
      (Setoid.refl _)
    change e₂.agent (e₁.agent.symm (.inr t)) = _
    rw [hsymm₁]
    cases t
    exacts [ea₂, eb₂]
  · -- The same active pair, seen from the other side: use the symmetry of the rules.
    subst la₁ lb₁
    subst la₂ lb₂
    obtain ⟨M, hM, hMR⟩ := I.rule_swap _ _ R₁ hR₁
    obtain rfl := Option.some.inj (hR₂.symm.trans hM)
    let f := e₁.symm.trans (e₂.trans (((WireIso.refl C₂).plug
      (activePairSwap _ _).symm.wireIso).trans
        (plugReindex C₂ (activePair _ _) (Equiv.sumComm _ _)).wireIso))
    have hf : ∀ t, f.agent (.inr t) = .inr t := fun t => by
      change (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _) ActivePair.Agent.swap.symm)
        (e₂.agent (e₁.agent.symm (.inr t)))) = _
      rw [hsymm₁]
      cases t
      · rw [eb₂]
        rfl
      · rw [ea₂]
        rfl
    refine .inl (Setoid.trans hN₁ (Setoid.trans ?_ (Setoid.symm hN₂)))
    refine Setoid.trans (plug_equiv (WireIso.ofPlugActivePair f hf).equiv (Setoid.refl _)) ?_
    refine Setoid.trans (plugReindex C₂ R₁ (Equiv.sumComm _ _)).symm.equiv ?_
    exact plug_equiv (Setoid.refl _) (Setoid.symm hMR)
  · -- Disjoint active pairs: cut the second one out of the context of the first, and reduce
    -- them in either order.
    have pc : C₁.IsActivePairW c d := by
      rw [← isActivePairW_plug_activePair_iff (α := α₁) (β := β₁), ← hc, ← hd]
      exact e₁.isActivePairW_iff.mpr p₂
    have lc : C₁.label c = α₂ := by
      have := e₁.label_agent a₂
      rw [hc] at this
      exact this.trans la₂
    have ld : C₁.label d = β₂ := by
      have := e₁.label_agent b₂
      rw [hd] at this
      exact this.trans lb₂
    subst lc ld
    let g := wireIsoPlugRemovePair pc
    let D := C₁.removePair c d pc.1
    have hD : D.exchange.exchange ≈ D := (reindexReindex D _ _ sumRightComm_sumRightComm).equiv
    let f := e₂.symm.trans ((e₁.trans (g.plug (.refl _))).trans (plugExchange D _ _).wireIso)
    have hf : ∀ t, f.agent (.inr t) = .inr t := fun t => by
      change sumRightComm _ _ _
        (Equiv.sumCongr g.agent (Equiv.refl _) (e₁.agent (e₂.agent.symm (.inr t)))) = _
      cases t
      · rw [e₂.agent.symm_apply_eq.mpr ea₂.symm, hc]
        change sumRightComm _ _ _ (.inl (RemovePair.classify c)) = _
        rw [RemovePair.classify_a]
        rfl
      · rw [e₂.agent.symm_apply_eq.mpr eb₂.symm, hd]
        change sumRightComm _ _ _ (.inl (RemovePair.classify d)) = _
        rw [RemovePair.classify_b pc.1]
        rfl
    have hC₂ := (WireIso.ofPlugActivePair f hf).equiv
    refine .inr ⟨(D.plug R₂).plug R₁, ?_, ?_⟩
    · refine Step.of_equiv (step_plug hR₂ (D.exchange.plug R₁)) (Setoid.symm ?_) ?_
      · exact Setoid.trans hN₁ (Setoid.trans (plug_equiv g.equiv (Setoid.refl _))
          (plugExchange D _ _).equiv)
      · exact Setoid.trans (plugExchange D.exchange _ _).equiv
          (plug_equiv (plug_equiv hD (Setoid.refl _)) (Setoid.refl _))
    · refine Step.of_equiv (step_plug hR₁ (D.plug R₂)) (Setoid.symm ?_) (Setoid.refl _)
      exact Setoid.trans hN₂ (Setoid.trans (plug_equiv hC₂ (Setoid.refl _))
        (Setoid.trans (plugExchange D.exchange _ _).equiv
          (plug_equiv (plug_equiv hD (Setoid.refl _)) (Setoid.refl _))))

/-! ### Church–Rosser -/

variable (I) in
/-- Reduction steps between nets up to `≈`. -/
def QStep : Quotient (Net.setoid S ι) → Quotient (Net.setoid S ι) → Prop :=
  Quotient.lift₂ I.Step fun _ _ _ _ h h' => propext (step_congr h h')

theorem qStep_mk {N N' : Net S ι} : I.QStep ⟦N⟧ ⟦N'⟧ ↔ I.Step N N' := Iff.rfl

/-- Multi-step reduction is reflexive transitive closure of reduction steps up to `≈`. -/
theorem reduces_iff_reflTransGen_qStep {N N' : Net S ι} :
    I.Reduces N N' ↔ Relation.ReflTransGen I.QStep ⟦N⟧ ⟦N'⟧ := by
  constructor
  · rintro ⟨M, hM, hMN'⟩
    rw [← Quotient.sound hMN']
    exact Relation.ReflTransGen.lift _ (fun _ _ h => qStep_mk.mpr h) _ _ hM
  · intro h
    obtain ⟨q, hq⟩ : ∃ q, q = (⟦N'⟧ : Quotient (Net.setoid S ι)) := ⟨_, rfl⟩
    rw [← hq] at h
    induction h generalizing N' with
    | refl => exact .of_equiv (Quotient.exact hq)
    | tail _ hstep ih =>
      rename_i b _ _
      induction b using Quotient.inductionOn with | h B =>
      rw [hq] at hstep
      exact (ih rfl).tail (qStep_mk.mp hstep)

theorem qStep_strong_confluence {x y z : Quotient (Net.setoid S ι)} (hy : I.QStep x y)
    (hz : I.QStep x z) : ∃ w, Relation.ReflGen I.QStep y w ∧ Relation.ReflTransGen I.QStep z w := by
  induction x using Quotient.inductionOn with | h N =>
  induction y using Quotient.inductionOn with | h N₁ =>
  induction z using Quotient.inductionOn with | h N₂ =>
  rcases Step.strong_confluence (qStep_mk.mp hy) (qStep_mk.mp hz) with h | ⟨N₃, h₁, h₂⟩
  · exact ⟨⟦N₂⟧, by rw [Quotient.sound h], .refl⟩
  · exact ⟨⟦N₃⟧, .single (qStep_mk.mpr h₁), .single (qStep_mk.mpr h₂)⟩

/-- Church–Rosser: two reducts of a net reduce to a common net. -/
theorem Reduces.church_rosser {N N₁ N₂ : Net S ι} (h₁ : I.Reduces N N₁) (h₂ : I.Reduces N N₂) :
    ∃ N₃, I.Reduces N₁ N₃ ∧ I.Reduces N₂ N₃ := by
  rw [reduces_iff_reflTransGen_qStep] at h₁ h₂
  obtain ⟨w, h₁, h₂⟩ := Relation.church_rosser (fun _ _ _ => qStep_strong_confluence) h₁ h₂
  induction w using Quotient.inductionOn with | h N₃ =>
  exact ⟨N₃, reduces_iff_reflTransGen_qStep.mpr h₁, reduces_iff_reflTransGen_qStep.mpr h₂⟩

/-- A net in normal form only reduces to itself, up to `≈`. -/
theorem Normal.equiv_of_reduces {N N' : Net S ι} (hN : I.Normal N) (h : I.Reduces N N') :
    N ≈ N' := by
  obtain ⟨M, hM, hMN'⟩ := h
  rcases hM.cases_head with rfl | ⟨K, hK, -⟩
  · exact hMN'
  · exact absurd hK (hN K)

/-- Normal forms are unique up to `≈`. -/
theorem Reduces.normal_unique {N N₁ N₂ : Net S ι} (h₁ : I.Reduces N N₁) (h₂ : I.Reduces N N₂)
    (hN₁ : I.Normal N₁) (hN₂ : I.Normal N₂) : N₁ ≈ N₂ := by
  obtain ⟨N₃, h₁₃, h₂₃⟩ := h₁.church_rosser h₂
  exact Setoid.trans (hN₁.equiv_of_reduces h₁₃) (Setoid.symm (hN₂.equiv_of_reduces h₂₃))

/-! ### Lengths of reductions -/

variable (I) in
/-- `N` reduces to `N'` in exactly `n` steps, up to `≈`. -/
inductive ReducesIn : ℕ → Net S ι → Net S ι → Prop
  | zero {N N'} : N ≈ N' → ReducesIn 0 N N'
  | succ {n N M N'} : I.Step N M → ReducesIn n M N' → ReducesIn (n + 1) N N'

theorem ReducesIn.of_equiv {n : ℕ} {N M N' : Net S ι} (h : I.ReducesIn n N N') (hN : N ≈ M) :
    I.ReducesIn n M N' := by
  cases h with
  | zero h => exact .zero (Setoid.trans (Setoid.symm hN) h)
  | succ hs h => exact .succ (hs.of_equiv hN (Setoid.refl _)) h

theorem ReducesIn.reduces {n : ℕ} {N N' : Net S ι} (h : I.ReducesIn n N N') : I.Reduces N N' := by
  induction h with
  | zero h => exact .of_equiv h
  | succ hs _ ih => exact ih.head hs

theorem Reduces.exists_reducesIn {N N' : Net S ι} (h : I.Reduces N N') :
    ∃ n, I.ReducesIn n N N' := by
  obtain ⟨M, hM, hMN'⟩ := h
  induction hM using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .zero hMN'⟩
  | head hs _ ih =>
    obtain ⟨n, h⟩ := ih
    exact ⟨n + 1, .succ hs h⟩

theorem reduces_iff_exists_reducesIn {N N' : Net S ι} :
    I.Reduces N N' ↔ ∃ n, I.ReducesIn n N N' :=
  ⟨Reduces.exists_reducesIn, fun ⟨_, h⟩ => h.reduces⟩

/-- A net in normal form only reduces in zero steps. -/
theorem Normal.reducesIn {n : ℕ} {N N' : Net S ι} (hN : I.Normal N) (h : I.ReducesIn n N N') :
    n = 0 ∧ N ≈ N' := by
  cases h with
  | zero h => exact ⟨rfl, h⟩
  | succ hs _ => exact absurd hs (hN _)

/-- If `N` reaches a normal form `N₁` in `n` steps, then every reduction of `N` takes at most `n`
steps, and can be continued to `N₁` in the remaining steps. -/
theorem ReducesIn.le_of_normal {n m : ℕ} {N N₁ N₂ : Net S ι} (h₁ : I.ReducesIn n N N₁)
    (hN₁ : I.Normal N₁) (h₂ : I.ReducesIn m N N₂) : m ≤ n ∧ I.ReducesIn (n - m) N₂ N₁ := by
  induction n generalizing N m N₂ with
  | zero =>
    cases h₁ with | zero h₁ =>
    cases h₂ with
    | zero h₂ => exact ⟨le_rfl, .zero (Setoid.trans (Setoid.symm h₂) h₁)⟩
    | succ hs _ => exact absurd (hs.of_equiv h₁ (Setoid.refl _)) (hN₁ _)
  | succ n ih =>
    cases h₁ with | @succ _ _ A _ hA h₁ =>
    cases h₂ with
    | zero h₂ => exact ⟨Nat.zero_le _, (ReducesIn.succ hA h₁).of_equiv h₂⟩
    | @succ m _ B _ hB h₂ =>
      rcases hA.strong_confluence hB with hAB | ⟨C, hAC, hBC⟩
      · obtain ⟨hle, h⟩ := ih h₁ (h₂.of_equiv (Setoid.symm hAB))
        exact ⟨Nat.succ_le_succ hle, by rwa [Nat.add_sub_add_right]⟩
      · obtain ⟨hle, hC⟩ := ih h₁ (ReducesIn.succ hAC (.zero (Setoid.refl C)))
        have hB' : I.ReducesIn n B N₁ := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
          rw [Nat.add_sub_cancel_left] at hC
          rw [Nat.add_comm]
          exact .succ hBC hC
        obtain ⟨hle', h⟩ := ih hB' h₂
        exact ⟨Nat.succ_le_succ hle', by rwa [Nat.add_sub_add_right]⟩

/-- All reductions of a net to normal form have the same length, and end in the same normal form
up to `≈`. -/
theorem ReducesIn.length_eq {n m : ℕ} {N N₁ N₂ : Net S ι} (h₁ : I.ReducesIn n N N₁)
    (hN₁ : I.Normal N₁) (h₂ : I.ReducesIn m N N₂) (hN₂ : I.Normal N₂) : n = m ∧ N₁ ≈ N₂ := by
  obtain ⟨hle, h⟩ := h₁.le_of_normal hN₁ h₂
  obtain ⟨h0, hN⟩ := hN₂.reducesIn h
  exact ⟨by omega, Setoid.symm hN⟩

end InteractionSystem

# Plan

## Design

- A **signature** gives symbols with the number of auxiliary ports; every agent also has one
  principal port.
- A **net** has two kinds of entities, *agents* and *wires* (two ports, no principal port),
  plus an interface `ι` of free ports.
- **Ports** are an inductive type: `free i`, `pri a`, `aux a k`, `wire w s` (with
  `s : Side`).
- **Wiring** is a fixed-point-free involution `link` on ports. Free ports may only be linked
  to entity ports, so gluing nets never creates chains of free ports that would need to be
  followed.
- Because wires are explicit, `a — w — b` and `a — b` are different nets. They are
  identified by an equivalence `≈` that contracts wires. Isomorphism stays strict (no wire
  flipping); wire orientation is handled by `≈` as well.

## Milestones

0. [x] Project setup: Lake + Mathlib.
   - [ ] CI workflow (`.github/workflows/ci.yml` using `leanprover/lean-action`).
1. [x] Signatures, ports, nets, active pairs; example nets.
2. [x] Isomorphism of nets (`Equiv` on agents and on wires, preserving labels and links,
   identity on the interface); setoid.
3. [ ] Gluing nets along their interfaces; algebra of gluing up to iso (associativity,
   commutativity, unit).
4. [ ] Wire contraction and the equivalence `≈` (iso + contraction).
5. [ ] Interaction systems: rules for pairs of symbols (RHS net with interface
   `Fin (arity α) ⊕ Fin (arity β)`), at most one rule per pair, symmetry.
6. [ ] Reduction: `N ⟶ N'` iff `N ≈ glue C (α ⋈ β)` and `N' ≈ glue C rhs`; multi-step
   reduction via `Relation.ReflTransGen`.
7. [ ] Metatheory: strong confluence modulo `≈`; Church–Rosser, uniqueness of normal forms,
   equal length of normalising reductions.
8. [ ] More examples: unary arithmetic rules, erasure/duplication, interaction combinators
   `γ, δ, ε`.

## Possible extensions

- Interaction calculus (term syntax) and its correspondence with the graph semantics.
- Executable reducer proven correct against the reduction relation.
- Universality of interaction combinators.
- Encodings of λ-calculus / linear logic.

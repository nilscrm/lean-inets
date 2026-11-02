# Plan

## Design

- A **signature** gives symbols with the number of auxiliary ports; every agent also has one
  principal port.
- A **net** has two kinds of entities, *agents* and *wires* (two ports, no principal port),
  plus an interface `ι` of free ports.
- **Ports** are an inductive type: `free i`, `pri a`, `aux a k`, `wire w s` (with
  `s : Side`).
- **Wiring** is a fixed-point-free involution `link` on ports. Free ports may only be linked
  to entity ports, so connecting free ports never creates chains of free ports that would need
  to be followed.
- **Building nets** uses two primitives: the disjoint union `N.union M` (no links between the
  parts) and the trace `N.trace` (for `N : Net S ((ι ⊕ κ) ⊕ κ)`, connect the free ports
  `inl (inr k)` and `inr k`). Plugging a net into a context, `C.plug R := (C.union R).trace`,
  and gluing nets along a common interface are derived from them.
- **Isomorphisms** carry a bijection of interfaces, so the structural laws of union and trace
  can be stated without reindexing by hand. Isomorphism stays strict about wires (no wire
  flipping). Both kinds of isomorphism extend a `Renaming` (label-preserving bijections of
  agents and interfaces).
- Because wires are explicit, `a — w — b` and `a — b` are different nets. The equivalence `≈`
  is *isomorphism up to wires*: label-preserving bijections of agents and interfaces that map
  *partners* to partners, and that are the identity on the interface. The partner of a
  terminal port (free port or agent port) is the terminal port at the other end of its path
  of links and wires. Chains of wires, wire orientation and closed loops of wires are
  invisible to `≈`.

## Milestones

0. [x] Project setup: Lake + Mathlib.
   - [ ] CI workflow (`.github/workflows/ci.yml` using `leanprover/lean-action`).
1. [x] Signatures, ports, nets, active pairs; example nets.
2. [x] Isomorphism of nets (`Equiv`s on agents, wires and interfaces, preserving labels and
   links); reindexing the interface.
3. [x] Union and trace: union respects isomorphism and is commutative and associative up to
   isomorphism (`unionComm`, `unionAssoc`); trace respects isomorphism (`Iso.trace`, which also
   renames the interface and the traced ports), superposing (`traceUnion`) and vanishing
   (`traceTrace`). Derived: plugging and gluing, `plugPlug` (plugging into a plugged net is
   plugging into the glued context) and `plugUnion` (plugging twice is plugging a union).
4. [x] Partners and the equivalence `≈` (isomorphism up to wires); union and trace respect it
   (`WireIso.union`, `WireIso.trace`, via chains of walks and jumps between traced ports), hence
   so do plugging, gluing and reindexing; plugging into the identity net of wires gives back
   the plugged net up to `≈` (`idNet_plug`).
5. [x] Interaction systems: the active pair `α ⋈ β` as a net (`activePair`, with
   `activePair α β ≅ activePair β α` swapping the interface); rules for pairs of symbols (RHS
   net with interface `Fin (arity α) ⊕ Fin (arity β)`), at most one rule per pair (`rule α β`
   is an `Option`), symmetry up to `≈` (the rule for `β ⋈ α` is the rule for `α ⋈ β` with its
   interface swapped, stated with `Option.Rel`). Example: the rules for unary addition.
6. [x] Reduction: `I.Step N N'` iff `N ≈ C.plug (α ⋈ β)` and `N' ≈ C.plug rhs` for a context
   `C : Net S (ι ⊕ κ)`; multi-step reduction `I.Reduces` (`Relation.ReflTransGen` of `Step`,
   followed by `≈`, so that zero steps relate equivalent nets); normal forms `I.Normal`.
   Redexes are exactly the active pairs up to wires (`IsActivePairW`: principal ports connected
   through wires) whose symbols have a rule (`exists_step_iff`). The hard direction cuts an
   active pair out of its net (`removePair`, `equiv_plug_removePair`).
7. [x] Metatheory: strong confluence modulo `≈` (`Step.strong_confluence`: the two steps
   reduce the same active pair, the same pair from the other side, or disjoint pairs);
   Church–Rosser (`Reduces.church_rosser`, via `Relation.church_rosser` on nets up to `≈`),
   uniqueness of normal forms (`Reduces.normal_unique`), equal length of normalising
   reductions (`ReducesIn.length_eq`), and no reduction is longer than a normalising one
   (`ReducesIn.le_of_normal`). The proof rests on contexts being determined by plugging in an
   active pair (`WireIso.ofPlugActivePair`) and on exchanging the two holes of a context
   (`plugExchange`, from `plugUnion`).
8. [x] More examples: unary arithmetic (`Z`, `S`, `add`, `mul`, eraser and duplicator for
   numerals); the interaction combinators `γ, δ, ε` (`Combinators.system`, every pair has a
   rule), with a complete three-step reduction to normal form. General lemmas added along the
   way: `step_activePair` (an active pair reduces to its rule), `Step.plug`/`Reduces.plug`
   (reduction is closed under contexts, via `plugPlug`).

## Possible extensions

- Interaction calculus (term syntax) and its correspondence with the graph semantics.
- Executable reducer proven correct against the reduction relation.
- Universality of interaction combinators.
- Encodings of λ-calculus / linear logic.

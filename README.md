# lean-inets

A formalisation of [interaction nets](https://doi.org/10.1145/96709.96718) (Lafont, 1990)
in Lean 4 with Mathlib.

## Layout

- `LeanInets/Signature.lean` – signatures (symbols with arities)
- `LeanInets/Port.lean` – ports: free ports, principal/auxiliary agent ports, wire ends
- `LeanInets/Net.lean` – nets and active pairs
- `LeanInets/Renaming.lean` – label-preserving bijections of agents and interfaces, shared by both kinds of isomorphism
- `LeanInets/Iso.lean` – isomorphism of nets (with a bijection of interfaces) and reindexing
- `LeanInets/Union.lean` – disjoint union of nets, commutative and associative up to isomorphism
- `LeanInets/Trace.lean` – the trace (connecting pairs of free ports): superposing and vanishing
- `LeanInets/Plug.lean` – plugging a net into a context and gluing nets, derived from union and trace
- `LeanInets/Connect.lean` – partners of terminal ports (paths of links and wires)
- `LeanInets/WireIso.lean` – isomorphism up to wires (the equivalence `≈`); union, trace,
  plugging and gluing respect it
- `LeanInets/Unit.lean` – plugging into the identity net gives back the plugged net up to `≈`
- `LeanInets/InteractionSystem.lean` – active pairs as nets, interaction rules and interaction systems
- `LeanInets/Decompose.lean` – active pairs up to wires, and cutting an active pair out of its net
- `LeanInets/Reduction.lean` – one-step and multi-step reduction, normal forms, and redexes
- `LeanInets/Context.lean` – exchanging the holes of a context, contexts are determined by the
  active pair plugged into them
- `LeanInets/Confluence.lean` – strong confluence, Church–Rosser, uniqueness of normal forms and
  equal length of normalising reductions
- `LeanInets/Examples.lean` – small example nets, the interaction system for unary arithmetic, and reductions
- `LeanInets/Combinators.lean` – Lafont's interaction combinators, with a complete reduction to normal form

See [PLAN.md](PLAN.md) for the roadmap.

## Building

```sh
lake exe cache get
lake build
```

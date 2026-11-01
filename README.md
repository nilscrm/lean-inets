# lean-inets

A formalisation of [interaction nets](https://doi.org/10.1145/96709.96718) (Lafont, 1990)
in Lean 4 with Mathlib.

## Layout

- `LeanInets/Signature.lean` – signatures (symbols with arities)
- `LeanInets/Port.lean` – ports: free ports, principal/auxiliary agent ports, wire ends
- `LeanInets/Net.lean` – nets and active pairs
- `LeanInets/Iso.lean` – isomorphism of nets
- `LeanInets/Glue.lean` – reindexing interfaces and gluing nets
- `LeanInets/Connect.lean` – connected ports (paths of links and wires) and partners of terminal ports
- `LeanInets/WireIso.lean` – isomorphism up to wires (the equivalence `≈`); gluing respects it
- `LeanInets/Unit.lean` – the identity net is a unit for gluing up to `≈`
- `LeanInets/InteractionSystem.lean` – active pairs as nets, interaction rules and interaction systems
- `LeanInets/Decompose.lean` – plugging a net into a context, active pairs up to wires, and
  cutting an active pair out of its net
- `LeanInets/Reduction.lean` – one-step and multi-step reduction, normal forms, and redexes
- `LeanInets/Context.lean` – plugging into contexts: renaming and exchanging holes, contexts are
  determined by the active pair plugged into them
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

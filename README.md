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
- `LeanInets/Examples.lean` – small example nets and the interaction system for unary addition

See [PLAN.md](PLAN.md) for the roadmap.

## Building

```sh
lake exe cache get
lake build
```

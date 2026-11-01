# lean-inets

A formalisation of [interaction nets](https://doi.org/10.1145/96709.96718) (Lafont, 1990)
in Lean 4 with Mathlib.

## Layout

- `LeanInets/Signature.lean` – signatures (symbols with arities)
- `LeanInets/Port.lean` – ports: free ports, principal/auxiliary agent ports, wire ends
- `LeanInets/Net.lean` – nets and active pairs
- `LeanInets/Examples.lean` – small example nets

See [PLAN.md](PLAN.md) for the roadmap.

## Building

```sh
lake exe cache get
lake build
```

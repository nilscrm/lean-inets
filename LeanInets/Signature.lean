module

/-!
# Signatures

A signature fixes the symbols agents can be labelled with, together with the number of
auxiliary ports of each symbol. Every agent additionally has exactly one principal port,
so an agent labelled `s` has `arity s + 1` ports in total.
-/

@[expose] public section

/-- A signature for interaction nets: a type of symbols and the number of auxiliary
ports of each symbol. -/
structure Signature where
  /-- The symbols agents can be labelled with. -/
  Sym : Type
  /-- The number of auxiliary ports of an agent with the given symbol. -/
  arity : Sym → Nat

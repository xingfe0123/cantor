# Cantor's Diagonal Argument in Rocq

A formal proof that the set of all infinite binary sequences (0-1 sequences) is uncountable, using Cantor's diagonal argument.

## Theorem

```
Theorem seq01_uncountable : ~ countable seq01.
```

where `seq01 := nat -> bool` and `countable X := exists f : X -> nat, injective f`.

## Proof Structure

| Statement | Type | Axioms |
|-----------|------|--------|
| `diagonal_not_in_range` | Constructive | None |
| `no_surjection_nat_seq01` | Constructive | None |
| `inj_to_nat_implies_surj_from_nat` | Classical | ClassicalEpsilon |
| `seq01_uncountable` | Classical | ClassicalEpsilon |

### Key Ideas

1. **Diagonal construction**: For any enumeration `f : nat -> seq01`, define `diagonal f n = flip (f n n)`. This sequence differs from every `f n` at position `n`.

2. **No surjection (constructive)**: If `f` were surjective, `diagonal f` would equal some `f n`, but `flip (f n n) ≠ f n n` — contradiction.

3. **Injection ⟹ surjection (classical)**: An injection `f : seq01 → nat` has a left inverse `g : nat → seq01` (constructed via `excluded_middle_informative` + `constructive_indefinite_description`), which is surjective.

4. **Uncountability**: If `seq01` were countable, there would be an injection to `nat`, hence a surjection from `nat` — contradicting (2).

## Build

```bash
coqc Cantor.v
```

Or with Makefile:

```bash
make
```

## Requirements

- Rocq Prover 9.1.1+ (or Coq 8.18+)
- OCaml 5.x

## Axioms

This proof uses `ClassicalEpsilon` which provides:
- `excluded_middle_informative : forall P:Prop, {P} + {~P}`
- `constructive_indefinite_description : forall (A:Type) (P:A->Prop), (exists x, P x) -> {x:A | P x}`

These are consistent with Rocq/Coq's type theory and are standard classical axioms.

## License

MIT

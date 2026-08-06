# Cantor's Diagonal Argument in Rocq

A formal proof that the set of all infinite binary sequences (0-1 sequences) is uncountable, using Cantor's diagonal argument. Includes a general form: for any type X, there is no surjection X -> (X -> bool).

## Theorems

```
Theorem no_surjection_general :
  forall X : Type,
    ~ exists f : X -> (X -> bool),
      forall s : X -> bool, exists x : X, f x = s.

Theorem seq01_uncountable : ~ countable seq01.
```

where `seq01 := nat -> bool` and `countable X := exists f : X -> nat, injective f`.

## Proof Structure

| Statement | Type | Axioms |
|-----------|------|--------|
| `diagonal_not_in_range` | Constructive | None |
| `no_surjection_general` | Constructive | None |
| `no_surjection_nat_seq01` | Constructive | None |
| `inj_to_nat_implies_surj_from_nat` | Classical | ClassicalEpsilon |
| `seq01_uncountable` | Classical | ClassicalEpsilon |

### Key Ideas

1. **Diagonal construction**: For any enumeration `f : nat -> seq01`, define `diagonal f n = flip (f n n)`. This sequence differs from every `f n` at position `n`.

2. **General Cantor's theorem (constructive)**: For any type `X`, no surjection `X -> (X -> bool)` exists. Given a surjection `f`, the diagonal `d x = flip (f x x)` must be in the range, so `f x0 = d` for some `x0`. But `f x0 x0 = d x0 = flip (f x0 x0)` — contradiction.

3. **No surjection nat -> seq01 (constructive)**: Direct corollary of (2) with `X = nat`.

4. **Injection ⟹ surjection (classical)**: An injection `f : seq01 -> nat` has a left inverse `g : nat -> seq01` (constructed via `excluded_middle_informative` + `constructive_indefinite_description`), which is surjective.

5. **Uncountability**: If `seq01` were countable, there would be an injection to `nat`, hence a surjection from `nat` — contradicting (3).

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

`Print Assumptions seq01_uncountable` outputs:

```
Axioms:
ClassicalEpsilon.constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

- `classic` (from `Classical_Prop`): excluded middle in `Prop`
- `constructive_indefinite_description` (from `ClassicalEpsilon`): eliminates
  `exists` in `Prop` to `{x | P x}` in `Type`

The proof uses `excluded_middle_informative` (a derived theorem, not an axiom)
to decide membership in the range of `f`. Both axioms are consistent with
Rocq/Coq's type theory.

The first three results (`diagonal_not_in_range`, `no_surjection_general`,
`no_surjection_nat_seq01`) are fully constructive — `Print Assumptions` reports
"Closed under the global context" for all three.

## License

MIT

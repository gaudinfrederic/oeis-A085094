# A085094 — "no entry is zero" conjecture, formalized in Lean 4

[![CI](https://github.com/USERNAME/a085094-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/USERNAME/a085094-lean/actions/workflows/ci.yml)

Machine-checked resolution of the conjecture recorded in the
comments of [OEIS A085094](https://oeis.org/A085094)
(Murthy–Srikanth, 2003): *smallest k such that n·k − 1 is a
palindrome, or 0 if no such number exists* — conjecture: **no
entry is zero**.

## Theorem

For every `n ≥ 1` there exists a nonzero decimal palindrome `P`
with `n ∣ P + 1` — i.e. `P = n·k − 1` for some `k ≥ 1`.

```lean
theorem A085094 (n : ℕ) (hn : n ≠ 0) :
    ∃ P : ℕ, P ≠ 0 ∧ (Nat.digits 10 P).Palindrome ∧ n ∣ P + 1
```

(Stronger than required: the OEIS convention counts `0` as a
palindrome — `a(1) = 1` — while our witness is nonzero.)

## Status

- Lean toolchain `v4.35.0`, mathlib `v4.35.0` (pinned manifest)
- `lake build` — full build of the closure, **zero `sorry`
  on the `A085094` path**
- `lake env lean A085094.lean` — exit 0
- `#print axioms A085094` — **only** `propext`,
  `Classical.choice`, `Quot.sound`: no `sorryAx`, no
  `native_decide` axioms anywhere in the transitive closure —
  every step is kernel-checked
- Independent bounded check (stdlib Python,
  `VERIFICATIONS/check_A085094.py` in the paper package):
  all 10000 b-file entries nonzero palindrome witnesses; all
  minima for `n ≤ 3000` re-derived and identical to OEIS

## Proof idea

`n = 2^a·5^b·m` with `gcd(m,10)=1`, `c = max(a,b)`: `P` begins
and ends with `c+1` nines, hence `P ≡ −1 (mod 10^c)` and
`2^a·5^b ∣ P+1` for free. A central palindromic window of length
`2·φ(m)·m+1` carries the positions `i = φ(m)·q` — each of weight
`w_i = 10^i + 10^(L−1−i) ≡ 2 (mod m)`, a unit — and a
unitary-sumset saturation lemma (`card_sum_intervals`,
`pal_window_extract_gen`) realizes the required residue mod `m`.
CRT closes `n ∣ P+1`.

## Contents

- `A085094.lean` — the theorem (282 lines) +
  `card_range_filter_dvd`
- `A084017.lean` — generic extraction `pal_window_extract_gen`
  (snapshot 2026-11-02, zero `sorry`; this is the in-progress
  development of the A084017 conjecture, whose headline theorem
  is still being assembled — `A085094` does **not** depend on
  it, see the axiom base above)
- `A084013.lean`, `A077727.lean`, `A077739.lean`,
  `A077754.lean`, `CornerTable.lean` — the shared engine:
  sumset growth lemma, `ofDigits` helpers, witness tables used
  by sibling theorems (not on the `A085094` dependency path)

## Reproduce

```sh
lake build        # installs toolchain via elan, fetches mathlib cache
lake env lean A085094.lean
```

## Reference

Companion paper `A085094-paper.tex` in the project package;
sibling result *Prescribed digit sums in residue classes and a
conjecture of Murthy (OEIS A077754)*, F. Gaudin —
https://doi.org/10.5281/zenodo.23879088

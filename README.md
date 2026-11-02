# ztl-classical — the classical register of ZTL's work

[ZTL](https://github.com/inventor1975/ZTL) (Zero-Trust Logic) keeps its Lean corpus on the **empty axiom list**: every
theorem there is checked by `#print axioms`, and a theorem that needs an axiom fails the build.

Some work around ZTL needs more than that, typically Mathlib's analysis, which rests on the three classical axioms
`propext`, `Classical.choice`, `Quot.sound`. That work lives here, separately, so that ZTL's "zero axioms" stays an
exact statement. The rule of this repository: **every theorem's axioms are printed and named**; nothing here is
counted as zero-axiom.

| file | theorems | axioms |
|---|---|---|
| `ZClassical/Zeta.lean` | `riemannZeta_neg_one`: ζ(−1) = −1/12 (from Mathlib's `riemannZeta_neg_nat_eq_bernoulli`); `riemannZeta_zero_val`: ζ(0) = −1/2; `shifted_value`: ζ(−1) − ζ(0) = 5/12 | `[propext, Classical.choice, Quot.sound]` |

`ZClassical/Zeta.lean` is the classical half of a reading of "1 + 2 + 3 + … = −1/12". The zero-axiom half is in ZTL
(`lean/ZZeta.lean`, `lean/ZZetaBridge.lean`). An article using both is being prepared for
[ztljudge.com](https://ztljudge.com).

## Build

Lean `leanprover/lean4:v4.29.1`, Mathlib `v4.29.1`:

    lake exe cache get    # Mathlib's prebuilt files
    lake build            # prints each theorem's axioms

## License and authorship

Apache-2.0 OR MIT, as ZTL. Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik.

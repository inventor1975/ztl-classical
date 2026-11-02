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
| `ZClassical/Bridge.lean` | `dispositions`: each of ZTL's six dispositions as a statement about classical propositions (below); `enum_iff`, `stableF_iff`, `rd_iff`, `kev_T_iff`, `kev_F_iff`; `credit_not_semantic` (where the translation must stop) | `[propext, Classical.choice, Quot.sound]` |
| `ZClassical/ZetaReading.lean` | `selfEq_disposition`: "S = S" for S = 1 + 2 + 3 + … is EARNED IF STABLE and not EARNED; the reading that blocks EARNED is ζ's own (ζ(−1) for S, ζ(−1) − ζ(0) for 0 + S) | `[propext, Classical.choice, Quot.sound]` |

## The bridge: ZTL's verdicts in classical terms

ZTL (`lean/ZSpeaks.lean`) gives a formula φ, under a valuation v that marks each atom true, false or dirty (Z), one of
six dispositions. `ZClassical/Bridge.lean` proves what each one says about classical propositions. A clean atom stands
for a proved or a refuted proposition; a dirty atom may stand for any proposition, read in one of two ways:
**uniformly** (one proposition per atom, at every occurrence: `semU v I φ`) or **occurrence by occurrence** (each
occurrence its own proposition: `semO v J φ` — ZTL's dirty reading).

| ZTL disposition | classical statement (`dispositions`) |
|---|---|
| EARNED | φ holds under every occurrence-by-occurrence reading |
| REFUTED | φ fails under every occurrence-by-occurrence reading |
| EARNED IF STABLE | φ holds under every uniform reading, not under every occurrence reading |
| REFUTED IF STABLE | φ fails under every uniform reading, not under every occurrence reading |
| ON CREDIT | uniform readings disagree about φ, and ZTL's greedy register says T |
| OPEN | uniform readings disagree about φ, and the greedy register does not say T |

The first four are statements of classical mathematics outright. ON CREDIT and OPEN coincide on the classical side —
the propositions consistent with the data disagree about φ — and differ only by ZTL's greedy register (`evalF`), which
classical logic does not have. That this is a boundary and not an omission is itself proved (`credit_not_semantic`):
p and ¬¬p, with p dirty, agree under every uniform and every occurrence reading, yet ZTL calls p OPEN and ¬¬p ON CREDIT —
the greedy register depends on the formula's shape, so no translation through readings can separate the two. The step from a proposition to its truth value uses excluded middle, hence the
classical axioms; ZTL itself stays on the empty axiom list.

`ZClassical/Zeta.lean` is the classical half of a reading of "1 + 2 + 3 + … = −1/12". The zero-axiom half is in ZTL
(`lean/ZZeta.lean`, `lean/ZZetaBridge.lean`). An article using both is being prepared for
[ztljudge.com](https://ztljudge.com).

## Build

Lean `leanprover/lean4:v4.29.1`, Mathlib `v4.29.1`:

    lake exe cache get    # Mathlib's prebuilt files
    lake build            # prints each theorem's axioms

## License and authorship

Apache-2.0 OR MIT, as ZTL. Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik.

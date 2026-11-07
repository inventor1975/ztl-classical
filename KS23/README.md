# KS23 — two order-23 Kochen–Specker candidates with no realization in ℝ³

[kscert](https://github.com/shayaansiddique06/kscert) (Siddique–Mian, [arXiv:2607.26413](https://arxiv.org/abs/2607.26413))
describes itself as machine-checking the geometric half of the minimum Kochen–Specker bound in Lean. Its
`unresolved.json` lists exactly two order-23 candidate graphs that none of its certified subgraphs covers. This
folder proves, for each of the two, that no realization exists:

| theorem | graph (full sha256 of the `unresolved.json` entry) | kernel check, our machine |
|---|---|---|
| `KS23.G07c6.not_realizable` | `07c673f16bdc25d57662acf746ffe72d166341ee2d8839c5bb133f0133249c49` | ~80 min |
| `KS23.G266c.not_realizable` | `266ce9a9c6d4688df50d0f1ed2fd35a9bdcbf9995302b97b51ea8ab2d473e608` | ~22 min |

(Timings: one Lean process per module, Lean `v4.29.1`, Mathlib `v4.29.1`, a desktop Linux machine; they are a
rough guide, not a benchmark.)

## What is stated, and what is not

Each theorem states `Realization 23 E → False`. `E` is the entry's edge list, copied from `unresolved.json`.
Lean itself does not hash `E`, so the link to kscert's entry rests on a comparison anyone can rerun:
`python3 KS23/scripts/check_edges.py PATH/TO/kscert/unresolved.json` finds each theorem's entry by its sha256 and
checks the same order, the same edge list (same pairs, same order), no duplicate edges, no loops and no vertex
outside `1..23`. Both print `OK`. `Realization` (`Geom.lean`) is our own structure, written to match kscert's field
by field: a vector in ℝ³ for each vertex, nonzero on `1..23`, orthogonal on every edge, and pairwise distinct as
rays. `SameRay u v` means `v = c·u` for some `c ≠ 0`, the same definition as kscert's `Geometry.lean` over ℝ.

Not claimed:

* the minimum Kochen–Specker bound, nor its verification;
* the completeness of kscert's candidate enumeration;
* any review by kscert's authors, or a line-by-line review of the Lean statements by a human expert.

These are two non-embeddability obligations, nothing more.

`#print axioms` for each of the two theorems: `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, no
`native_decide` and no custom axiom. The certificates are closed terms decided by `decide +kernel`, so the trust
base is Lean's kernel, including its built-in big-number arithmetic on `Nat` literals, and Mathlib.

## How the proof goes

* **Frame.** A triangle of the graph is sent to the coordinate axes (`wlog_frame`).
* **Chain.** Every other vertex is either the cross product of two already determined neighbours or lies in the
  plane orthogonal to one determined neighbour. With `p`, `q` an orthogonal pair of equal length spanning that
  plane, every ray of it is `(1 − t²)·p + 2t·q` for some `t ∈ [−1, 1]`, up to a nonzero factor of either sign
  (`plane_param`; `t = ±1` gives the ray of `q`). For these two graphs, two such parameters suffice. This
  is a property of the graphs, and the certificate's chain check fails if it does not hold.
* **Vectors.** Each vertex gets an explicit integer polynomial vector `P_v(t₁, t₂)` with an identity
  (`g · P_v = P_a × P_b`, …). Each identity is checked by Kronecker substitution, one exact integer evaluation,
  and the degree and coefficient bounds that make it sound are proved in `PE.check_sound`.
* **Realization to parameters.** `chain_sound` shows that any realization gives a parameter point at which every
  `P_v` is a nonzero multiple of the realization vector. The factors `g` are shown nonzero there: two distinct
  rays are not parallel, so their cross product is nonzero.
* **Cover.** A quadtree over `[−1, 1]²` uses outward-rounded dyadic interval arithmetic (`Dy.lean`). At each leaf
  some edge's dot product provably avoids 0. A box the tree leaves open must lie, as checked, in the square of a
  blow-up chart `(a + r, b + rs)` / `(a + rs, b + r)`. `cover_square` shows the two charts of a centre cover its
  whole square, the centre itself (`r = 0`) included. Each chart has its own tree and its own exact identities `L·(P_v ∘ φ) = g·R_v`. A chart may have charts
  of its own; these two graphs use two levels (`Cert.lean`).
* **Soundness.** `chart_ok` and `no_realization` are proved once, for any certificate. The graph-specific files
  only supply the data and the kernel's verdict on it.

The certificates (the `G07c6/` and `G266c/` Lean files) are committed here. They were produced by a search in
Python. That search is untrusted and is not needed to check them; it lives in a private repository. We also ran
the same two graphs through a second checker of our own, the exact-arithmetic `zcertify.check_none` of
[ZTL](https://github.com/inventor1975/ZTL), which accepted both. It uses a different certificate format and
different code, but it is written by the same people from the same edge lists, so it is a cross-check and not an
independent verification.

## Build

    lake exe cache get
    lake build KS23

`KS23` is not a default target because of its kernel time.

## Authorship

Formalised by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik.

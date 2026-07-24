# Hierarchical Symmetry Selects Log-Poisson Cascades: Classification, Uniqueness, and Stability

**E. M. Freeburg**
Independent Researcher

**arXiv:** [2604.01632](https://arxiv.org/abs/2604.01632) (published: **v2**, June 2026 — this repository carries **v3**; the arXiv replacement is forthcoming)

> **Version 3.** This repository carries **v3** — an erratum and
> strengthening of Theorem 17 (the v2 claim "no finite moment window
> identifies the class" is false as stated: impersonators exist for every
> window within {0, k, 2k, 3k}, and five exact contiguous orders identify
> the class), with machine-checked coverage of every principal numbered
> result. See [CHANGES-v3.md](CHANGES-v3.md) for the full change log and
> verification trail. The arXiv v3 replacement is forthcoming;
> [versions/](versions/) archives the published arXiv artifacts.

---

## Abstract

Within i.i.d. multiplicative cascades, a single axiom—the hierarchical symmetry, a linear contraction on incremental scaling exponents—is shown to be necessary and sufficient for the cascade multiplier to be log-Poisson. We prove: (1) a characterization theorem determining the log-Poisson law with explicit parameters, within the class of *all* multipliers with finite lattice moments; (2) a classification theorem locating the log-Poisson class inside the log-infinitely-divisible family and identifying how every rival sub-family fails the symmetry; (3) a stability theorem with explicit constants—(1+beta)^{1/2} known increment, sqrt(2) fitted, sharp at the variance level—and (4) an unconditional propagation theorem transferring the bound to the multiplier distribution at the sharp rate Theta(sqrt(epsilon)), with a matching lower bound. Beyond independence, the classification extends *exactly* at the level of asymptotic statistics (the limiting cumulant generating function at lattice orders, with large deviations and the multifractal spectrum under off-lattice regularity) and *provably not* at the level of laws: an explicit stationary ergodic Markov multiplier satisfies the symmetry exactly with a non-log-Poisson marginal, while exchangeable multipliers with exact scaling collapse to the i.i.d. log-Poisson cascade and finite-state Markov multipliers cannot satisfy the symmetry's real-argument form with nontrivial intermittency. For exactly scale-invariant log-infinitely-divisible multifractal random measures, five exact contiguous moment orders identify the cascade class while four contiguous orders admit impersonators, and at the level of the scale-invariance generator the symmetry selects exactly the Barral–Mandelbrot compound Poisson cascade, with scale-ratio-free stability constants. The proofs reduce to second-moment identities and multiplicative couplings.

## Reader's Companion — Plain-Language Site

**[When Hierarchy Imposes Form](https://emfreeburg.github.io/hierarchical-symmetry-theorem/)**
is a plain-language companion to the paper. It explains the result and its
context for a general audience while staying faithful to the paper's scope —
the formal classification is established within i.i.d. multiplicative cascades.

- **Live:** <https://emfreeburg.github.io/hierarchical-symmetry-theorem/>
- **Single self-contained file:**
  [`artifact/when-hierarchy-imposes-form.html`](https://emfreeburg.github.io/hierarchical-symmetry-theorem/artifact/when-hierarchy-imposes-form.html)
  — the entire page (text, figures, styles) inlined into one portable HTML file.

The companion is served via GitHub Pages from the
[`gh-pages`](../../tree/gh-pages) branch; the paper itself remains the
authoritative statement of the results.

## Read the Paper

- **[PAPER.md](PAPER.md)** — the full paper, readable directly on GitHub.
  The transcription is 1:1 with the LaTeX source (statements, proofs,
  numbering, constants, bibliography), up to two markdown conventions:
  section headings are title-cased, and inline mathematics uses GitHub's
  dollar-backtick delimiters.
- **[versions/v2/](versions/v2/)** — the official arXiv-watermarked PDF.
- The authoritative source is the self-contained LaTeX project in
  [`paper/`](paper/), in two formats: arXiv/amsart (`main.tex`, 32 pp.)
  and Journal of Statistical Physics / Springer Nature
  (`jsp/main-jsp.tex`, 27 pp.). The two bodies are kept 1:1 with identical
  numbering.

### Building the paper

Requires a TeX distribution (TeX Live, MacTeX, or TinyTeX):

```bash
cd paper
pdflatex main && pdflatex main          # → paper/main.pdf   (32 pp.)

cd jsp
pdflatex main-jsp && pdflatex main-jsp  # → paper/jsp/main-jsp.pdf (27 pp.)
```

## The Lean Formalization — [`formalization/`](formalization/)

The i.i.d. theory of the paper — the characterization at the level of
probability laws (Thm 3(ii)), the forward classification (Thm 7), the
stability theorem with both sharp constants and their exact sharpness
witnesses (Thm 10), and **both halves of the sharp propagation rate Θ(√ε)**
(Thm 11, unconditional, and Thm 12, with the bracket `theorem11_12_theta`) —
**and, new in v3, the corrected continuous-cascade Theorem 17 (both
parts: five-point rigidity and the four-order impersonators, in exact
rationals) with Theorem 18's weakened-hypothesis forward route**
(`formalization/Freeburg/Continuous.lean`), **§6 in scoped form
(Theorems 13–16: `BeyondIID.lean`) and Corollaries 19–23
(`Corollaries.lean`)** —
is formalized and kernel-checked in **Lean 4 + Mathlib**:

- **16 modules, 8,477 lines, 302 named declarations, zero `sorry`** — plus the compile-checked interface manifest (`Freeburg/Main.lean`) and boundary-regime instances (`Freeburg/EdgeCases.lean`).
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only — enforced by
  [`AxiomAudit.lean`](formalization/AxiomAudit.lean), which walks every
  constant compiled from the library (489, including all auto-generated
  auxiliaries) and fails on any violation.
- The formalization found exactly one error in the §1–5 material (a sign
  typo in a Theorem-12 parenthetical, fixed in v2 pre-submission) and has
  sharpened eight statements to date; see the
  [formalization README](formalization/README.md) for the full
  theorem-by-theorem mapping, the documented deviations, and the findings.

### Building the formalization

Requires [elan](https://github.com/leanprover/elan) (the toolchain is pinned
by `lean-toolchain`; Mathlib is pinned by `lake-manifest.json`):

```bash
cd formalization
lake exe cache get      # pulls the Mathlib build cache (multi-GB, one-time)
lake build              # builds the sixteen Freeburg modules
lake env lean AxiomAudit.lean   # whole-library axiom audit (must print PASS)
```

## Repository Structure

```
.
├── README.md
├── PAPER.md              # Full paper readable on GitHub (1:1 transcription)
├── LICENSE
├── paper/                # Current (v3 draft) LaTeX source
│   ├── main.tex          #   arXiv/amsart format
│   └── jsp/              #   Journal of Statistical Physics format
│                         #   (Springer Nature sn-jnl class, cls/bst included)
├── formalization/        # Lean 4 + Mathlib formalization (kernel-checked)
│   ├── Freeburg/         #   the sixteen modules (incl. Main = manifest, EdgeCases)
│   ├── AxiomAudit.lean   #   whole-library axiom audit
│   ├── README.md         #   Lean ↔ paper mapping, deviations, findings
│   └── LICENSE           #   Apache-2.0 (the formalization's code license)
└── versions/             # Official arXiv PDFs; frozen superseded sources
    ├── v1/               #   April 2026 (14 pp.) — PDF + frozen source
    └── v2/               #   June 2026 (23 pp.) — PDF + frozen source
```

## Versions

- **v3 (this repository; arXiv replacement forthcoming)** — erratum and strengthening of
  Theorem 17: the v2 statement "no finite moment window identifies the class"
  is corrected to a sharp boundary (impersonators exist for every window
  contained in {0, k, 2k, 3k}; five exact contiguous orders force the compound
  Poisson cascade; sparse windows remain open), with a new self-contained squared-tilt proof that also
  yields Theorem 18's forward direction under weaker hypotheses. Abstract,
  introduction, remarks, and §9 updated to match. Full log:
  [CHANGES-v3.md](CHANGES-v3.md).
- **v2 (June 2026, latest arXiv version)** — complete rewrite and major expansion:
  9 sections, 23 numbered results. Sharp-constant stability theory;
  unconditional propagation at the exact rate Θ(√ε) with a matching lower
  bound (§5); beyond-independence classification and its boundary (§6);
  continuous cascades and generator-level selection of the Barral–Mandelbrot
  compound Poisson cascade (§7). JSP-format twin added, and the Lean
  formalization published alongside.
- **v1 (April 2026)** — initial submission (14 pp.): characterization,
  classification, and stability for i.i.d. cascades.
  Kept under [`versions/v1/`](versions/v1/).

## Citation

```bibtex
@article{freeburg2026hierarchical,
  author  = {Freeburg, E. M.},
  title   = {Hierarchical symmetry selects log-{P}oisson cascades:
             classification, uniqueness, and stability},
  year    = {2026},
  eprint  = {2604.01632},
  archivePrefix = {arXiv},
  primaryClass  = {math.PR}
}
```

## License

- The paper — `PAPER.md`, the `paper/` sources, and everything outside
  `formalization/` — is licensed under [CC BY 4.0](LICENSE).
- The Lean formalization ([`formalization/`](formalization/)) is licensed
  under the [Apache License 2.0](formalization/LICENSE), the standard
  license of the Lean/Mathlib ecosystem.

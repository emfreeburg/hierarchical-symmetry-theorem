# Hierarchical Symmetry Selects Log-Poisson Cascades: Classification, Uniqueness, and Stability

**E. M. Freeburg**
Independent Researcher

**arXiv:** [2604.01632](https://arxiv.org/abs/2604.01632) (current version: **v2**, June 2026)

---

## Abstract

Within i.i.d. multiplicative cascades, a single axiom—the hierarchical symmetry, a linear contraction on incremental scaling exponents—is shown to be necessary and sufficient for the cascade multiplier to be log-Poisson. We prove: (1) a characterization theorem determining the log-Poisson law with explicit parameters, within the class of *all* multipliers with finite lattice moments; (2) a classification theorem locating the log-Poisson class inside the log-infinitely-divisible family and identifying the mechanism by which every rival sub-family fails the symmetry; (3) a stability theorem with sharp constants—(1+beta)^{1/2} when the limiting increment is known, sqrt(2) when it is fitted—and (4) an unconditional propagation theorem transferring the bound to the multiplier distribution at the sharp rate Theta(sqrt(epsilon)), with a matching lower bound. Beyond independence, the classification extends *exactly* at the level of asymptotic statistics (limiting cumulant generating function, large deviations, multifractal spectrum) and *provably not* at the level of laws: an explicit stationary ergodic Markov multiplier satisfies the symmetry exactly with a non-log-Poisson marginal, while exchangeable multipliers collapse to the i.i.d. log-Poisson cascade and finite-state Markov multipliers cannot satisfy the symmetry at all. In the continuous category of exactly scale-invariant log-infinitely-divisible multifractal random measures, no finite moment window of structure-function exponents identifies the cascade class, whereas at the level of the scale-invariance generator the symmetry selects exactly the Barral–Mandelbrot compound Poisson cascade, with scale-ratio-free stability constants. The proofs reduce to second-moment identities on [0,1] via the change of variables u = e^{kx}, boundedness of the multiplier (ess sup W = r^gamma), and multiplicative couplings.

## Read the Paper

- **[PAPER.md](PAPER.md)** — the full paper, readable directly on GitHub.
  The transcription is 1:1 with the LaTeX source (statements, proofs,
  numbering, constants, bibliography), up to two markdown conventions:
  section headings are title-cased, and inline mathematics uses GitHub's
  dollar-backtick delimiters.
- **[versions/v2/](versions/v2/)** — the official arXiv-watermarked PDF.
- The authoritative source is the self-contained LaTeX project in
  [`paper/`](paper/), in two formats: arXiv/amsart (`main.tex`, 27 pp.) and
  Journal of Statistical Physics / Springer Nature (`jsp/main-jsp.tex`,
  23 pp.). The two bodies are character-identical with identical numbering.

### Building the paper

Requires a TeX distribution (TeX Live, MacTeX, or TinyTeX):

```bash
cd paper
pdflatex main && pdflatex main          # → paper/main.pdf   (27 pp.)

cd jsp
pdflatex main-jsp && pdflatex main-jsp  # → paper/jsp/main-jsp.pdf (23 pp.)
```

## The Lean Formalization — [`formalization/`](formalization/)

The i.i.d. theory of the paper — the characterization at the level of
probability laws (Thm 3(ii)), the forward classification (Thm 7), the
stability theorem with both sharp constants and their exact sharpness
witnesses (Thm 10), and **both halves of the sharp propagation rate Θ(√ε)**
(Thm 11, unconditional, and Thm 12, with the bracket `theorem11_12_theta`) —
is formalized and kernel-checked in **Lean 4 + Mathlib**:

- **11 modules, 6,581 lines, 247 declarations, zero `sorry`.**
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only — enforced by
  [`AxiomAudit.lean`](formalization/AxiomAudit.lean), which walks every
  constant compiled from the library (373, including all auto-generated
  auxiliaries) and fails on any violation.
- The formalization found exactly one error in the paper (a sign typo in a
  Theorem-12 parenthetical, fixed in v2 pre-submission) and sharpened six
  statements; see the
  [formalization README](formalization/README.md) for the full
  theorem-by-theorem mapping, the documented deviations, and the findings.

### Building the formalization

Requires [elan](https://github.com/leanprover/elan) (the toolchain is pinned
by `lean-toolchain`; Mathlib is pinned by `lake-manifest.json`):

```bash
cd formalization
lake exe cache get      # pulls the Mathlib build cache (multi-GB, one-time)
lake build              # builds the eleven Freeburg modules
lake env lean AxiomAudit.lean   # whole-library axiom audit (must print PASS)
```

## Repository Structure

```
.
├── README.md
├── PAPER.md              # Full paper readable on GitHub (1:1 transcription)
├── LICENSE
├── paper/                # Current (v2) LaTeX source
│   ├── main.tex          #   arXiv/amsart format
│   └── jsp/              #   Journal of Statistical Physics format
│                         #   (Springer Nature sn-jnl class, cls/bst included)
├── formalization/        # Lean 4 + Mathlib formalization (kernel-checked)
│   ├── Freeburg/         #   the eleven modules
│   ├── AxiomAudit.lean   #   whole-library axiom audit
│   ├── README.md         #   Lean ↔ paper mapping, deviations, findings
│   └── LICENSE           #   Apache-2.0 (the formalization's code license)
└── versions/             # Official arXiv PDFs; frozen superseded sources
    ├── v1/               #   April 2026 (14 pp.) — PDF + frozen source
    └── v2/               #   June 2026 (27 pp.) — PDF (source = paper/)
```

## Versions

- **v2 (June 2026, current)** — complete rewrite and major expansion:
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

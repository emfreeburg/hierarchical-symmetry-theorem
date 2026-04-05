# Hierarchical Symmetry Selects Log-Poisson Cascades: Classification, Uniqueness, and Stability

**E. M. Freeburg**
Independent Researcher

**arXiv:** [2604.01632](https://arxiv.org/abs/2604.01632)

---

## Abstract

Within i.i.d. multiplicative cascades, a single axiom—the hierarchical symmetry, a linear contraction on incremental scaling exponents—is shown to be necessary and sufficient for the cascade multiplier to be log-Poisson. We establish three results: (1) a characterization theorem proving that the hierarchical symmetry uniquely determines the log-Poisson distribution with explicit parameters; (2) a classification theorem proving that the hierarchical symmetry selects exactly the log-Poisson class from the full log-infinitely-divisible family, excluding log-normal, log-stable, and all intermediate generators; and (3) a stability theorem proving that approximate hierarchical symmetry implies approximate log-Poisson, with an explicit O(sqrt(epsilon)) Wasserstein bound. The proofs reduce the problem to the Hausdorff moment problem on [0,1] via the change of variables u = e^{kx}, where determinacy and stability follow from classical results.

## Read the Paper

**[Read the full paper in markdown](PAPER.md)** — readable directly on GitHub.

The authoritative version is a self-contained LaTeX project in the [`paper/`](paper/) directory.

### Building

Requires a TeX distribution (TeX Live, MacTeX, or TinyTeX):

```bash
cd paper
pdflatex main
pdflatex main
```

This produces `paper/main.pdf`.

## Repository Structure

```
.
├── README.md
├── PAPER.md              # Full paper readable on GitHub
├── LICENSE
└── paper/
    └── main.tex          # Self-contained LaTeX source (as submitted to arXiv)
```

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

This work is licensed under [CC BY 4.0](LICENSE).

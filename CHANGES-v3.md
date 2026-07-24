# v3 changes

Change log for version 3. Base: v2 (arXiv:2604.01632v2, repository commit
`18f5ae1`). This file documents every substantive change from v2, with
provenance.

## Headline: erratum and strengthening of Theorem 17

**v2 stated (Theorem 17, "No finite moment window identifies the class"):**
for *any* finite lattice window `F ⊂ kℕ₀` there exist non-CPC log-ID
generators matching the She–Lévêque exponents on `F`; structure-function data
on a finite window can never certify the log-Poisson class.

**This is false as stated.** The correct statement, now Theorem 17 in v3
("Four orders do not identify the class; five contiguous orders do"):

- **(i)** Impersonators exist for every `F ⊆ {0, k, 2k, 3k}` — the maximal
  impersonable *contiguous* window is four orders. (Sparse windows neither
  contained in `{0..3k}` nor containing `{0..4k}` are open; the paper's
  statement is scoped accordingly.) Every four-point impersonator
  strictly *undershoots* at the next order (`ζ_{4k} < ζ^SL_{4k}`), with an
  explicit deficit budget `≤ Cβ(1−β)³` absent amplifying jumps.
- **(ii)** **Five-point rigidity:** exact agreement with `ζ^SL` at the five
  contiguous points `{0, k, 2k, 3k, 4k}` forces `σ₀² = 0` and `Π = Cδ_b` —
  the generator *is* the compound Poisson cascade. Hypotheses are *weaker*
  than v2's Theorem 18 setting: only `ψ` finite on `[0, 4k]`, no (S_c), no
  divergence steps.

**Where the v2 proof broke:** the closing sentence of the v2 proof ("For
general finite F, the same ansatz with more atoms imposes finitely many linear
constraints on infinitely many degrees of freedom, with positivity maintained
by anchoring the negative part on the CPC atom") fails at the very next window:
for `F = {0,k,2k,3k}` the constrained perturbation collapses to the CPC atom
(geometric-moment/Dirac rigidity applied to `(1−u)dμ⁺`). The v2 *example*
(`F = {0,1,2}`, weights `w₁ = 5/27`, `w₂ = 55/27`, deviation `+77/5400` at
`m = 3`, `s = ½`) is correct and is retained.

**Proof mechanism of (ii):** weight the tilted Lévy measure by the *squared*
tilt, `ρ := (u−1)² dΠ̃ ≥ 0`. Being a square, ρ is nonnegative on both sides of
`u = 1`, which kills amplifying jumps on a finite window with no `q → ∞`
argument. Step-k second differences give `Δ²ψ(mk) = σ₀²k² + r_m`; matching at
five points pins `σ₀²k² + r_m = A′β^m` (m = 0, 1, 2, `A′ = C(1−β)²`); testing
against `(u−β)²` yields `0 ≤ ∫(u−β)²dρ = −σ₀²k²(1−β)² ≤ 0`, so `σ₀² = 0` and
`ρ = A′δ_β`, and inverting the tilt gives `Π̃ = Cδ_β`. This is the paper's own
kernel-checked Dirac-rigidity step (`Dirac.eq_dirac_of_geometric_moments`)
applied to ρ instead of η.

### Provenance / verification trail

Discovered and proved in the furtherance program; independently verified
twice; adversarial gate closed.

- Internal verification memo `19-paper-trustmap`
  §2b — original refutation and proofs (results F2, R5/A4-8, A4-10; claims
  A4-5, A4-9).
- Internal verification memo `29-verify-thm17-refutation`
  — adversarial verification, **REFUTATION-CONFIRMED** (2026-06-14). Exact
  Farkas/SOS certificate in rationals: `P(u) = ((u−1)(u−β))²`,
  `y = [4/9, −20/9, 37/9, −10/3, 1]`; plus exhaustive LP/nonlinear adversarial
  families (amplifying atoms, continuous bands, Gaussian components) all
  infeasible on 5-point windows; 4-point boundary control reproduces the v2
  printed example exactly.
- Internal verification memo `EXTERNAL-2026-06-13-thm17-from-health-of-form`
  — independent external review (sister project `test-health-of-form`):
  symbolic re-derivation + numerical check over 10⁵ random parameter draws.
- Numerics: internal script `29_thm17.py`
  (seed 20260644, mpmath 50 dps); re-run self-contained in this
  workspace's internal verification tree as
  `review/numerics/scripts/a2_thm17_rigidity.py` →
  `review/numerics/results/thm17/a2_thm17_rigidity.json`.

## File-by-file change log

Identical edits applied to `paper/main.tex` (LaTeX source) and `PAPER.md`
(GitHub-rendered mirror), keeping v2's theorem numbering (Theorem 17 stays 17,
now two-part; Theorem 18 and Corollary 19 unchanged).

1. **Theorem 17 statement** (`thm:window`) — replaced by the corrected
   two-part statement (i)/(ii) above.
2. **Theorem 17 proof** — rewritten: squared-tilt machinery and second-
   difference identity (eq. `\ref{eq:seconddiff}` / (7.1)) up front; part (ii)
   rigidity proof; part (i) retains the v2 three-point example (exact rational
   weights now printed), adds the collapse lemma showing the v2 general-F
   sentence false at `{0..3k}`, the explicit maximal 4-point impersonator
   (`ρ = 0.114478δ_{0.4} + 0.107744δ_{0.95}`, deviation `−0.01679` at
   `q = 4`), and the Cauchy–Schwarz one-sidedness bound.
3. **Remark after Theorem 17** — v2's "Identifiability requires constraints of
   unbounded order, which structure functions cannot supply" deleted as false;
   replaced by the corrected picture (obstruction stops at three-point
   windows; the barrier to structure-function certification is statistical,
   not principled), with an explicit note that v2 asserted the contrary.
4. **Theorem 18 proof** — appended alternative forward proof as a corollary of
   Theorem 17(ii), with strictly weaker hypotheses (`ψ` finite on `[0,4k]`
   only; no (S_c), no divergence steps).
5. **Remark "What the two theorems mean together"** — reframed: the practical
   preference for magnitude statistics is now a statement about statistics
   rather than principle; continuous-category rigidity strengthened (five
   lattice moments suffice).
6. **Abstract** — the "no finite moment window … identifies the cascade
   class" sentence replaced by the sharp-boundary formulation (all three
   sources + repo README's plain-text abstract).
7. **Introduction, continuous-cascades summary** — "*no finite window
   identifies the cascade class*" replaced by the sharp boundary ("four
   contiguous orders admit impersonators, five exact contiguous orders force
   the compound Poisson cascade").
8. **§9 opener** — "while no finite moment window of structure functions can
   do so" corrected (five exact contiguous orders can, beyond the practical
   window).
9. **§9 open problem 4 (Statistics of the A1 test)** — requalified: magnitude
   statistics remain the operative recommendation, now as a dictate of
   statistics, not principle; sparse-window question recorded as open.

(All nine edits applied identically to `paper/main.tex`, `paper/jsp/main-jsp.tex`,
and `PAPER.md`; audit `review/1b-diff-audit.md` confirms the three are 1:1.)

## Second hardening pass (2026-07-22): independent-review fixes

A round of five independent adversarial review passes (hostile-referee
read, three-source parity audit, Appendix-A accuracy audit, Lean
statement-faithfulness audit, publication dry run) plus fresh
deterministic gates produced the following paper changes, applied identically to `main.tex`, `jsp/main-jsp.tex`, and
`PAPER.md` (evidence: the internal verification record
`review/REVIEW-LOG.md`, session-4 entry, kept with the working tree):

- **§7 opening / intro / Thm 17 tail / two remarks — the "finite moment
  window" motivation corrected.** v2–v3 asserted that concavity with
  ζ₁ = 1 forces a finite structure-function window [0, q*) ("a hard
  information barrier"). False for the selected class itself: under (M2)
  the SL curve is strictly increasing (γ = 1/3 at SL values), ζ_q > 1 for
  all q > 1, so every CPC moment is finite (q* = ∞). Rewritten throughout:
  the finite window is a property of rival generators with eventually
  decreasing ζ (log-normal, log-stable); for the CPC the barrier is
  statistical (finite samples), matching the existing "statistical, not
  principle" language. All `q* ≤ 3` annotations replaced by
  "practically accessible window, typically q ≲ 3".
- **Abstract + intro — finite-state claim scoped.** "cannot satisfy the
  symmetry at all" claimed the lattice-only case, which Thm 16's own
  remark and §9 list as open. Now "cannot satisfy the symmetry's
  real-argument form" / "the real-p form of A1".
- **§5 display corrected.** The pathwise bound `Σ(1−U_i^{1/k}) ≤
  (2/k)Σ(1−U_i)` is false for k ≥ 3 (at u → 0 the left side tends to 1 >
  2/k). Constant corrected to 2 (valid for all k: trivial for u ≤ 1/2,
  telescoping for u ≥ 1/2); nothing downstream used the 2/k form.
- **Thm 10 sharpness scoped to the variance level.** The printed two-atom
  family attains the variance constants for every β but the Wasserstein
  constants only for β < 1/2 (at β = 2/3 its best W₁ ratio is 0.948,
  verified numerically twice). Statement, remark (a)/(b), intro, abstract,
  and Appendix A now say "sharp for the underlying variance bounds",
  with the β < 1/2 Wasserstein attainment noted.
- **Thm 11 constant honesty.** "absorbing O(ε) via ε ≤ √ε" replaced by the
  explicit threshold ε₀ = ‖η‖/(4(1+β)) — the form the Lean actually
  verifies (`theorem11_rate_upper`).
- **Thm 14(ii) proof completed.** The printed comparison was against the
  matched-λ log-Poisson law only; a two-line support/mass-ratio argument
  (lattice forces (a′,b′) = (a,b); depth-≥1 ratios force λ′ = 2λ; top atom
  e^{−2λ} < ½(1+e^{−2λ})) now rules out every log-Poisson law.
- **Thm 17(i) continuum for the maximal window.** The claimed continuum was
  argued only for F ⊆ {0,k,2k}; one sentence now exhibits the
  two-parameter family (vary atom positions, weights by two-point
  interpolation) for the full window.
- **Smaller fixes:** ζ^LP curve defined at first use (Thm 14); Thm 12(ii)
  local `a = |A|` collision removed (display uses e^{|A|}); "Lemma 1(2)"
  citation corrected (no part (2) exists); window notation `{0,…,4k}`
  written out as `{0, k, 2k, 3k, 4k}` (ambiguous for k > 1); Lemma 1's
  editorial sentence moved out of the statement; Appendix A: Cor 6 mapping
  corrected to "lattice-level skeleton", W₁ Kantorovich–Rubinstein dual
  form disclosed as a definitional bridge, Unicode em-dashes normalized.
- **Typography:** the Thm 17(ii) inequality chain split into an `aligned`
  display; Lean identifiers in Appendix A made breakable at underscores.
  Both PDFs: 0 errors, 0 undefined refs, **0 overfull hboxes** (restores
  the v2 release standard), now 33 pp. / 27 pp.
- **PAPER.md rendering fix (also latent in published v2):** GitHub strips
  markdown backslash-escapes inside `$$…$$` before math extraction
  (confirmed against the live renderer) — `\\` row separators, `\,`,
  `\|`, `\{` all corrupted; 61 of 81 displays affected, the two
  Theorem-10 `cases` displays broken outright. All 81 displays converted
  to ` ```math ` fences (code-fence content is escape-proof;
  render-verified via `gh api /markdown`, 81/81 recognized). Equation tag
  (7.1) renumbered to (3) to match both PDFs.
- **Lean additions (gates re-run, ALL PASS):** non-vacuity witness — the
  CPC generator satisfies `theorem17_five_point_rigidity`'s five-point
  hypothesis (compiled `example`, `EdgeCases.lean` item 5); docstring
  clarifications (Thm 18 route-B header, Thm 14(ii) matched-law scope,
  AxiomAudit run directory). Library now 8,477 lines (302 declarations,
  489 audited constants unchanged).

## Third hardening pass (2026-07-23): second-round review fixes

A second round of adversarial review (re-verifying the previous pass's
own edits, a cold-eyes referee read focused on §§2–6/§8, a page-by-page
visual PDF pass, and an arXiv staging dry run) produced these changes, applied to all
three sources:

- **Theorem 13 consequent scoped (the round's one serious find).**
  Lattice A1 pins Λ off-lattice only up to convexity, so the
  large-deviation rate and multifractal spectrum are not forced to
  coincide by lattice data alone; exact coincidence is now claimed for
  lattice observables, with LD/spectrum conditioned on Λ = Λ_LP holding
  on [0,∞) (as Theorem 14's construction delivers). Abstract parenthetical
  scoped to match.
- **Theorem 16's "real-p form" defined** in the statement (the closed
  form (∗∗) for all real p ≥ 0); abstract finite-state clause carries
  "with nontrivial intermittency" (C = 0 deterministic multipliers
  satisfy real-p A1 trivially).
- **Theorem 17(i): nondegeneracy hypothesis γ ≥ 0 added** (as at
  She–Lévêque values; for large C the matched curve degenerates as a
  measure). Part (ii) unchanged.
- **Theorem 14 proof: phase-transition labels un-swapped** (phase-1
  states are the jump states; the next value from them is a).
- **Theorem 3(ii) proof: C ≥ 0 derived** (log-convexity of
  m ↦ E[W^{km}]; second logarithmic difference C(1−β)²β^m|ln r|),
  C = 0 degenerate case noted.
- **Theorem 11: kernel-verified threshold stated in paper units** —
  ε₀ = ‖η‖/(4(1+β)|ln r|), and the Lean's constant identified as the
  sharper k = 1 form (e^{a₀} for e^{a₀+1}).
- **Smaller fixes:** Thm 12 proof uses the defined a₀ (no bare a);
  reading-(ii) Wasserstein attainment at v = 2β documented in the
  sharpness remark; Prop 9(b) scoped to lattice exponents; Cor 21 given
  its conservation hypothesis (matching `corollary21_unique_curve`);
  Φ(r^n) ≙ W₁⋯W_n made operative in §2; ε₁ → +ε; log/ln convention;
  abstract "exchangeable … with exact scaling".
- **Bibliography corrections:** [SW95] title is "Quantized energy
  cascade …" (not "dissipation"); [DG96] is "Possible statistics of
  scale invariant systems", pages 797–816 (the printed title tail and
  pages both belonged to the 1996 companion paper).
- **Recorded, deliberately unchanged:** section-crossing notation reuse
  (d, W₁, A, a — published-v2 notation; renaming would drift from the
  Lean and README cross-references); c₂(β)'s redundant "∨ 1" (Lean
  parity); the QED-box-beside-cases artifact in Thm 10 (amsthm/sn-jnl
  limitation, identical in published v2); sn-jnl's bold-math abstract
  (house style).
- PDFs: 0 errors / 0 undefined / 0 overfull, now 33 pp. / 27 pp.
  arXiv v3 tarballs staged with checksums and paste-ready metadata
  (internal staging area; nothing uploaded).

## Explicitly *not* changed (and why)

- **The practical recommendation** (magnitude/cumulant statistics over
  high-order structure functions) — unchanged everywhere. Theorem 17(ii) is an
  exact-arithmetic, in-principle result; it does not move the finite-sample
  floor (§9 problem 4). Both verification runs stress this.
- **Discrete sharpening A4-9** ("R5-discrete": Theorem 7 from A1 at
  `p ∈ {0,k,2k}` + `E[W^{4k}] < ∞` only) — **not** included in v3: it carries
  the flagged gap **G1** (the ID moment–cumulant bridge `E[W^p] = e^{ψ(p)}`
  on the needed range), the same bridge the formalization declines to
  formalize. Candidate for v3 once G1 is resolved.
- **Sparse windows** (e.g. `{0, k, 5k, 17k}`) — not settled by R5 (which needs
  a *contiguous* five-window); the theorem statement is careful to claim only
  `F ⊇ {0,…,4k}` for rigidity and `F ⊆ {0,k,2k,3k}` for impersonation.
  Windows that are neither (sparse, non-contiguous) remain open.
- **Lean formalization** — Theorems 17/18 were never formalized (§6–7 are
  paper-only; see `gate0_scope_ledger.md` in the sister project
  `test-health-of-form`), so the
  public Lean release is *not* affected by the erratum. Theorem 17(ii) reduces
  to the kernel-checked `Dirac.eq_dirac_of_geometric_moments` under the
  `ln r ↦ −1` dictionary and is close to mechanizable — a v3 formalization
  target.

## TODO before v3 submission

- [x] Mechanize Theorem 17 in Lean — DONE 2026-07-22, beyond the original
      goal: `formalization/Freeburg/Continuous.lean` kernel-checks 17(ii)
      (five-point rigidity, `theorem17_five_point_rigidity`), 17(i)
      (one-sidedness with equality-iff-CPC, the deficit budget, and both
      exact-rational witnesses incl. the injective 3-atom continuum), plus
      Theorem 18's forward direction via route B
      (`theorem18_forward_fiveMoment`). 0 sorry, 0 custom axioms
      (AxiomAudit PASS; library-wide count now 489 constants).
- [ ] Decide whether to cite the Farkas/SOS certificate in the paper (an
      appendix remark would make the rigidity independently checkable by hand).
      **Status 2026-07-23: DEFERRED (author undecided; recommendation: omit
      for v3 — the kernel-checked proof supersedes a hand-check remark, and
      new paper content would reopen the converged review loop. Can ship in
      any later revision without affecting correctness.)**
- [ ] Resolve G1, then consider adding A4-9 (discrete five-moment sharpening
      of Theorem 7). **Status 2026-07-23: stays PARKED for v3 by prior
      decision (G1 unresolved); not a blocker.**
- [x] Full-document pass for any remaining v2 language — DONE 2026-07-22
      (review track 1c: CLEAN; three stale version labels fixed).
- [x] Abstract updated (edit 6 above) — verified against the extracted v2
      PDF by review track 1b.
- [ ] Rebuild PDF; on acceptance, freeze v2 source into `versions/v2/` per
      repo convention and update `versions/README.md`.

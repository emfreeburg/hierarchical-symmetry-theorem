/-
Freeburg formalization — Main.lean
The public interface: the principal machine-checked claims of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632 (v3 draft).
-/
import Freeburg.Basic
import Freeburg.BeyondIID
import Freeburg.CompoundPoisson
import Freeburg.Continuous
import Freeburg.Corollaries
import Freeburg.Dirac
import Freeburg.LevyKhintchine
import Freeburg.LogPoissonLaw
import Freeburg.MomentDeterminacy
import Freeburg.Propagation
import Freeburg.PropagationLower
import Freeburg.Stability
import Freeburg.Stretch
import Freeburg.Wasserstein1

/-!
# The checked claims — an interface manifest

This module is the front door of the formalization: the list below *is*
the set of principal machine-checked claims, one anchor per claim.  Each
`example := @…` line elaborates the named constant, so **this file fails
to compile if any principal theorem is renamed or removed** — the
manifest cannot silently rot.  Statements and proofs live in the
modules; the theorem-by-theorem mapping to the paper's numbering, with
all documented deviations, is in `README.md`.

Supporting lemmas outside this list are internal machinery: they are
kernel-checked too (the axiom audit walks *every* constant), but only
the anchors below are maintained as the stable, citable interface.

## The discrete (i.i.d.) theory — §§2–5

* Lemma 1 / Corollary 6 (exponent form, lattice biconditional).
* Proposition 5 (converse: log-Poisson satisfies A1).
* Lemma 2 (boundedness `essSup V = r^{γk}`; Hausdorff determinacy).
* Theorem 3(ii) (the law is log-Poisson: characterization at law level).
* Theorem 7 (forward classification: A1 forces the log-Poisson
  generator `ν = λδ_b` within the log-ID class).
* Theorem 10 (stability, both readings, with the sharp constants
  `(1+β)` and `2` attained exactly by endpoint two-atom witnesses;
  Wasserstein form).
* Theorem 11 (unconditional propagation upper bound `W₁ ≤ K∞√ε`).
* Theorem 12 (matching lower bound `W₁ ≥ c₁√ε`).
* The Θ(√ε) capstone (both halves bracketed on the attaining family).

## The continuous theory — §7 (v3)

* Theorem 17(i) (impersonation: the exact-rational three-atom continuum
  on `{0,1,2}`; the maximal-window two-atom impersonator on
  `{0,1,2,3}`; one-sidedness `ζ₄ ≤ ζ^SL₄` with equality iff CPC; the
  attenuation-only deficit budget `Cβ(1−β)³`).
* Theorem 17(ii) (five-point rigidity: exact `ζ^SL` on `{0,…,4}`
  forces the compound Poisson cascade).
* Theorem 18 forward, route B (from A1 via five lattice moments, under
  hypotheses strictly weaker than (S_c)).
-/

namespace Freeburg.Main

/-! ### Discrete theory anchors -/

example := @Freeburg.satisfiesA1_iff_closed_form
example := @Freeburg.zeta_gamma_C
example := @Freeburg.logPoisson_satisfies_A1
example := @Freeburg.lemma2_boundedness
example := @Freeburg.ext_of_lattice_moments_eq
example := @Freeburg.theorem3_law_uniqueness_W
example := @Freeburg.eq_dirac_of_geometric_moments
example := @Freeburg.theorem7_forward_eta
example := @Freeburg.theorem7_forward_nu
example := @Freeburg.theorem10_step0
example := @Freeburg.theorem10_variance_known
example := @Freeburg.theorem10_variance_fitted
example := @Freeburg.theorem10_wasserstein_known
example := @Freeburg.theorem10_wasserstein_W1
example := @Freeburg.variance_le_sharp
example := @Freeburg.fitted_variance_le_sharp
example := @Freeburg.theorem11_W1_upper
example := @Freeburg.theorem11_rate_upper
example := @Freeburg.theorem11_from_theorem10
example := @Freeburg.theorem12_residual_lower
example := @Freeburg.theorem12_residual_upper
example := @Freeburg.theorem12_W1_lower
example := @Freeburg.theorem12_rate_lower
example := @Freeburg.theorem11_12_theta

/-! ### Beyond-independence anchors (§6, scoped forms) -/

example := @Freeburg.theorem13_asymptotic_classification
example := @Freeburg.theorem14_even_block_moments
example := @Freeburg.theorem14_marginal_ne_logPoisson
example := @Freeburg.corollary15_conditional
example := @Freeburg.theorem16_growth_contradiction
example := @Freeburg.theorem16_scoped

/-! ### Corollary anchors (§7 Cor 19 / §8 Cors 20–23) -/

example := @Freeburg.corollary20_conservation
example := @Freeburg.corollary21_unique_curve
example := @Freeburg.slCurve_hasDerivAt
example := @Freeburg.corollary22_spectrum_width
example := @Freeburg.corollary23_native_stability
example := @Freeburg.corollary23_turbulence

/-! ### Continuous theory anchors (v3 Theorem 17 / Theorem 18) -/

example := @Freeburg.lkPsi_second_diff
example := @Freeburg.theorem17_five_point_rigidity
example := @Freeburg.theorem17_one_sided
example := @Freeburg.theorem17_one_sided_budget
example := @Freeburg.theorem17_impersonation_three_point
example := @Freeburg.nu3_injOn
example := @Freeburg.theorem17_impersonation_four_point
example := @Freeburg.theorem18_forward_fiveMoment

end Freeburg.Main

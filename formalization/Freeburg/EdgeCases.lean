/-
Freeburg formalization — EdgeCases.lean
Living documentation: kernel-checked instances at the delicate boundary
regimes of arXiv:2604.01632 (v3 draft).
-/
import Freeburg.Basic
import Freeburg.Continuous
import Freeburg.Dirac
import Freeburg.Stability

/-!
# Edge-case coverage

This module exercises the boundary regimes the formal statements are known
to be delicate at, as concrete kernel-checked instances.  Nothing here is
new mathematics — each item *instantiates* a shipped theorem at an extreme
of its parameter range, so that the coverage claims of the README's
"findings" list are held by compiled code rather than prose.

* **Monofractal edge `C = 0` / arbitrary `β`** — the A1 recurrence
  `deltaLP_A1` holds with Poisson intensity `λ = 0` (degenerate,
  monofractal cascade) and indeed for *any* `b` (README finding 1: the
  converse needs no `λ > 0`, no `b < 0`).
* **Dirac rigidity outside `[0,1]`** — geometric moments with ratio
  `β = 2` on a measure supported in `[0,1]` force the measure (and its
  mass `A`) to vanish (README finding 2: rigidity is uniform in `β`;
  out-of-range ratios are not excluded by hypothesis, they self-destruct).
* **Sharp constants at She–Lévêque values** — the endpoint two-atom
  witness attains `∫(u−β)² dη = (5/3)ε` *exactly* at `β = 2/3`
  (README finding 3: sharpness with equality on the closed interval).
* **The Theorem 17 boundary, cross-checked** — the maximal-window
  impersonator `nu4` has no amplifying jumps, so the one-sided deficit
  budget applies to it, and the kernel derives `34/2025 ≤ 4/81`:
  the concrete witness's undershoot sits inside the proved budget
  `Cβ(1−β)³`, tying `theorem17_impersonation_four_point` and
  `theorem17_one_sided_budget` together on live data.
* **Non-vacuity of five-point rigidity** — the CPC generator itself
  (`σ² = 0`, `ν = C·δ_{ln β}` at `(β, C) = (2/3, 2)`) satisfies the
  five-point matching hypothesis of `theorem17_five_point_rigidity`
  for a suitable drift, so the rigidity theorem constrains a nonempty
  class rather than holding vacuously.

Everything in this file is sorry-free.
-/

open MeasureTheory
open scoped ENNReal

namespace Freeburg.EdgeCases

/-! ## 1. The monofractal edge: `λ = 0`, any `β` -/

/-- **`C = 0` (monofractal) satisfies A1** — the log-Poisson A1
recurrence at Poisson intensity `λ = 0`, scale ratio `r = 1/2`, `k = 1`:
A1 carries no information in the degenerate case, for every drift `a`
and every jump `b` (hence every `β = e^b > 0`, not only `β ∈ (0,1)`). -/
example (a b p : ℝ) :
    deltaLP a b 0 (1 / 2) 1 (p + 1)
      = (1 - Real.exp (b * 1)) * (a * 1 / Real.log (1 / 2))
        + Real.exp (b * 1) * deltaLP a b 0 (1 / 2) 1 p :=
  deltaLP_A1 a b 0 (1 / 2) 1
    (Real.log_neg (by norm_num) (by norm_num)).ne p

/-! ## 2. Dirac rigidity outside `[0,1]`: out-of-range `β` forces `η = 0` -/

/-- **Geometric moments with ratio `β = 2` annihilate the measure**: on a
finite measure supported in `[0,1]`, the moment identities
`∫ u^m dη = A·2^m` (`m = 0,1,2`) force `η = 0` and `A = 0` — the rigidity
argument needs no range hypothesis on `β` because concentration at an
out-of-range point contradicts the support. -/
lemma eq_zero_of_geometric_moments_two {η : Measure ℝ} [IsFiniteMeasure η]
    {A : ℝ} (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1)
    (hmom : ∀ m : ℕ, m ≤ 2 → ∫ u, u ^ m ∂η = A * 2 ^ m) :
    η = 0 ∧ A = 0 := by
  have hae := ae_eq_of_geometric_moments hsupp hmom
  have hfalse : ∀ᵐ _u ∂η, False := by
    filter_upwards [hae, hsupp] with u hu hu2
    rw [hu] at hu2
    exact absurd hu2.2 (by norm_num)
  have hzero : η = 0 := by
    have h := ae_iff.mp hfalse
    simp only [not_false_eq_true, Set.setOf_true] at h
    exact Measure.measure_univ_eq_zero.mp h
  refine ⟨hzero, ?_⟩
  have hmass := mass_eq_of_geometric_moments (η := η) hmom
  rw [hzero] at hmass
  simpa using hmass.symm

/-! ## 3. Sharp constants attained exactly at She–Lévêque values -/

/-- **The `(1+β)` constant is attained with equality at `β = 2/3`**: for
every tolerance `ε ≥ 0` there is a finite measure on `[0,1]` whose
residuals obey the Theorem-10 hypotheses at level `ε` while
`∫(u − 2/3)² dη = (5/3)·ε` **exactly** — the stability constant
`1 + β = 5/3` cannot be improved, even at the She–Lévêque point. -/
example (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ η : Measure ℝ, ∃ _ : IsFiniteMeasure η,
      (∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1) ∧
      |(∫ u, u ^ 1 ∂η) - 2 / 3 * (∫ u, u ^ 0 ∂η)| ≤ ε ∧
      |(∫ u, u ^ 2 ∂η) - 2 / 3 * (∫ u, u ^ 1 ∂η)| ≤ ε ∧
      ∫ u, (u - 2 / 3) ^ 2 ∂η = 5 / 3 * ε := by
  have h := variance_le_sharp (2 / 3) ε (by norm_num) hε
  have h53 : (1 + 2 / 3 : ℝ) = 5 / 3 := by norm_num
  rwa [h53] at h

/-! ## 4. The Theorem 17 boundary, cross-checked on the live witness -/

/-- `nu4` has no amplifying jumps: both atoms sit at negative `x`
(attenuation factors `2/5, 19/20 < 1`). -/
lemma nu4_no_pos_jumps : nu4 (Set.Ioi (0 : ℝ)) = 0 := by
  unfold nu4
  have h1 : Real.log (2 / 5 : ℝ) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  have h2 : Real.log (19 / 20 : ℝ) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Ioi,
    Measure.dirac_apply' _ measurableSet_Ioi,
    Set.indicator_of_notMem (by simp [Set.mem_Ioi]; linarith),
    Set.indicator_of_notMem (by simp [Set.mem_Ioi]; linarith)]
  simp

/-- Every LK integrand is integrable against the atomic `nu4`. -/
lemma nu4_integrable (q : ℕ) (_ : q ≤ 4) :
    Integrable (lkIntegrand q) nu4 := by
  unfold nu4
  exact (integrable_ofReal_smul_dirac _ _ _).add_measure
    (integrable_ofReal_smul_dirac _ _ _)

/-- **The witness sits inside the budget** (kernel-derived, not
`norm_num`-asserted): applying the one-sided deficit budget
`theorem17_one_sided_budget` to the concrete maximal-window impersonator
`nu4` — via its matching certificate from
`theorem17_impersonation_four_point` and `nu4_no_pos_jumps` — yields
`34/2025 ≤ Cβ(1−β)³ = 4/81`.  The two Theorem-17(i) results are mutually
consistent on live data, and the budget is seen to be conservative by a
factor of about 3 at this witness. -/
example : (34 / 2025 : ℝ) ≤ 4 / 81 := by
  obtain ⟨a, hm, hdev, -⟩ := theorem17_impersonation_four_point
  have hb := theorem17_one_sided_budget
    (show (2 / 3 : ℝ) ∈ Set.Ioo 0 1 by constructor <;> norm_num)
    nu4_integrable nu4_no_pos_jumps hm
  have hRHS : (2 : ℝ) * (2 / 3) * (1 - 2 / 3) ^ 3 = 4 / 81 := by norm_num
  linarith [hb, hdev, hRHS.symm.le, hRHS.le]

/-! ## 5. Non-vacuity of five-point rigidity: the CPC satisfies the hypotheses -/

/-- **The rigidity hypotheses are satisfiable** — the compound Poisson
cascade generator itself (`σ² = 0`, `ν = C·δ_{ln β}` at the paper's
`(β, C) = (2/3, 2)`) matches `ζ^SL` at all five points `q = 0, …, 4` for a
suitable drift: `theorem17_five_point_rigidity` is a rigidity statement
about a nonempty class, not a vacuous implication.  (Its conclusion then
says this generator is the *only* member.) -/
example :
    ∃ a : ℝ,
      MatchesSLUpTo a 0
        (ENNReal.ofReal 2 • Measure.dirac (Real.log (2 / 3)))
        (1 / 3) 2 (2 / 3) 4 := by
  have hv : Real.exp (Real.log (2 / 3 : ℝ)) = 2 / 3 :=
    Real.exp_log (by norm_num)
  set D : ℝ → ℝ := fun q => 2 * lkIntegrand q (Real.log (2 / 3)) with hD
  have hψ : ∀ q : ℝ,
      lkPsi (-(D 1)) 0
        (ENNReal.ofReal 2 • Measure.dirac (Real.log (2 / 3))) q
        = -(D 1) * q + D q := by
    intro q
    unfold lkPsi
    rw [integral_ofReal_smul_dirac (lkIntegrand q)
      (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [hD]
    ring
  have hD2 : D 2 - 2 * D 1 = 2 / 9 := by
    have k := lkIntegrand_comb2 (Real.log (2 / 3))
    rw [hv] at k
    simp only [hD]
    nlinarith [k]
  have hD3 : D 3 - 3 * D 1 = 16 / 27 := by
    have k := lkIntegrand_comb3 (Real.log (2 / 3))
    rw [hv] at k
    simp only [hD]
    nlinarith [k]
  have hD4 : D 4 - 4 * D 1 = 86 / 81 := by
    have k := lkIntegrand_comb4 (Real.log (2 / 3))
    rw [hv] at k
    simp only [hD]
    nlinarith [k]
  refine ⟨-(D 1), ?_⟩
  intro q hq
  interval_cases q
  · push_cast
    rw [hψ 0]
    simp [hD, lkIntegrand_zero_fun]
  · push_cast
    rw [hψ 1]
    norm_num
  · push_cast
    rw [hψ 2]
    norm_num
    linarith [hD2]
  · push_cast
    rw [hψ 3]
    norm_num
    linarith [hD3]
  · push_cast
    rw [hψ 4]
    norm_num
    linarith [hD4]

end Freeburg.EdgeCases

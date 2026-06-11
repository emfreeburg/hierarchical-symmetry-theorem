/-
Freeburg formalization — Stability.lean
Theorem 10 (Stability), Steps 1–3 of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632.
-/
import Freeburg.Basic
import Freeburg.Dirac

/-!
# Stability: the variance identity and the sharp `(1+β)` and `2` bounds

This file quantifies the rigidity proved in `Freeburg.Dirac`: if the
moments of the tilted Lévy measure `η` satisfy the A1 recurrence only
*approximately*, the second moment `∫ (u−β)² dη` is small, with the sharp
constants of Theorem 10 of arXiv:2604.01632, and Cauchy–Schwarz converts
this into a Wasserstein-type bound for the normalized measure.

**Normalization.** We work in the units `|ln r| = 1` (allowed by
Corollary 23 of the paper, where every constant is shown to be
scale-ratio-free).  In these units the signed residuals of
Theorem 10, Step 1 are `ε_m = μ_{m+1} − β μ_m`, where `μ_m = ∫ u^m dη`.

Main results (all sorry-free):

* `Freeburg.variance_identity` — Theorem 10, Step 2 (telescoping):
  `∫ (u−β)² dη = ε₁ − β ε₀`.
* `Freeburg.variance_le_of_residual_bounds` — reading (i) of Theorem 10:
  `|ε₀| ≤ ε` and `|ε₁| ≤ ε` give `∫ (u−β)² dη ≤ (1+β) ε`.
* `Freeburg.variance_le_of_fitted_residual_bounds` — reading (ii)
  (fitted `d^*`): residuals `h_m = ε_m − t` against an offset `t` with
  `|h₀|, |h₁|, |t| ≤ ε` give `∫ (u−β)² dη ≤ 2ε`, via the cancellation
  `ε₁ − β ε₀ = (h₁ − β h₀) + (1−β) t`.
* `Freeburg.sq_integral_abs_le` — the Cauchy–Schwarz step
  `(∫ |f| dη)² ≤ η(univ) ∫ f² dη`, proved self-containedly through the
  quadratic-discriminant argument.
* `Freeburg.abs_moment_le`, `Freeburg.normalized_abs_moment_le` —
  Theorem 10, Step 3: the first-absolute-moment (= `W₁`-to-`δ_β`) bounds
  `∫ |u−β| dη ≤ √(‖η‖ (1+β) ε)` and
  `‖η‖⁻¹ ∫ |u−β| dη ≤ √((1+β) ε / ‖η‖)`.

For a Dirac target the `W₁` distance *is* the first absolute moment:
`W₁(η/‖η‖, δ_β) = ‖η‖⁻¹ ∫ |u−β| dη`; we state the conclusion in the
latter elementary form rather than invoking a Wasserstein library.
-/

open MeasureTheory

namespace Freeburg

variable {η : Measure ℝ} [IsFiniteMeasure η]

/-! ## The variance identity (Theorem 10, Step 2) -/

/-- **Theorem 10, Step 2 (telescoping variance identity)** of
arXiv:2604.01632, in the normalization `|ln r| = 1`:
`∫ (u−β)² dη = (μ₂ − β μ₁) − β (μ₁ − β μ₀) = ε₁ − β ε₀`. -/
theorem variance_identity (β : ℝ)
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1) :
    ∫ u, (u - β) ^ 2 ∂η
      = ((∫ u, u ^ 2 ∂η) - β * (∫ u, u ^ 1 ∂η))
        - β * ((∫ u, u ^ 1 ∂η) - β * (∫ u, u ^ 0 ∂η)) := by
  rw [integral_sq_sub β hsupp]; ring

/-- **Theorem 10, reading (i)** of arXiv:2604.01632 (`d^* = δ_∞`, the
true limit known): if both residuals are bounded by `ε`, then
`∫ (u−β)² dη ≤ ε₁ − β ε₀ ≤ (1+β) ε`.  The constant `(1+β)` is sharp
(Remark after Theorem 10 in the paper). -/
theorem variance_le_of_residual_bounds (β ε : ℝ) (hβ : 0 ≤ β)
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1)
    (h₀ : |(∫ u, u ^ 1 ∂η) - β * (∫ u, u ^ 0 ∂η)| ≤ ε)
    (h₁ : |(∫ u, u ^ 2 ∂η) - β * (∫ u, u ^ 1 ∂η)| ≤ ε) :
    ∫ u, (u - β) ^ 2 ∂η ≤ (1 + β) * ε := by
  rw [variance_identity β hsupp]
  have k1 : (∫ u, u ^ 2 ∂η) - β * (∫ u, u ^ 1 ∂η) ≤ ε :=
    le_trans (le_abs_self _) h₁
  have k0 : -ε ≤ (∫ u, u ^ 1 ∂η) - β * (∫ u, u ^ 0 ∂η) :=
    (abs_le.mp h₀).1
  have k2 : β * (-ε) ≤ β * ((∫ u, u ^ 1 ∂η) - β * (∫ u, u ^ 0 ∂η)) :=
    mul_le_mul_of_nonneg_left k0 hβ
  nlinarith [k1, k2]

/-- **Theorem 10, reading (ii)** of arXiv:2604.01632 (fitted `d^*`):
write the hypothesis residuals as `h_m = ε_m − t` where
`t = (1−β)(d^* − δ_∞)` is the offset between the fitted constant and the
true limit.  If `|h₀| ≤ ε`, `|h₁| ≤ ε` and `|t| ≤ ε` (Step 0 of the
paper's proof gives `|t| ≤ ε`), then the cancellation
`ε₁ − β ε₀ = (h₁ − β h₀) + (1−β) t` yields `∫ (u−β)² dη ≤ 2ε`.
The constant `2` is sharp, and for `β < √2 − 1` it cannot be improved to
`(1+β)²` (Remark after Theorem 10 in the paper). -/
theorem variance_le_of_fitted_residual_bounds (β ε t : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (ht : |t| ≤ ε)
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1)
    (h₀ : |(∫ u, u ^ 1 ∂η) - β * (∫ u, u ^ 0 ∂η) - t| ≤ ε)
    (h₁ : |(∫ u, u ^ 2 ∂η) - β * (∫ u, u ^ 1 ∂η) - t| ≤ ε) :
    ∫ u, (u - β) ^ 2 ∂η ≤ 2 * ε := by
  rw [variance_identity β hsupp]
  have k1 : (∫ u, u ^ 2 ∂η) - β * (∫ u, u ^ 1 ∂η) - t ≤ ε :=
    le_trans (le_abs_self _) h₁
  have k0 : -ε ≤ (∫ u, u ^ 1 ∂η) - β * (∫ u, u ^ 0 ∂η) - t :=
    (abs_le.mp h₀).1
  have k2 : β * (-ε) ≤ β * ((∫ u, u ^ 1 ∂η) - β * (∫ u, u ^ 0 ∂η) - t) :=
    mul_le_mul_of_nonneg_left k0 hβ0
  have kt : (1 - β) * t ≤ (1 - β) * ε :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self t) ht) (by linarith)
  nlinarith [k1, k2, kt]

/-! ## The Cauchy–Schwarz step (Theorem 10, Step 3) -/

/-- **Cauchy–Schwarz against the constant function 1**, proved
self-containedly by the quadratic-discriminant argument: for any finite
measure `η` and any `f` with `|f|` and `f²` integrable,
`(∫ |f| dη)² ≤ η(univ) · ∫ f² dη`.
This is the inequality used in Theorem 10, Step 3 of arXiv:2604.01632. -/
theorem sq_integral_abs_le (f : ℝ → ℝ)
    (h1 : Integrable (fun u => |f u|) η)
    (h2 : Integrable (fun u => (f u) ^ 2) η) :
    (∫ u, |f u| ∂η) ^ 2 ≤ η.real Set.univ * ∫ u, (f u) ^ 2 ∂η := by
  set M := η.real Set.univ with hMdef
  set I := ∫ u, |f u| ∂η with hIdef
  set J := ∫ u, (f u) ^ 2 ∂η with hJdef
  -- For every x : 0 ≤ ∫ (x − |f u|)² dη = M x² − 2 I x + J.
  have key : ∀ x : ℝ, 0 ≤ M * (x * x) + (-(2 * I)) * x + J := by
    intro x
    have hfun : (fun u : ℝ => (x - |f u|) ^ 2)
        = fun u : ℝ => x * x + ((-(2 * x)) * |f u| + (f u) ^ 2) := by
      funext u
      rw [sub_sq, sq_abs]
      ring
    have pos : 0 ≤ ∫ u, (x - |f u|) ^ 2 ∂η :=
      integral_nonneg fun u => sq_nonneg _
    have hinner : ∫ u, ((-(2 * x)) * |f u| + (f u) ^ 2) ∂η
        = (-(2 * x)) * I + J := by
      rw [integral_add (h1.const_mul (-(2 * x))) h2, integral_const_mul]
    have houter : ∫ u, (x * x + ((-(2 * x)) * |f u| + (f u) ^ 2)) ∂η
        = (∫ _u, (x * x) ∂η) + ∫ u, ((-(2 * x)) * |f u| + (f u) ^ 2) ∂η :=
      integral_add (integrable_const (x * x)) ((h1.const_mul (-(2 * x))).add h2)
    have expand : ∫ u, (x - |f u|) ^ 2 ∂η
        = M * (x * x) + ((-(2 * x)) * I + J) := by
      rw [hfun, houter, hinner, integral_const, smul_eq_mul]
    rw [expand] at pos
    nlinarith [pos]
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-- **Theorem 10, Step 3 (unnormalized form)** of arXiv:2604.01632,
`|ln r| = 1` units: under the reading-(i) residual bounds, the first
absolute moment of `η` about `β` satisfies
`∫ |u−β| dη ≤ √(‖η‖ · (1+β) ε)`. -/
theorem abs_moment_le (β ε : ℝ) (hβ : 0 ≤ β)
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1)
    (h₀ : |(∫ u, u ^ 1 ∂η) - β * (∫ u, u ^ 0 ∂η)| ≤ ε)
    (h₁ : |(∫ u, u ^ 2 ∂η) - β * (∫ u, u ^ 1 ∂η)| ≤ ε) :
    ∫ u, |u - β| ∂η ≤ Real.sqrt (η.real Set.univ * ((1 + β) * ε)) := by
  have hI0 : 0 ≤ ∫ u, |u - β| ∂η := integral_nonneg fun u => abs_nonneg _
  have hCS : (∫ u, |u - β| ∂η) ^ 2 ≤ η.real Set.univ * ∫ u, (u - β) ^ 2 ∂η :=
    sq_integral_abs_le (fun u => u - β) (integrable_abs_sub β hsupp)
      (integrable_sq_sub β hsupp)
  have hvar : ∫ u, (u - β) ^ 2 ∂η ≤ (1 + β) * ε :=
    variance_le_of_residual_bounds β ε hβ hsupp h₀ h₁
  have key : (∫ u, |u - β| ∂η) ^ 2 ≤ η.real Set.univ * ((1 + β) * ε) :=
    le_trans hCS (mul_le_mul_of_nonneg_left hvar measureReal_nonneg)
  have hrhs : 0 ≤ η.real Set.univ * ((1 + β) * ε) :=
    le_trans (sq_nonneg _) key
  exact (Real.le_sqrt hI0 hrhs).mpr key

/-- **Theorem 10, Step 3 (normalized form)** of arXiv:2604.01632,
`|ln r| = 1` units: under the reading-(i) residual bounds and
`‖η‖ = η(univ) > 0` (nontrivial intermittency; in the paper
`‖η‖ = |A|` exactly), the normalized first absolute moment — which for a
Dirac target equals the Wasserstein-1 distance
`W₁(η/‖η‖, δ_β)` — satisfies
`‖η‖⁻¹ ∫ |u−β| dη ≤ √((1+β) ε / ‖η‖)`.
This is the displayed bound of Theorem 10(i), with the sharp constant
`√((1+β)/‖η‖)` (`= √((1+β)|ln r|/|A|)` after undoing the
normalization). -/
theorem normalized_abs_moment_le (β ε : ℝ) (hβ : 0 ≤ β)
    (hpos : 0 < η.real Set.univ)
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1)
    (h₀ : |(∫ u, u ^ 1 ∂η) - β * (∫ u, u ^ 0 ∂η)| ≤ ε)
    (h₁ : |(∫ u, u ^ 2 ∂η) - β * (∫ u, u ^ 1 ∂η)| ≤ ε) :
    (η.real Set.univ)⁻¹ * ∫ u, |u - β| ∂η
      ≤ Real.sqrt ((1 + β) * ε / η.real Set.univ) := by
  set M := η.real Set.univ with hMdef
  set I := ∫ u, |u - β| ∂η with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun u => abs_nonneg _
  have hCS : I ^ 2 ≤ M * ∫ u, (u - β) ^ 2 ∂η :=
    sq_integral_abs_le (fun u => u - β) (integrable_abs_sub β hsupp)
      (integrable_sq_sub β hsupp)
  have hvar : ∫ u, (u - β) ^ 2 ∂η ≤ (1 + β) * ε :=
    variance_le_of_residual_bounds β ε hβ hsupp h₀ h₁
  have key : I ^ 2 ≤ M * ((1 + β) * ε) :=
    le_trans hCS (mul_le_mul_of_nonneg_left hvar hpos.le)
  have hε0 : 0 ≤ (1 + β) * ε := by nlinarith [sq_nonneg I, hpos]
  have hx0 : 0 ≤ M⁻¹ * I := mul_nonneg (inv_nonneg.mpr hpos.le) hI0
  have hy0 : 0 ≤ (1 + β) * ε / M := div_nonneg hε0 hpos.le
  rw [Real.le_sqrt hx0 hy0]
  have expand : (M⁻¹ * I) ^ 2 = I ^ 2 / M ^ 2 := by
    rw [mul_pow, inv_pow, inv_mul_eq_div]
  rw [expand, div_le_div_iff₀ (by positivity) hpos]
  nlinarith [mul_le_mul_of_nonneg_right key hpos.le]

/-! ## Glue: from the A1 recurrence to the measure statements

The paper converts A1 into moment data via the substitution `u = e^{kx}`:
in the normalization `|ln r| = 1`, Step 4 of Theorem 7 (resp. Step 1 of
Theorem 10) reads `μ_m = ∫ u^m dη = δ_{mk} − δ_∞`.  The next two theorems
take this dictionary as a hypothesis and derive the paper's conclusions
from the results above, exhibiting the classification as the `ε = 0`
case of the stability estimate (Remark closing Section 5 of
arXiv:2604.01632). -/

/-- **Theorem 7, Step 4 (classification, assembled)** of
arXiv:2604.01632, normalization `|ln r| = 1`: if the incremental
exponents satisfy A1 *exactly* and the tilted Lévy measure `η` realizes
the moment dictionary `∫ u^m dη = δ_m − L` (`m ≤ 2` suffices), then `η`
is the Dirac mass `(δ₀ − L) δ_β` — i.e. the generator is log-Poisson.
This is the `ε = 0` case of the variance identity. -/
theorem classification_of_A1 (δ : ℕ → ℝ) (β L : ℝ)
    (hrec : SatisfiesA1 δ β L)
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1)
    (hdict : ∀ m : ℕ, m ≤ 2 → ∫ u, u ^ m ∂η = δ m - L) :
    η = ENNReal.ofReal (δ 0 - L) • Measure.dirac β := by
  refine eq_dirac_of_geometric_moments hsupp fun m hm => ?_
  rw [hdict m hm, delta_closed_form δ β L hrec m]
  ring

/-- **Theorem 10, Steps 1–2 (stability, assembled)** of
arXiv:2604.01632, reading (i), normalization `|ln r| = 1`: if A1 holds
only approximately — `|δ_{m+1} − (1−β) L − β δ_m| ≤ ε` for `m = 0, 1`,
with `L = δ_∞` the true limit — and `η` realizes the moment dictionary,
then the moment residuals `ε_m = μ_{m+1} − β μ_m` coincide with the A1
residuals and `∫ (u−β)² dη ≤ (1+β) ε`. -/
theorem stability_of_approx_A1 (δ : ℕ → ℝ) (β L ε : ℝ) (hβ : 0 ≤ β)
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1)
    (hdict : ∀ m : ℕ, m ≤ 2 → ∫ u, u ^ m ∂η = δ m - L)
    (h0 : |δ 1 - (1 - β) * L - β * δ 0| ≤ ε)
    (h1 : |δ 2 - (1 - β) * L - β * δ 1| ≤ ε) :
    ∫ u, (u - β) ^ 2 ∂η ≤ (1 + β) * ε := by
  refine variance_le_of_residual_bounds β ε hβ hsupp ?_ ?_
  · rw [hdict 1 (by norm_num), hdict 0 (by norm_num)]
    have : δ 1 - L - β * (δ 0 - L) = δ 1 - (1 - β) * L - β * δ 0 := by ring
    rw [this]
    exact h0
  · rw [hdict 2 (by norm_num), hdict 1 (by norm_num)]
    have : δ 2 - L - β * (δ 1 - L) = δ 2 - (1 - β) * L - β * δ 1 := by ring
    rw [this]
    exact h1

/-! ## Sharpness of the constants `(1+β)` and `2`

The Remark after Theorem 10 of arXiv:2604.01632 exhibits the constants
as limits along a two-atom family `c₀ δ_{u₀} + c₁ δ_v`, `u₀ ↓ 0`,
`v ↑ 1`.  On the closed interval `[0,1]` used here, the limiting family
itself is admissible, and equality is *exact*: the endpoint measure
`c₀ δ₀ + c₁ δ₁` realizes residuals `(ε₀, ε₁) = (−ε, ε)` and second
moment exactly `(1+β) ε` (reading (i)), resp. `(0, 2ε)` with offset
`t = ε` and second moment exactly `2ε` (reading (ii)).  Hence neither
constant in the theorems above can be improved. -/

/-- The endpoint two-atom measure `c₀ δ₀ + c₁ δ₁` on `ℝ`. -/
noncomputable def twoAtom (c₀ c₁ : ℝ) : Measure ℝ :=
  ENNReal.ofReal c₀ • Measure.dirac 0 + ENNReal.ofReal c₁ • Measure.dirac 1

instance twoAtom.instIsFiniteMeasure (c₀ c₁ : ℝ) :
    IsFiniteMeasure (twoAtom c₀ c₁) := by
  constructor
  simp only [twoAtom, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

/-- The two-atom measure is concentrated on `[0,1]`. -/
theorem twoAtom_ae_Icc (c₀ c₁ : ℝ) :
    ∀ᵐ u ∂(twoAtom c₀ c₁), u ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  have hs : MeasurableSet {a : ℝ | ¬ a ∈ Set.Icc (0 : ℝ) 1} :=
    measurableSet_Icc.compl
  have h0 : (0 : ℝ) ∉ {a : ℝ | ¬ a ∈ Set.Icc (0 : ℝ) 1} := by
    simp only [Set.mem_setOf_eq, not_not, Set.mem_Icc]
    exact ⟨le_refl 0, zero_le_one⟩
  have h1 : (1 : ℝ) ∉ {a : ℝ | ¬ a ∈ Set.Icc (0 : ℝ) 1} := by
    simp only [Set.mem_setOf_eq, not_not, Set.mem_Icc]
    exact ⟨zero_le_one, le_refl 1⟩
  rw [twoAtom, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' (0 : ℝ) hs, Measure.dirac_apply' (1 : ℝ) hs,
    Set.indicator_of_notMem h0, Set.indicator_of_notMem h1]
  simp

/-- Integrals against the two-atom measure: `∫ f d(c₀δ₀ + c₁δ₁) =
c₀ f(0) + c₁ f(1)` — for *every* `f : ℝ → ℝ` (Dirac integration needs no
measurability). -/
theorem twoAtom_integral (c₀ c₁ : ℝ) (h0 : 0 ≤ c₀) (h1 : 0 ≤ c₁)
    (f : ℝ → ℝ) :
    ∫ u, f u ∂(twoAtom c₀ c₁) = c₀ * f 0 + c₁ * f 1 := by
  have hd0 : Integrable f (Measure.dirac (0 : ℝ)) := integrable_dirac enorm_lt_top
  have hd1 : Integrable f (Measure.dirac (1 : ℝ)) := integrable_dirac enorm_lt_top
  rw [twoAtom,
    integral_add_measure (hd0.smul_measure ENNReal.ofReal_ne_top)
      (hd1.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac, smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal h1]

/-- **Sharpness of the reading-(i) constant `(1+β)`** (Remark after
Theorem 10 of arXiv:2604.01632, taken at its endpoint limit): for every
`β ∈ (0,1)` and `ε ≥ 0` there is a finite measure on `[0,1]` whose
residuals obey the hypotheses of `variance_le_of_residual_bounds`
— realizing the extremal pattern `(ε₀, ε₁) = (−ε, ε)` — while
`∫ (u−β)² dη = (1+β) ε` *exactly*.  The witness is
`η = (2ε/β) δ₀ + (ε/(1−β)) δ₁`. -/
theorem variance_le_sharp (β ε : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hε : 0 ≤ ε) :
    ∃ η : Measure ℝ, ∃ _ : IsFiniteMeasure η,
      (∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1) ∧
      |(∫ u, u ^ 1 ∂η) - β * (∫ u, u ^ 0 ∂η)| ≤ ε ∧
      |(∫ u, u ^ 2 ∂η) - β * (∫ u, u ^ 1 ∂η)| ≤ ε ∧
      ∫ u, (u - β) ^ 2 ∂η = (1 + β) * ε := by
  have hβ0 : (0 : ℝ) < β := hβ.1
  have h1β : (0 : ℝ) < 1 - β := by linarith [hβ.2]
  have hc0 : 0 ≤ 2 * ε / β := by positivity
  have hc1 : 0 ≤ ε / (1 - β) := by positivity
  set η : Measure ℝ := twoAtom (2 * ε / β) (ε / (1 - β)) with hηdef
  have hI : ∀ f : ℝ → ℝ, ∫ u, f u ∂η
      = (2 * ε / β) * f 0 + (ε / (1 - β)) * f 1 := fun f =>
    twoAtom_integral _ _ hc0 hc1 f
  have k0 : (∫ u, u ^ 1 ∂η) - β * (∫ u, u ^ 0 ∂η) = -ε := by
    rw [hI (fun u => u ^ 1), hI (fun u => u ^ 0)]
    norm_num
    field_simp
    ring
  have k1 : (∫ u, u ^ 2 ∂η) - β * (∫ u, u ^ 1 ∂η) = ε := by
    rw [hI (fun u => u ^ 2), hI (fun u => u ^ 1)]
    norm_num
    field_simp
  have kv : ∫ u, (u - β) ^ 2 ∂η = (1 + β) * ε := by
    rw [hI (fun u => (u - β) ^ 2)]
    field_simp
    ring
  exact ⟨η, inferInstance, twoAtom_ae_Icc _ _,
    by rw [k0, abs_neg, abs_of_nonneg hε],
    by rw [k1, abs_of_nonneg hε], kv⟩

/-- **Sharpness of the reading-(ii) constant `2`** (Remark after
Theorem 10 of arXiv:2604.01632, endpoint limit): for every `β ∈ (0,1)`
and `ε ≥ 0` there are a finite measure on `[0,1]` and an offset `t` with
`|t| ≤ ε` whose *fitted* residuals obey the hypotheses of
`variance_le_of_fitted_residual_bounds` — realizing the extremal pattern
`(ε₀, ε₁) = (0, 2ε)`, `t = ε` — while `∫ (u−β)² dη = 2ε` *exactly*.
In particular, for `β < √2 − 1` the reading-(i) constant `(1+β)` is
strictly violated under fitted reading: `2 > (1+β)²` there, which is why
the paper's v1 constant `(1+β)²` had to be repaired.  The witness is
`η = (2ε/β) δ₀ + (2ε/(1−β)) δ₁`. -/
theorem fitted_variance_le_sharp (β ε : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hε : 0 ≤ ε) :
    ∃ η : Measure ℝ, ∃ _ : IsFiniteMeasure η, ∃ t : ℝ,
      (∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1) ∧ |t| ≤ ε ∧
      |(∫ u, u ^ 1 ∂η) - β * (∫ u, u ^ 0 ∂η) - t| ≤ ε ∧
      |(∫ u, u ^ 2 ∂η) - β * (∫ u, u ^ 1 ∂η) - t| ≤ ε ∧
      ∫ u, (u - β) ^ 2 ∂η = 2 * ε := by
  have hβ0 : (0 : ℝ) < β := hβ.1
  have h1β : (0 : ℝ) < 1 - β := by linarith [hβ.2]
  have hc0 : 0 ≤ 2 * ε / β := by positivity
  have hc1 : 0 ≤ 2 * ε / (1 - β) := by positivity
  set η : Measure ℝ := twoAtom (2 * ε / β) (2 * ε / (1 - β)) with hηdef
  have hI : ∀ f : ℝ → ℝ, ∫ u, f u ∂η
      = (2 * ε / β) * f 0 + (2 * ε / (1 - β)) * f 1 := fun f =>
    twoAtom_integral _ _ hc0 hc1 f
  have k0 : (∫ u, u ^ 1 ∂η) - β * (∫ u, u ^ 0 ∂η) = 0 := by
    rw [hI (fun u => u ^ 1), hI (fun u => u ^ 0)]
    norm_num
    field_simp
    ring
  have k1 : (∫ u, u ^ 2 ∂η) - β * (∫ u, u ^ 1 ∂η) = 2 * ε := by
    rw [hI (fun u => u ^ 2), hI (fun u => u ^ 1)]
    norm_num
    field_simp
  have kv : ∫ u, (u - β) ^ 2 ∂η = 2 * ε := by
    rw [hI (fun u => (u - β) ^ 2)]
    field_simp
    ring
  refine ⟨η, inferInstance, ε, twoAtom_ae_Icc _ _, by rw [abs_of_nonneg hε],
    ?_, ?_, kv⟩
  · rw [k0]
    rw [zero_sub, abs_neg, abs_of_nonneg hε]
  · rw [k1]
    have : 2 * ε - ε = ε := by ring
    rw [this, abs_of_nonneg hε]

end Freeburg

/-
Freeburg formalization — Dirac.lean
Theorem 7 (Log-ID Classification), Step 4 of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632.
-/
import Mathlib

/-!
# Geometric moments force a Dirac mass

This file formalizes the *geometric rigidity* at the heart of the
classification theorem (Theorem 7, Step 4 of arXiv:2604.01632): if a
finite nonnegative measure `η` on `[0,1]` (the tilted Lévy measure
`η = (1−u) dν̃` in the compactified coordinates `u = e^{kx}`) has its
first three moments in geometric progression,

  `∫ u^m dη = A β^m`  for `m = 0, 1, 2`,

then the second-moment identity
`∫ (u−β)^2 dη = μ₂ − 2β μ₁ + β² μ₀ = A(β² − 2β² + β²) = 0`
forces `η` to be the Dirac mass `A δ_β`.

Main results:

* `Freeburg.integral_pow_integrable` and friends — integrability of the
  test integrands from the a.e. support hypothesis.
* `Freeburg.integral_sq_sub` — the expansion
  `∫ (u−β)² dη = μ₂ − 2β μ₁ + β² μ₀` (shared with the stability theory).
* `Freeburg.variance_zero_of_geometric_moments` — `∫ (u−β)² dη = 0`.
* `Freeburg.ae_eq_of_geometric_moments` — `u = β` for `η`-a.e. `u`.
* `Freeburg.measure_eq_zero_of_geometric_moments` — `η s = 0` whenever
  `β ∉ s` (no measurability of `s` required).
* `Freeburg.measure_singleton_of_geometric_moments` — `η {β} = A`
  (in `ENNReal.ofReal` and `Measure.real` forms).
* `Freeburg.eq_dirac_of_geometric_moments` — `η = A • δ_β` as measures.

Note that no hypothesis on `β` or `A` is needed beyond the three moment
identities: `A = η(univ) ≥ 0` is automatic, and concentration on `{β}`
holds for any real `β`.  The paper instantiates `β ∈ (0,1)`, `A = |A| > 0`.
Everything in this file is sorry-free.
-/

open MeasureTheory

namespace Freeburg

variable {η : Measure ℝ}

/-! ## Integrability from the support hypothesis -/

/-- On a finite measure concentrated on `[0,1]`, every monomial `u^m` is
integrable. -/
theorem integral_pow_integrable [IsFiniteMeasure η]
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1) (m : ℕ) :
    Integrable (fun u : ℝ => u ^ m) η := by
  refine (integrable_const (1 : ℝ)).mono'
    ((continuous_pow m).aestronglyMeasurable) ?_
  filter_upwards [hsupp] with u hu
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_one₀ (abs_nonneg u) (abs_le.mpr ⟨by linarith [hu.1], hu.2⟩)

/-- On a finite measure concentrated on `[0,1]`, the quadratic test
function `(u − β)²` is integrable. -/
theorem integrable_sq_sub [IsFiniteMeasure η] (β : ℝ)
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun u : ℝ => (u - β) ^ 2) η := by
  refine (integrable_const ((1 + |β|) ^ 2)).mono'
    (((continuous_id.sub continuous_const).pow 2).aestronglyMeasurable) ?_
  filter_upwards [hsupp] with u hu
  rw [Real.norm_eq_abs, abs_pow]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
  calc |u - β| = |u + -β| := by rw [sub_eq_add_neg]
    _ ≤ |u| + |-β| := abs_add_le u (-β)
    _ = |u| + |β| := by rw [abs_neg]
    _ ≤ 1 + |β| := by
        have : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
        linarith

/-- On a finite measure concentrated on `[0,1]`, the absolute deviation
`|u − β|` is integrable. -/
theorem integrable_abs_sub [IsFiniteMeasure η] (β : ℝ)
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun u : ℝ => |u - β|) η := by
  refine (integrable_const (1 + |β|)).mono'
    ((continuous_id.sub continuous_const).abs.aestronglyMeasurable) ?_
  filter_upwards [hsupp] with u hu
  rw [Real.norm_eq_abs, abs_abs]
  calc |u - β| = |u + -β| := by rw [sub_eq_add_neg]
    _ ≤ |u| + |-β| := abs_add_le u (-β)
    _ = |u| + |β| := by rw [abs_neg]
    _ ≤ 1 + |β| := by
        have : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
        linarith

/-! ## The second-moment expansion -/

/-- **The second-moment identity** (Theorem 7, Step 4 and Theorem 10,
Step 2 of arXiv:2604.01632): for a finite measure on `[0,1]`,
`∫ (u−β)² dη = μ₂ − 2β μ₁ + β² μ₀`, where `μ_m = ∫ u^m dη`. -/
theorem integral_sq_sub [IsFiniteMeasure η] (β : ℝ)
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1) :
    ∫ u, (u - β) ^ 2 ∂η
      = (∫ u, u ^ 2 ∂η) - 2 * β * (∫ u, u ^ 1 ∂η)
        + β ^ 2 * (∫ u, u ^ 0 ∂η) := by
  have hi0 := integral_pow_integrable hsupp 0
  have hi1 := integral_pow_integrable hsupp 1
  have hi2 := integral_pow_integrable hsupp 2
  have hfun : (fun u : ℝ => (u - β) ^ 2)
      = fun u : ℝ => u ^ 2 + ((-(2 * β)) * u ^ 1 + β ^ 2 * u ^ 0) := by
    funext u; ring
  have hinner : ∫ u, ((-(2 * β)) * u ^ 1 + β ^ 2 * u ^ 0) ∂η
      = (-(2 * β)) * (∫ u, u ^ 1 ∂η) + β ^ 2 * (∫ u, u ^ 0 ∂η) := by
    rw [integral_add (hi1.const_mul (-(2 * β))) (hi0.const_mul (β ^ 2)),
      integral_const_mul, integral_const_mul]
  have houter : ∫ u, (u ^ 2 + ((-(2 * β)) * u ^ 1 + β ^ 2 * u ^ 0)) ∂η
      = (∫ u, u ^ 2 ∂η)
        + ∫ u, ((-(2 * β)) * u ^ 1 + β ^ 2 * u ^ 0) ∂η :=
    integral_add hi2 ((hi1.const_mul (-(2 * β))).add (hi0.const_mul (β ^ 2)))
  rw [hfun, houter, hinner]
  ring

/-- The zeroth moment is the total mass: `∫ u^0 dη = η(univ)` (as a real
number). -/
theorem integral_pow_zero (η : Measure ℝ) :
    ∫ u, u ^ (0 : ℕ) ∂η = η.real Set.univ := by
  simp

/-! ## Geometric moments ⟹ Dirac (Theorem 7, Step 4) -/

section GeometricMoments

variable [IsFiniteMeasure η] {β A : ℝ}

/-- **Theorem 7, Step 4 (variance identity)** of arXiv:2604.01632:
if `∫ u^m dη = A β^m` for `m = 0, 1, 2`, then
`∫ (u−β)² dη = A(β² − 2β² + β²) = 0`. -/
theorem variance_zero_of_geometric_moments
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1)
    (hmom : ∀ m : ℕ, m ≤ 2 → ∫ u, u ^ m ∂η = A * β ^ m) :
    ∫ u, (u - β) ^ 2 ∂η = 0 := by
  rw [integral_sq_sub β hsupp, hmom 0 (by norm_num), hmom 1 (by norm_num),
    hmom 2 (by norm_num)]
  ring

/-- **Theorem 7, Step 4 (concentration)** of arXiv:2604.01632: since
`(u−β)² > 0` off `{β}` and `η ≥ 0`, the vanishing second moment forces
`u = β` for `η`-a.e. `u`. -/
theorem ae_eq_of_geometric_moments
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1)
    (hmom : ∀ m : ℕ, m ≤ 2 → ∫ u, u ^ m ∂η = A * β ^ m) :
    ∀ᵐ u ∂η, u = β := by
  have hzero := variance_zero_of_geometric_moments hsupp hmom
  have hae : (fun u : ℝ => (u - β) ^ 2) =ᵐ[η] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun u => sq_nonneg (u - β))
      (integrable_sq_sub β hsupp)).mp hzero
  filter_upwards [hae] with u hu
  simp only [Pi.zero_apply] at hu
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hu)

/-- **Theorem 7, Step 4** of arXiv:2604.01632, set form:
`η((0,1) \ {β}) = 0` — indeed `η s = 0` for *every* set `s` avoiding
`β` (no measurability of `s` is required, by outer monotonicity). -/
theorem measure_eq_zero_of_geometric_moments
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1)
    (hmom : ∀ m : ℕ, m ≤ 2 → ∫ u, u ^ m ∂η = A * β ^ m)
    (s : Set ℝ) (hβs : β ∉ s) : η s = 0 := by
  have hae := ae_eq_of_geometric_moments hsupp hmom
  refine measure_mono_null ?_ (ae_iff.mp hae)
  intro u hus
  simp only [Set.mem_setOf_eq]
  intro hu
  exact hβs (hu ▸ hus)

omit [IsFiniteMeasure η] in
/-- The total mass of `η` is `A` (so `A ≥ 0` automatically): from the
`m = 0` moment identity. -/
theorem mass_eq_of_geometric_moments
    (hmom : ∀ m : ℕ, m ≤ 2 → ∫ u, u ^ m ∂η = A * β ^ m) :
    η.real Set.univ = A := by
  have h0 := hmom 0 (by norm_num)
  rw [integral_pow_zero] at h0
  simpa using h0

/-- **Theorem 7, Step 4 (atom mass)** of arXiv:2604.01632:
`η {β} = A`, stated in `ENNReal.ofReal` form. -/
theorem measure_singleton_of_geometric_moments
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1)
    (hmom : ∀ m : ℕ, m ≤ 2 → ∫ u, u ^ m ∂η = A * β ^ m) :
    η {β} = ENNReal.ofReal A := by
  have hcompl : η ({β}ᶜ) = 0 :=
    measure_eq_zero_of_geometric_moments hsupp hmom ({β}ᶜ)
      (by simp)
  have huniv : η {β} = η Set.univ := by
    have h := measure_add_measure_compl (μ := η) (measurableSet_singleton β)
    rwa [hcompl, add_zero] at h
  have hA : η.real Set.univ = A := mass_eq_of_geometric_moments hmom
  rw [huniv, ← hA, Measure.real, ENNReal.ofReal_toReal (measure_ne_top η _)]

/-- `η {β} = A`, stated in `Measure.real` form. -/
theorem real_measure_singleton_of_geometric_moments
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1)
    (hmom : ∀ m : ℕ, m ≤ 2 → ∫ u, u ^ m ∂η = A * β ^ m) :
    η.real {β} = A := by
  have hA0 : 0 ≤ A := by
    rw [← mass_eq_of_geometric_moments hmom]; exact measureReal_nonneg
  rw [Measure.real, measure_singleton_of_geometric_moments hsupp hmom,
    ENNReal.toReal_ofReal hA0]

/-- **Theorem 7, Step 4 (conclusion)** of arXiv:2604.01632: the tilted
measure *is* the Dirac mass, `η = A δ_β`.  (In the paper one then
inverts the tilt `η = (1−u) dν̃` to get `ν̃ = (A/(1−β)) δ_β`, i.e. the
Lévy measure of `log W` is `λ δ_b` with `b = ln β / k`,
`λ = A/(1−β)` — the log-Poisson generator.) -/
theorem eq_dirac_of_geometric_moments
    (hsupp : ∀ᵐ u ∂η, u ∈ Set.Icc (0 : ℝ) 1)
    (hmom : ∀ m : ℕ, m ≤ 2 → ∫ u, u ^ m ∂η = A * β ^ m) :
    η = ENNReal.ofReal A • Measure.dirac β := by
  have hae := ae_eq_of_geometric_moments hsupp hmom
  have hatom := measure_singleton_of_geometric_moments hsupp hmom
  ext s hs
  rw [Measure.smul_apply, Measure.dirac_apply' β hs, smul_eq_mul]
  by_cases hβs : β ∈ s
  · rw [Set.indicator_of_mem hβs, Pi.one_apply, mul_one]
    have hcompl : η (sᶜ) = 0 := by
      refine measure_eq_zero_of_geometric_moments hsupp hmom (sᶜ) ?_
      simp [hβs]
    have huniv : η s = η Set.univ := by
      have h := measure_add_measure_compl (μ := η) hs
      rwa [hcompl, add_zero] at h
    have hsing : η {β} = η Set.univ := by
      have h := measure_add_measure_compl (μ := η) (measurableSet_singleton β)
      have hc : η ({β}ᶜ) = 0 :=
        measure_eq_zero_of_geometric_moments hsupp hmom ({β}ᶜ) (by simp)
      rwa [hc, add_zero] at h
    rw [huniv, ← hsing, hatom]
  · rw [Set.indicator_of_notMem hβs, mul_zero]
    exact measure_eq_zero_of_geometric_moments hsupp hmom s hβs

end GeometricMoments

end Freeburg

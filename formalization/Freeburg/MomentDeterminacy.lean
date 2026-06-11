/-
Freeburg formalization — MomentDeterminacy.lean
Lemma 2(ii) (Moment Determinacy) of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632.
-/
import Mathlib

/-!
# Hausdorff moment determinacy on a compact interval

Lemma 2(ii) of the paper: a probability law supported in the compact
interval `[0, M]` is uniquely determined by its integer moments
(Hausdorff moment problem), and — because A1 constrains only the moments
along the lattice `p ∈ kℕ₀` — already by the lattice moments of the
`k`-th power.

The proof is the classical one, exactly as in the paper: polynomials are
uniformly dense in `C([0, M])` (Weierstrass approximation), so two
finite measures with equal moments integrate every continuous function
equally, and finite Borel measures on a metric space are determined by
their integrals against bounded continuous functions.

Main results:

* `Freeburg.integrable_of_ae_Icc` — continuous functions are integrable
  against finite measures concentrated on `[0, M]`.
* `Freeburg.integral_polynomial_eq_of_moments` — equal moments give
  equal polynomial integrals.
* `Freeburg.ext_of_moments_eq` — **Hausdorff determinacy**: finite Borel
  measures concentrated on `[0, M]` with equal moments coincide.
* `Freeburg.ext_of_lattice_moments_eq` — the `k`-lattice version, by
  pushing forward along `x ↦ x^k`, applying determinacy on `[0, M^k]`,
  and inverting via `y ↦ y^{1/k}` on the support: laws of nonnegative
  bounded multipliers are determined by the A1-constrained moments
  alone.

Everything in this file is sorry-free.
-/

open MeasureTheory
open scoped BoundedContinuousFunction

namespace Freeburg

variable {μ ν : Measure ℝ} {M : ℝ}

/-! ## Integrability against finite measures on `[0, M]` -/

/-- Any continuous function is integrable against a finite measure
concentrated on the compact interval `[0, M]`. -/
theorem integrable_of_ae_Icc [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) M)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable g μ := by
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_bound_of_continuousOn
      hg.continuousOn
  refine (integrable_const B).mono' hg.aestronglyMeasurable ?_
  filter_upwards [hsupp] with x hx
  exact hB x hx

/-! ## Equal moments give equal polynomial integrals -/

/-- Two finite measures concentrated on `[0, M]` with equal moments
integrate every polynomial equally. -/
theorem integral_polynomial_eq_of_moments [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) M)
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) M)
    (hmom : ∀ m : ℕ, ∫ x, x ^ m ∂μ = ∫ x, x ^ m ∂ν)
    (p : Polynomial ℝ) :
    ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂ν := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hpμ : Integrable (fun x => p.eval x) μ :=
        integrable_of_ae_Icc hμ p.continuous
      have hqμ : Integrable (fun x => q.eval x) μ :=
        integrable_of_ae_Icc hμ q.continuous
      have hpν : Integrable (fun x => p.eval x) ν :=
        integrable_of_ae_Icc hν p.continuous
      have hqν : Integrable (fun x => q.eval x) ν :=
        integrable_of_ae_Icc hν q.continuous
      simp only [Polynomial.eval_add]
      rw [integral_add hpμ hqμ, integral_add hpν hqν, hp, hq]
  | monomial n a =>
      simp only [Polynomial.eval_monomial]
      rw [integral_const_mul, integral_const_mul, hmom n]

/-! ## Hausdorff determinacy -/

/-- **Hausdorff moment determinacy on `[0, M]`** (Lemma 2(ii) of the
paper, abstract form): two finite Borel measures on `ℝ`, both
concentrated on the compact interval `[0, M]`, with equal integer
moments, are equal.  This is the classical Weierstrass–Riesz argument:
approximate any bounded continuous `f` uniformly on `[0, M]` by a
polynomial, whose integrals against the two measures agree. -/
theorem ext_of_moments_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) M)
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) M)
    (hmom : ∀ m : ℕ, ∫ x, x ^ m ∂μ = ∫ x, x ^ m ∂ν) :
    μ = ν := by
  have key : ∀ f : ℝ →ᵇ ℝ, ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
    intro f
    set K : ℝ := μ.real Set.univ + ν.real Set.univ with hKdef
    -- ε-estimate via a Weierstrass polynomial
    have hdiff : ∀ ε : ℝ, 0 < ε →
        |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ ε * K := by
      intro ε hε
      obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 M
        (fun x => f x) f.continuous.continuousOn ε hε
      have hfμ : Integrable (fun x => f x) μ := f.integrable μ
      have hfν : Integrable (fun x => f x) ν := f.integrable ν
      have hpμ : Integrable (fun x => p.eval x) μ :=
        integrable_of_ae_Icc hμ p.continuous
      have hpν : Integrable (fun x => p.eval x) ν :=
        integrable_of_ae_Icc hν p.continuous
      have hbμ : |(∫ x, f x ∂μ) - ∫ x, p.eval x ∂μ| ≤ ε * μ.real Set.univ := by
        rw [← integral_sub hfμ hpμ]
        calc |∫ x, (f x - p.eval x) ∂μ|
            ≤ ∫ x, |f x - p.eval x| ∂μ := abs_integral_le_integral_abs
          _ ≤ ∫ _x, ε ∂μ := by
              refine integral_mono_ae (hfμ.sub hpμ).abs (integrable_const ε) ?_
              filter_upwards [hμ] with x hx
              rw [abs_sub_comm]
              exact (hp x hx).le
          _ = ε * μ.real Set.univ := by
              rw [integral_const, smul_eq_mul, mul_comm]
      have hbν : |(∫ x, f x ∂ν) - ∫ x, p.eval x ∂ν| ≤ ε * ν.real Set.univ := by
        rw [← integral_sub hfν hpν]
        calc |∫ x, (f x - p.eval x) ∂ν|
            ≤ ∫ x, |f x - p.eval x| ∂ν := abs_integral_le_integral_abs
          _ ≤ ∫ _x, ε ∂ν := by
              refine integral_mono_ae (hfν.sub hpν).abs (integrable_const ε) ?_
              filter_upwards [hν] with x hx
              rw [abs_sub_comm]
              exact (hp x hx).le
          _ = ε * ν.real Set.univ := by
              rw [integral_const, smul_eq_mul, mul_comm]
      have hpeq := integral_polynomial_eq_of_moments hμ hν hmom p
      calc |(∫ x, f x ∂μ) - ∫ x, f x ∂ν|
          ≤ |(∫ x, f x ∂μ) - ∫ x, p.eval x ∂μ|
              + |(∫ x, p.eval x ∂μ) - ∫ x, f x ∂ν| := abs_sub_le _ _ _
        _ = |(∫ x, f x ∂μ) - ∫ x, p.eval x ∂μ|
              + |(∫ x, f x ∂ν) - ∫ x, p.eval x ∂ν| := by
            congr 1
            rw [hpeq, abs_sub_comm]
        _ ≤ ε * μ.real Set.univ + ε * ν.real Set.univ := add_le_add hbμ hbν
        _ = ε * K := by rw [hKdef]; ring
    -- let ε ↓ 0 along 1/(n+1)
    have hseq : ∀ n : ℕ,
        |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ K * (1 / ((n : ℝ) + 1)) := by
      intro n
      have h := hdiff (1 / ((n : ℝ) + 1)) (by positivity)
      linarith
    have hlim : Filter.Tendsto (fun n : ℕ => K * (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul K
    have habs : |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ 0 := ge_of_tendsto' hlim hseq
    exact sub_eq_zero.mp (abs_nonpos_iff.mp habs)
  -- bundle as finite measures and apply the bounded-continuous ext theorem
  have hbundle : (⟨μ, ‹IsFiniteMeasure μ›⟩ : FiniteMeasure ℝ)
      = (⟨ν, ‹IsFiniteMeasure ν›⟩ : FiniteMeasure ℝ) :=
    FiniteMeasure.ext_of_forall_integral_eq (fun f => key f)
  exact congrArg FiniteMeasure.toMeasure hbundle

/-! ## The lattice version (what A1 actually constrains) -/

/-- **Lemma 2(ii)** of the paper, lattice form: two finite Borel
measures concentrated on `[0, M]` with equal moments along the lattice
`{k·m : m ∈ ℕ₀}` — the only moments A1 constrains when `k ≥ 2` — are
equal.  Proof: push forward along `x ↦ x^k` (which converts lattice
moments into all moments), apply Hausdorff determinacy on `[0, M^k]`,
and invert via `y ↦ y^{1/k}` on the support. -/
theorem ext_of_lattice_moments_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {k : ℕ} (hk : k ≠ 0)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) M)
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) M)
    (hmom : ∀ m : ℕ, ∫ x, x ^ (k * m) ∂μ = ∫ x, x ^ (k * m) ∂ν) :
    μ = ν := by
  have hT : Measurable fun x : ℝ => x ^ k := (continuous_pow k).measurable
  have hS : Measurable fun y : ℝ => y ^ ((k : ℝ)⁻¹) :=
    (Real.continuous_rpow_const (by positivity)).measurable
  -- the pushforwards live on [0, M^k] …
  have hmap : ∀ ρ : Measure ℝ, (∀ᵐ x ∂ρ, x ∈ Set.Icc (0 : ℝ) M) →
      ∀ᵐ y ∂(ρ.map fun x : ℝ => x ^ k), y ∈ Set.Icc (0 : ℝ) (M ^ k) := by
    intro ρ hρ
    refine (MeasureTheory.ae_map_iff hT.aemeasurable ?_).mpr ?_
    · exact measurableSet_Icc
    · filter_upwards [hρ] with x hx
      exact ⟨pow_nonneg hx.1 k, pow_le_pow_left₀ hx.1 hx.2 k⟩
  -- … and have equal (all-index) moments
  have hmommap : ∀ m : ℕ,
      (∫ y, y ^ m ∂(μ.map fun x : ℝ => x ^ k))
        = ∫ y, y ^ m ∂(ν.map fun x : ℝ => x ^ k) := by
    intro m
    rw [integral_map hT.aemeasurable (continuous_pow m).aestronglyMeasurable,
      integral_map hT.aemeasurable (continuous_pow m).aestronglyMeasurable]
    simp only [← pow_mul]
    exact hmom m
  have hmaps : μ.map (fun x : ℝ => x ^ k) = ν.map (fun x : ℝ => x ^ k) :=
    ext_of_moments_eq (hmap μ hμ) (hmap ν hν) hmommap
  -- invert on the support
  have hinvert : ∀ ρ : Measure ℝ, (∀ᵐ x ∂ρ, x ∈ Set.Icc (0 : ℝ) M) →
      (ρ.map fun x : ℝ => x ^ k).map (fun y : ℝ => y ^ ((k : ℝ)⁻¹)) = ρ := by
    intro ρ hρ
    rw [Measure.map_map hS hT]
    have hae : (fun y : ℝ => y ^ ((k : ℝ)⁻¹)) ∘ (fun x : ℝ => x ^ k) =ᵐ[ρ] id := by
      filter_upwards [hρ] with x hx
      simp only [Function.comp_apply, id_eq]
      exact Real.pow_rpow_inv_natCast hx.1 hk
    rw [Measure.map_congr hae, Measure.map_id]
  calc μ = (μ.map fun x : ℝ => x ^ k).map (fun y : ℝ => y ^ ((k : ℝ)⁻¹)) :=
        (hinvert μ hμ).symm
    _ = (ν.map fun x : ℝ => x ^ k).map (fun y : ℝ => y ^ ((k : ℝ)⁻¹)) := by
        rw [hmaps]
    _ = ν := hinvert ν hν

end Freeburg

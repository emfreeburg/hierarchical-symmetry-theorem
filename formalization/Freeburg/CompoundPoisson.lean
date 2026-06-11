/-
Freeburg formalization — CompoundPoisson.lean
The compound-Poisson toolkit for §5 of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632.
-/
import Mathlib

/-!
# Two-atom compound-Poisson multipliers and Poisson superposition

Mathlib has no compound-Poisson or Poisson-point-process theory.  The
paper's Theorem 12 needs none: by the marked-Poisson (superposition)
decomposition, the compound-Poisson multiplier over a **two-atom** Lévy
measure `ν̃ = λ₁δ_s + λ₂δ_t` is the pushforward of two *independent*
Poisson counts,

  `W = e^c · s^{N₁} · t^{N₂}`,  `N₁ ~ Poisson(λ₁)`, `N₂ ~ Poisson(λ₂)`.

This file builds that object directly on Mathlib's `poissonMeasure` and
certifies it against the paper's description three ways:

* **superposition** (`poissonMeasure_prod_map_add`): the total jump
  count `N₁ + N₂` is `Poisson(λ₁ + λ₂)` — the law-level content of the
  marked decomposition;
* **cumulant identity** (`integral_pow_twoAtomCPLaw_CGF`):
  `E[W^m] = exp(cm + ∫(u^m − 1) dν̃)` — the defining compound-Poisson
  cumulant form, with `ν̃` the actual two-atom Lévy measure;
* **conservation** (`integral_twoAtomCPLaw_eq_one`): the drift
  `c = ∫(1−u) dν̃` gives `E[W] = 1`, the paper's normalization.

Also here: the Poisson generating function
(`integral_pow_poissonMeasure`), the de-tilting computation
`ν̃.withDensity (1−u) = η` for two-atom measures
(`twoAtomLevy_withDensity_tilt`), and the telescoping product
inequality `|∏sᵢ − ∏tᵢ| ≤ Σ|sᵢ − tᵢ|` on `[0,1]`
(`abs_prod_sub_prod_le`) used by the multiplicative couplings of
Theorem 11.  (Wald's identity for Poisson-counted i.i.d. sums is
deferred to the coupling construction in `Propagation.lean` that
consumes it.)

Everything in this file is sorry-free.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Nat

namespace Freeburg

/-! ## The Poisson generating function -/

/-- The **Poisson probability generating function**:
`E[x^N] = exp(λ(x−1))` for `N ~ Poisson(λ)`, any real `x`. -/
theorem integral_pow_poissonMeasure (lam : ℝ≥0) (x : ℝ) :
    ∫ n, x ^ n ∂(poissonMeasure lam) = Real.exp ((lam : ℝ) * (x - 1)) := by
  rw [integral_poissonMeasure]
  have hterm : ∀ n : ℕ,
      (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / n !) • x ^ n
        = Real.exp (-(lam : ℝ)) * (((lam : ℝ) * x) ^ n / n !) := by
    intro n
    rw [smul_eq_mul, mul_pow]
    ring
  rw [tsum_congr hterm, tsum_mul_left,
    (NormedSpace.expSeries_div_hasSum_exp ((lam : ℝ) * x)).tsum_eq,
    ← Real.exp_eq_exp_ℝ, ← Real.exp_add]
  congr 1
  ring

/-! ## Poisson superposition -/

/-- **Poisson superposition**: the sum of two independent Poisson
counts is Poisson with the summed rate,
`(N₁, N₂) ↦ N₁ + N₂` pushes `Poisson(λ₁) ⊗ Poisson(λ₂)` to
`Poisson(λ₁ + λ₂)`.  This is the law-level content of the marked
decomposition of a compound-Poisson process into its atoms. -/
theorem poissonMeasure_prod_map_add (l1 l2 : ℝ≥0) :
    ((poissonMeasure l1).prod (poissonMeasure l2)).map
        (fun p : ℕ × ℕ => p.1 + p.2)
      = poissonMeasure (l1 + l2) := by
  refine Measure.ext_of_singleton fun n => ?_
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton n),
    poissonMeasure_singleton]
  -- the fiber over `n` is the finite antidiagonal
  have hpre : (fun p : ℕ × ℕ => p.1 + p.2) ⁻¹' {n}
      = ⋃ i ∈ Finset.range (n + 1), ({((i, n - i) : ℕ × ℕ)} : Set (ℕ × ℕ)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Finset.mem_range, Prod.ext_iff]
    constructor
    · intro h
      exact ⟨p.1, by omega, rfl, by omega⟩
    · rintro ⟨i, hi, h1, h2⟩
      omega
  rw [hpre, measure_biUnion_finset ?_ (fun i _ => measurableSet_singleton _)]
  swap
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Set.disjoint_singleton]
    exact fun h => hij (congrArg Prod.fst h)
  -- each fiber point is a product rectangle
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ((poissonMeasure l1).prod (poissonMeasure l2))
          ({((i, n - i) : ℕ × ℕ)} : Set (ℕ × ℕ))
        = ENNReal.ofReal ((Real.exp (-(l1 : ℝ)) * (l1 : ℝ) ^ i / i !)
            * (Real.exp (-(l2 : ℝ)) * (l2 : ℝ) ^ (n - i) / (n - i)!)) := by
    intro i _
    rw [← Set.singleton_prod_singleton, Measure.prod_prod,
      poissonMeasure_singleton, poissonMeasure_singleton,
      ← ENNReal.ofReal_mul (by positivity)]
  rw [Finset.sum_congr rfl hterm,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  congr 1
  -- the real Vandermonde identity, by the binomial theorem
  have key : ∀ i ∈ Finset.range (n + 1),
      Real.exp (-(l1 : ℝ)) * (l1 : ℝ) ^ i / i !
          * (Real.exp (-(l2 : ℝ)) * (l2 : ℝ) ^ (n - i) / (n - i)!)
        = (Real.exp (-(l1 : ℝ)) * Real.exp (-(l2 : ℝ)))
            * ((l1 : ℝ) ^ i * (l2 : ℝ) ^ (n - i) * (n.choose i : ℝ) / n !) := by
    intro i hi
    have hle : i ≤ n := Finset.mem_range_succ_iff.mp hi
    have hch : ((n.choose i : ℕ) : ℝ) * (i ! : ℝ) * ((n - i)! : ℝ) = (n ! : ℝ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℝ))
        (Nat.choose_mul_factorial_mul_factorial hle)
    have hi0 : (0 : ℝ) < (i ! : ℝ) := by positivity
    have hni0 : (0 : ℝ) < ((n - i)! : ℝ) := by positivity
    have hn0 : (0 : ℝ) < (n ! : ℝ) := by positivity
    have hdiv : (1 : ℝ) / ((i ! : ℝ) * ((n - i)! : ℝ)) = (n.choose i : ℝ) / (n ! : ℝ) := by
      rw [div_eq_div_iff (mul_pos hi0 hni0).ne' hn0.ne', one_mul]
      linear_combination -hch
    calc Real.exp (-(l1 : ℝ)) * (l1 : ℝ) ^ i / i !
          * (Real.exp (-(l2 : ℝ)) * (l2 : ℝ) ^ (n - i) / (n - i)!)
        = (Real.exp (-(l1 : ℝ)) * Real.exp (-(l2 : ℝ)))
            * ((l1 : ℝ) ^ i * (l2 : ℝ) ^ (n - i)
              * ((1 : ℝ) / ((i ! : ℝ) * ((n - i)! : ℝ)))) := by ring
      _ = (Real.exp (-(l1 : ℝ)) * Real.exp (-(l2 : ℝ)))
            * ((l1 : ℝ) ^ i * (l2 : ℝ) ^ (n - i) * ((n.choose i : ℝ) / (n ! : ℝ))) := by
          rw [hdiv]
      _ = (Real.exp (-(l1 : ℝ)) * Real.exp (-(l2 : ℝ)))
            * ((l1 : ℝ) ^ i * (l2 : ℝ) ^ (n - i) * (n.choose i : ℝ) / n !) := by
          ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  have hbinom : ∑ i ∈ Finset.range (n + 1),
        (l1 : ℝ) ^ i * (l2 : ℝ) ^ (n - i) * (n.choose i : ℝ) / n !
      = ((l1 : ℝ) + (l2 : ℝ)) ^ n / n ! := by
    rw [← Finset.sum_div, ← add_pow]
  rw [hbinom, ← Real.exp_add,
    show -(l1 : ℝ) + -(l2 : ℝ) = -((l1 : ℝ) + (l2 : ℝ)) by ring]
  push_cast
  ring

/-! ## The two-atom compound-Poisson multiplier -/

/-- The **two-atom compound-Poisson multiplier law**: the distribution
of `W = e^c · s^{N₁} · t^{N₂}` with independent `N₁ ~ Poisson(λ₁)`,
`N₂ ~ Poisson(λ₂)` — by superposition, the compound-Poisson product
over the Lévy measure `λ₁δ_s + λ₂δ_t` with drift `e^c`. -/
noncomputable def twoAtomCPLaw (c s t : ℝ) (l1 l2 : ℝ≥0) : Measure ℝ :=
  ((poissonMeasure l1).prod (poissonMeasure l2)).map
    fun p : ℕ × ℕ => Real.exp c * s ^ p.1 * t ^ p.2

instance isProbabilityMeasure_twoAtomCPLaw (c s t : ℝ) (l1 l2 : ℝ≥0) :
    IsProbabilityMeasure (twoAtomCPLaw c s t l1 l2) := by
  unfold twoAtomCPLaw
  exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

/-- For jump factors in `[0,1]` the two-atom compound-Poisson
multiplier is concentrated on the compact interval `[0, e^c]`
(Lemma 2(i): the multiplier is bounded by its drift factor). -/
theorem twoAtomCPLaw_ae_mem_Icc (c : ℝ) {s t : ℝ} (l1 l2 : ℝ≥0)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ w ∂(twoAtomCPLaw c s t l1 l2), w ∈ Set.Icc (0 : ℝ) (Real.exp c) := by
  unfold twoAtomCPLaw
  refine (MeasureTheory.ae_map_iff Measurable.of_discrete.aemeasurable
    measurableSet_Icc).mpr ?_
  refine Filter.Eventually.of_forall fun p => ⟨?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (Real.exp_pos c).le (pow_nonneg hs.1 _))
      (pow_nonneg ht.1 _)
  · have h1 : s ^ p.1 ≤ 1 := pow_le_one₀ hs.1 hs.2
    have h2 : t ^ p.2 ≤ 1 := pow_le_one₀ ht.1 ht.2
    calc Real.exp c * s ^ p.1 * t ^ p.2
        ≤ Real.exp c * 1 * 1 := by
          refine mul_le_mul (mul_le_mul le_rfl h1 (pow_nonneg hs.1 _)
            (Real.exp_pos c).le) h2 (pow_nonneg ht.1 _) ?_
          positivity
      _ = Real.exp c := by ring

/-- **The two-atom compound-Poisson moment formula**:
`E[W^m] = exp(cm + λ₁(s^m − 1) + λ₂(t^m − 1))` — two Poisson
generating functions through the product structure. -/
theorem integral_pow_twoAtomCPLaw (c s t : ℝ) (l1 l2 : ℝ≥0) (m : ℕ) :
    ∫ w, w ^ m ∂(twoAtomCPLaw c s t l1 l2)
      = Real.exp (c * m + (l1 : ℝ) * (s ^ m - 1) + (l2 : ℝ) * (t ^ m - 1)) := by
  rw [twoAtomCPLaw, integral_map Measurable.of_discrete.aemeasurable
    (continuous_pow m).aestronglyMeasurable]
  have hterm : (fun p : ℕ × ℕ => (Real.exp c * s ^ p.1 * t ^ p.2) ^ m)
      = fun p : ℕ × ℕ =>
          Real.exp (c * m) * ((fun n => (s ^ m) ^ n) p.1 * (fun n => (t ^ m) ^ n) p.2) := by
    funext p
    have h1 : (Real.exp c) ^ m = Real.exp (c * m) := by
      rw [← Real.exp_nat_mul, mul_comm]
    have h2 : (s ^ p.1) ^ m = (s ^ m) ^ p.1 := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    have h3 : (t ^ p.2) ^ m = (t ^ m) ^ p.2 := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [mul_pow, mul_pow, h1, h2, h3]
    ring
  rw [hterm, integral_const_mul, integral_prod_mul,
    integral_pow_poissonMeasure, integral_pow_poissonMeasure,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- **Conservation**: with the drift fixed by `c = λ₁(1−s) + λ₂(1−t)`
(the paper's `a = ∫(1−u) dν̃`), the multiplier has unit mean. -/
theorem integral_twoAtomCPLaw_eq_one (c s t : ℝ) (l1 l2 : ℝ≥0)
    (hdrift : c = (l1 : ℝ) * (1 - s) + (l2 : ℝ) * (1 - t)) :
    ∫ w, w ∂(twoAtomCPLaw c s t l1 l2) = 1 := by
  have h := integral_pow_twoAtomCPLaw c s t l1 l2 1
  simp only [pow_one, Nat.cast_one, mul_one] at h
  rw [h, hdrift, show (l1 : ℝ) * (1 - s) + (l2 : ℝ) * (1 - t)
      + (l1 : ℝ) * (s - 1) + (l2 : ℝ) * (t - 1) = 0 by ring, Real.exp_zero]

/-! ## The two-atom Lévy measure and the cumulant identity -/

/-- The **two-atom Lévy measure** `ν̃ = λ₁δ_s + λ₂δ_t` in the
multiplicative `u`-coordinate. -/
noncomputable def twoAtomLevy (s t : ℝ) (l1 l2 : ℝ≥0) : Measure ℝ :=
  (l1 : ℝ≥0∞) • Measure.dirac s + (l2 : ℝ≥0∞) • Measure.dirac t

/-- Integration against the two-atom Lévy measure. -/
theorem integral_twoAtomLevy (s t : ℝ) (l1 l2 : ℝ≥0) (f : ℝ → ℝ) :
    ∫ u, f u ∂(twoAtomLevy s t l1 l2) = (l1 : ℝ) * f s + (l2 : ℝ) * f t := by
  unfold twoAtomLevy
  rw [integral_add_measure
      ((integrable_dirac enorm_lt_top).smul_measure ENNReal.coe_ne_top)
      ((integrable_dirac enorm_lt_top).smul_measure ENNReal.coe_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp [smul_eq_mul]

/-- **The compound-Poisson cumulant identity**: the two-Poisson
construction realizes exactly the compound-Poisson cumulant form
`E[W^m] = exp(cm + ∫(u^m − 1) dν̃)` over its two-atom Lévy measure —
the faithfulness certificate identifying `twoAtomCPLaw` with the
paper's "compound-Poisson multiplier with Lévy measure `ν̃`". -/
theorem integral_pow_twoAtomCPLaw_CGF (c s t : ℝ) (l1 l2 : ℝ≥0) (m : ℕ) :
    ∫ w, w ^ m ∂(twoAtomCPLaw c s t l1 l2)
      = Real.exp (c * m + ∫ u, (u ^ m - 1) ∂(twoAtomLevy s t l1 l2)) := by
  rw [integral_pow_twoAtomCPLaw, integral_twoAtomLevy]
  congr 1
  ring

/-- **De-tilting a two-atom Lévy measure**: multiplying `ν̃ = λ₁δ_s + λ₂δ_t`
by a density `g` reweights the atoms, `ν̃·g = (λ₁ g(s))δ_s + (λ₂ g(t))δ_t`.
With `g = 1 − u` this is the paper's tilt `η = (1−u) dν̃`. -/
theorem twoAtomLevy_withDensity_tilt (s t : ℝ) (l1 l2 : ℝ≥0) (g : ℝ → ℝ≥0∞) :
    (twoAtomLevy s t l1 l2).withDensity g
      = ((l1 : ℝ≥0∞) * g s) • Measure.dirac s
          + ((l2 : ℝ≥0∞) * g t) • Measure.dirac t := by
  unfold twoAtomLevy
  rw [withDensity_add_measure, withDensity_smul_measure, withDensity_smul_measure,
    dirac_withDensity, dirac_withDensity, smul_smul, smul_smul]

/-! ## The telescoping product inequality -/

/-- **Telescoping products on `[0,1]`**:
`|∏ᵢ sᵢ − ∏ᵢ tᵢ| ≤ Σᵢ |sᵢ − tᵢ|` — the multiplicative coupling cost of
Theorem 11 (finite form; the infinite-product version is a monotone
limit taken in `Propagation.lean`'s layered construction). -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, f i ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ i ∈ s, g i ∈ Set.Icc (0 : ℝ) 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa := hf a (Finset.mem_insert_self a s)
    have hga := hg a (Finset.mem_insert_self a s)
    have hf' : ∀ i ∈ s, f i ∈ Set.Icc (0 : ℝ) 1 :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' : ∀ i ∈ s, g i ∈ Set.Icc (0 : ℝ) 1 :=
      fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have ihs := ih hf' hg'
    have hPg : (∏ i ∈ s, g i) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨Finset.prod_nonneg fun i hi => (hg' i hi).1,
        Finset.prod_le_one (fun i hi => (hg' i hi).1) fun i hi => (hg' i hi).2⟩
    have habsPg : |∏ i ∈ s, g i| ≤ 1 := by
      rw [abs_of_nonneg hPg.1]; exact hPg.2
    have habsfa : |f a| ≤ 1 := by
      rw [abs_of_nonneg hfa.1]; exact hfa.2
    calc |f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i|
        = |(f a - g a) * ∏ i ∈ s, g i
            + f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := by ring_nf
      _ ≤ |(f a - g a) * ∏ i ∈ s, g i|
            + |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := abs_add_le _ _
      _ = |f a - g a| * |∏ i ∈ s, g i|
            + |f a| * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| := by
          rw [abs_mul, abs_mul]
      _ ≤ |f a - g a| * 1 + 1 * ∑ i ∈ s, |f i - g i| := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left habsPg (abs_nonneg _)
          · exact mul_le_mul habsfa ihs (abs_nonneg _) zero_le_one
      _ = |f a - g a| + ∑ i ∈ s, |f i - g i| := by ring

/-- The unpaired-jump cost: `|∏ᵢ sᵢ − 1| ≤ Σᵢ (1 − sᵢ)` on `[0,1]`
(Theorem 11, Step 1). -/
theorem abs_prod_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, f i ∈ Set.Icc (0 : ℝ) 1) :
    |(∏ i ∈ s, f i) - 1| ≤ ∑ i ∈ s, (1 - f i) := by
  have h := abs_prod_sub_prod_le s f (fun _ => 1) hf fun i _ => ⟨zero_le_one, le_rfl⟩
  simp only [Finset.prod_const_one] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_))
  rw [abs_sub_comm, abs_of_nonneg (by linarith [(hf i hi).2])]

end Freeburg

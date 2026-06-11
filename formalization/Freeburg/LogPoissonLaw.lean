/-
Freeburg formalization — LogPoissonLaw.lean
Theorem 3(ii) (Uniqueness, at the level of laws) of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632.
-/
import Freeburg.Stretch
import Freeburg.MomentDeterminacy

/-!
# The log-Poisson law and the law-level characterization

This file constructs the **log-Poisson law** — the distribution of
`W = exp(a + bN)` with `N ~ Poisson(λ)` — as a measure on `ℝ`, computes
its moments in closed form, and proves the paper's headline uniqueness
statement at the level of probability laws:

> **Theorem 3(ii).** An i.i.d. cascade multiplier whose moments satisfy
> the A1 closed form `E[W^{km}] = r^{γkm + C(1−β^m)}` *is* log-Poisson:
> no other probability distribution on `W` is compatible with A1.

The proof is the paper's: the A1 moments are geometrically sandwiched,
so the multiplier is essentially bounded with `essSup = r^γ`
(Lemma 2(i), `Freeburg.Stretch`); a law on a compact interval is
determined by its lattice moments (Lemma 2(ii),
`Freeburg.MomentDeterminacy`); and the log-Poisson law realizes exactly
the A1 moments.  Combining the three closes the characterization.

Main results:

* `Freeburg.logPoissonLaw` — the law of `exp(a + bN)`, `N ~ Poisson(λ)`.
* `Freeburg.integral_pow_logPoissonLaw` — the moment formula
  `E[W^m] = exp(am + λ(e^{bm} − 1))`.
* `Freeburg.logPoissonLaw_ae_mem_Icc` — for `b ≤ 0` the law lives on
  `[0, e^a]`.
* `Freeburg.theorem3_law_uniqueness` — **Theorem 3(ii)** for `V = W^k`
  (all lattice moments prescribed by A1 ⟹ the law is log-Poisson).
* `Freeburg.theorem3_law_uniqueness_W` — **Theorem 3(ii)** for the
  multiplier `W` itself, from the `k`-lattice moments alone.

This also contains Proposition 9(a) of the paper: in the log-Poisson
(A1) regime the scaling exponents uniquely determine the multiplier law.
Everything in this file is sorry-free.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal Nat

namespace Freeburg

/-! ## The log-Poisson law -/

/-- The **log-Poisson law**: the distribution of `W = exp(a + b·N)` with
`N ~ Poisson(λ)`, as a Borel measure on `ℝ`. -/
noncomputable def logPoissonLaw (a b : ℝ) (lam : ℝ≥0) : Measure ℝ :=
  (poissonMeasure lam).map fun n : ℕ => Real.exp (a + b * n)

instance isProbabilityMeasure_logPoissonLaw (a b : ℝ) (lam : ℝ≥0) :
    IsProbabilityMeasure (logPoissonLaw a b lam) := by
  unfold logPoissonLaw
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete).aemeasurable

/-- For a nonpositive jump parameter `b ≤ 0` (the paper's `b = ln β/k < 0`),
the log-Poisson law is concentrated on the compact interval `[0, e^a]`:
the multiplier is bounded by its most-singular factor. -/
theorem logPoissonLaw_ae_mem_Icc (a b : ℝ) (lam : ℝ≥0) (hb : b ≤ 0) :
    ∀ᵐ w ∂(logPoissonLaw a b lam), w ∈ Set.Icc (0 : ℝ) (Real.exp a) := by
  unfold logPoissonLaw
  refine (MeasureTheory.ae_map_iff (Measurable.of_discrete).aemeasurable ?_).mpr ?_
  · exact measurableSet_Icc
  · refine Filter.Eventually.of_forall fun n => ⟨(Real.exp_pos _).le, ?_⟩
    refine Real.exp_le_exp.mpr ?_
    have hbn : b * (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hb (Nat.cast_nonneg n)
    linarith

/-- **The log-Poisson moment formula**: `E[W^m] = exp(am + λ(e^{bm} − 1))`
for every `m : ℕ` (the display in the proofs of Theorem 3(ii) and
Proposition 5 — equivalently eq. (∗∗) under `E[W^p] = r^{ζ_p}`; the
computation is the Poisson generating function). -/
theorem integral_pow_logPoissonLaw (a b : ℝ) (lam : ℝ≥0) (m : ℕ) :
    ∫ w, w ^ m ∂(logPoissonLaw a b lam)
      = Real.exp (a * m + (lam : ℝ) * (Real.exp (b * m) - 1)) := by
  rw [logPoissonLaw, integral_map (Measurable.of_discrete).aemeasurable
    (continuous_pow m).aestronglyMeasurable, integral_poissonMeasure]
  have hterm : ∀ n : ℕ,
      (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / n !) • (Real.exp (a + b * n)) ^ m
        = (Real.exp (a * m) * Real.exp (-(lam : ℝ)))
            * (((lam : ℝ) * Real.exp (b * m)) ^ n / n !) := by
    intro n
    have h1 : (Real.exp (a + b * n)) ^ m
        = Real.exp (a * m) * (Real.exp (b * m)) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [smul_eq_mul, h1, mul_pow]
    ring
  rw [tsum_congr hterm, tsum_mul_left,
    (NormedSpace.expSeries_div_hasSum_exp ((lam : ℝ) * Real.exp (b * m))).tsum_eq,
    ← Real.exp_eq_exp_ℝ, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-! ## Theorem 3(ii): the law-level characterization -/

/-- **Theorem 3(ii) of the paper, at the level of laws** (`V`-form).
Let `μ` be the law of `V = W^k` on a probability space: nonnegative,
with all moments integrable and equal to the A1 closed form
`r^{γk·m + C(1−β^m)}` (Lemma 1).  Then `μ` *is* the log-Poisson law
with parameters `a = γk·ln r`, `b = ln β`, `λ = −C·ln r`.

The proof chains the three pillars exactly as the paper does:
boundedness from the geometric moment sandwich (Lemma 2(i)), Hausdorff
moment determinacy on `[0, r^{γk}]` (Lemma 2(ii)), and the log-Poisson
moment formula. -/
theorem theorem3_law_uniqueness
    (r γk C β : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (lam : ℝ≥0) (hlam : (lam : ℝ) = -(C * Real.log r))
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (hint : ∀ m : ℕ, Integrable (fun x => x ^ m) μ)
    (hmom : ∀ m : ℕ, ∫ x, x ^ m ∂μ = r ^ (γk * m + C * (1 - β ^ m))) :
    μ = logPoissonLaw (γk * Real.log r) (Real.log β) lam := by
  have hb : Real.log β < 0 := Real.log_neg hβ.1 hβ.2
  -- Step 1 (Lemma 2(i)): the A1 moments force the support into [0, r^γk]
  have hV0 : (0 : ℝ → ℝ) ≤ᵐ[μ] fun x => x := by
    filter_upwards [hpos] with x hx using hx
  have hbdd : ∀ᵐ x ∂μ, x ≤ r ^ γk := by
    refine ae_le_of_pow_integral_le (fun x => x) measurable_id hV0 (r ^ γk) 1
      (Real.rpow_nonneg hr.1.le γk) hint (fun m => ?_)
    rw [hmom m]
    exact (rpow_A1_moment_sandwich r γk C β hr hC hβ m).2
  have hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) (r ^ γk) := by
    filter_upwards [hpos, hbdd] with x h1 h2 using ⟨h1, h2⟩
  -- Step 2: the log-Poisson law realizes exactly the A1 moments
  have hmomLP : ∀ m : ℕ,
      ∫ x, x ^ m ∂(logPoissonLaw (γk * Real.log r) (Real.log β) lam)
        = r ^ (γk * m + C * (1 - β ^ m)) := by
    intro m
    rw [integral_pow_logPoissonLaw, Real.rpow_def_of_pos hr.1]
    have hexpβ : Real.exp (Real.log β * m) = β ^ m := by
      rw [mul_comm (Real.log β) (m : ℝ), Real.exp_nat_mul, Real.exp_log hβ.1]
    rw [hexpβ, hlam]
    congr 1
    ring
  -- Step 3: the log-Poisson law lives on the same interval
  have hsuppLP : ∀ᵐ x ∂(logPoissonLaw (γk * Real.log r) (Real.log β) lam),
      x ∈ Set.Icc (0 : ℝ) (r ^ γk) := by
    have h := logPoissonLaw_ae_mem_Icc (γk * Real.log r) (Real.log β) lam hb.le
    have hexp : Real.exp (γk * Real.log r) = r ^ γk := by
      rw [Real.rpow_def_of_pos hr.1, mul_comm]
    rwa [hexp] at h
  -- Step 4 (Lemma 2(ii)): Hausdorff determinacy on [0, r^γk]
  exact ext_of_moments_eq hsupp hsuppLP
    (fun m => by rw [hmom m, hmomLP m])

/-- **Theorem 3(ii) of the paper, at the level of laws** (`W`-form).
The multiplier law itself is pinned by the *lattice* moments alone —
the only moments A1 constrains when `k ≥ 2`: if the law of `W` is
nonnegative with `E[W^{km}] = r^{γk·m + C(1−β^m)}`, then
`W` is log-Poisson with `a = γ·ln r`, `b = ln β / k`, `λ = −C·ln r`.
"No other probability distribution on `W` is compatible with A1." -/
theorem theorem3_law_uniqueness_W
    (r γ C β : ℝ) {k : ℕ} (hk : k ≠ 0)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hC : 0 ≤ C) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (lam : ℝ≥0) (hlam : (lam : ℝ) = -(C * Real.log r))
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (hint : ∀ m : ℕ, Integrable (fun x => x ^ (k * m)) μ)
    (hmom : ∀ m : ℕ, ∫ x, x ^ (k * m) ∂μ = r ^ (γ * k * m + C * (1 - β ^ m))) :
    μ = logPoissonLaw (γ * Real.log r) (Real.log β / k) lam := by
  have hb : Real.log β < 0 := Real.log_neg hβ.1 hβ.2
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hpow : (r ^ γ : ℝ) ^ k = r ^ (γ * (k : ℝ)) := by
    rw [← Real.rpow_natCast (r ^ γ) k, ← Real.rpow_mul hr.1.le]
  -- Step 1 (Lemma 2(i) applied to V = W^k): support in [0, r^γ]
  have hVpos : (0 : ℝ → ℝ) ≤ᵐ[μ] fun x => x ^ k := by
    filter_upwards [hpos] with x hx using pow_nonneg hx k
  have hbddV : ∀ᵐ x ∂μ, x ^ k ≤ r ^ (γ * (k : ℝ)) := by
    refine ae_le_of_pow_integral_le (fun x => x ^ k)
      (continuous_pow k).measurable hVpos (r ^ (γ * (k : ℝ))) 1
      (Real.rpow_nonneg hr.1.le _) (fun m => ?_) (fun m => ?_)
    · simpa [← pow_mul] using hint m
    · have : (fun x : ℝ => (x ^ k) ^ m) = fun x : ℝ => x ^ (k * m) := by
        funext x; rw [← pow_mul]
      rw [this, hmom m]
      exact (rpow_A1_moment_sandwich r (γ * k) C β hr hC hβ m).2
  have hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) (r ^ γ) := by
    filter_upwards [hpos, hbddV] with x h0 hxk
    refine ⟨h0, ?_⟩
    have hxk' : x ^ k ≤ (r ^ γ) ^ k := by rw [hpow]; exact hxk
    exact (pow_le_pow_iff_left₀ h0 (Real.rpow_nonneg hr.1.le γ) hk).mp hxk'
  -- Step 2: the log-Poisson lattice moments match the A1 closed form
  have hmomLP : ∀ m : ℕ,
      ∫ x, x ^ (k * m) ∂(logPoissonLaw (γ * Real.log r) (Real.log β / k) lam)
        = r ^ (γ * k * m + C * (1 - β ^ m)) := by
    intro m
    rw [integral_pow_logPoissonLaw, Real.rpow_def_of_pos hr.1]
    have harg : Real.log β / k * ((k * m : ℕ) : ℝ) = Real.log β * m := by
      push_cast
      field_simp
    rw [harg]
    have hexpβ : Real.exp (Real.log β * m) = β ^ m := by
      rw [mul_comm (Real.log β) (m : ℝ), Real.exp_nat_mul, Real.exp_log hβ.1]
    rw [hexpβ, hlam]
    push_cast
    congr 1
    ring
  -- Step 3: the log-Poisson law lives on [0, r^γ] as well
  have hsuppLP : ∀ᵐ x ∂(logPoissonLaw (γ * Real.log r) (Real.log β / k) lam),
      x ∈ Set.Icc (0 : ℝ) (r ^ γ) := by
    have hbk : Real.log β / k ≤ 0 := by
      rw [div_eq_mul_inv]
      exact mul_nonpos_of_nonpos_of_nonneg hb.le
        (inv_nonneg.mpr (Nat.cast_nonneg k))
    have h := logPoissonLaw_ae_mem_Icc (γ * Real.log r) (Real.log β / k) lam hbk
    have hexp : Real.exp (γ * Real.log r) = r ^ γ := by
      rw [Real.rpow_def_of_pos hr.1, mul_comm]
    rwa [hexp] at h
  -- Step 4 (Lemma 2(ii), lattice form): determinacy on [0, r^γ]
  exact ext_of_lattice_moments_eq hk hsupp hsuppLP
    (fun m => by rw [hmom m, hmomLP m])

end Freeburg

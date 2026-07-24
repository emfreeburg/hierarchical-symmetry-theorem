/-
Freeburg formalization — PropagationLower.lean
Theorem 12 (Lower Bound: the Rate √ε Is Exact) of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632.
-/
import Freeburg.CompoundPoisson
import Freeburg.LevyKhintchine
import Freeburg.LogPoissonLaw
import Freeburg.Wasserstein1

/-!
# Theorem 12: the propagation rate `√ε` is exact

The paper's Theorem 11 transfers the A1 stability bound to the
multiplier law at rate `O(√ε)`; **Theorem 12** shows no rate `o(√ε)`
is possible, by exhibiting an explicit family.  For `d ∈ (0, β(1−β)/2]`
the *two-atom perturbation* has tilted measure

  `η_d = (A/2)(δ_{β−d} + δ_{β+d})`

(`A` is the paper's `|A| = (δ_∞ − δ₀)·ln r > 0`, the common η-mass; for
the Theorem-3 cascade `A = C·|ln r|·(1−β)`).  Its multiplier is the
two-atom compound-Poisson law `W_{(d)} = e^A (β−d)^{N₁} (β+d)^{N₂}`
(`Freeburg.CompoundPoisson`), drift-rigid under conservation.  Then:

* **(i)** the A1 residual obeys `A·d²/|ln r| ≤ ε(d) ≤ c₂(β)·A·d²/|ln r|`
  (`theorem12_residual_lower` / `theorem12_residual_upper`, with
  `ε(d) = ⨆ m, (μ_{m+1} − βμ_m)/|ln r|` the genuine residual supremum);
* **(ii)** `W₁(law W_{(d)}, law W₀) ≥ λ_d e^{−λ_d} e^A d`
  (`theorem12_W1_lower`), via the 1-Lipschitz test function
  `f(w) = min(dist(w, G), e^A β(1−β)/2)`, `G = {e^A β^j}` the support
  of the log-Poisson target — the easy direction of duality
  (`Freeburg.Wasserstein1.le_W1`);
* **assembled** (`theorem12_rate_lower`): `W₁ ≥ c₁(β, A, r)·√ε(d)` with
  an explicit positive constant — *no propagation bound of order
  `o(√ε)` is possible*, so combined with Theorem 11 the exact rate is
  `Θ(√ε)`.

The constant `c₂(β)` here is the explicit admissible value
`max((e·β·ln(2/(1+β)))⁻¹, 1)` — a closed-form upper bound for the
paper's `[e·min_{ρ∈[β,(1+β)/2]} ρ|ln ρ|]⁻¹ ∨ 1` (the interval minimum
is bounded below by `β·ln(2/(1+β))`), giving the same `d²` rate.  As in
the paper, `k = 1`; sharpening discovered in formalization: the
Wasserstein lower bound (ii) holds against the log-Poisson target of
*every* rate `λ` (the test function vanishes on the whole geometric
support), not only the matched rate `λ = A/(1−β)`.

Also here: **Theorem 10's Wasserstein display as a genuine `W₁`
statement** (`theorem10_wasserstein_W1`), gluing `Freeburg.W1_dirac`
onto `Freeburg.theorem10_wasserstein_known`.

Everything in this file is sorry-free.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Nat

namespace Freeburg

/-! ## Elementary bounds

The two calculus-free ingredients of part (i): the mean-value bound by
the geometric sum, and `sup_x x·ρ^x ≤ (e|ln ρ|)⁻¹` via `e^y ≥ e·y`. -/

/-- `x^m − y^m ≤ m·x^{m−1}·(x − y)` for `0 ≤ y ≤ x` (the mean-value
bound, by the geometric-sum identity — no calculus needed). -/
theorem pow_sub_pow_le {x y : ℝ} (m : ℕ) (hy : 0 ≤ y) (hxy : y ≤ x) :
    x ^ m - y ^ m ≤ m * x ^ (m - 1) * (x - y) := by
  rw [← geom_sum₂_mul]
  refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr hxy)
  calc ∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)
      ≤ ∑ _i ∈ Finset.range m, x ^ (m - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have him : i < m := Finset.mem_range.mp hi
        calc x ^ i * y ^ (m - 1 - i) ≤ x ^ i * x ^ (m - 1 - i) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hxy _)
                (pow_nonneg (hy.trans hxy) i)
          _ = x ^ (m - 1) := by
              rw [← pow_add]
              congr 1
              omega
    _ = m * x ^ (m - 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `m·ρ^m ≤ (e·|ln ρ|)⁻¹` for `ρ ∈ (0,1)`: the elementary form of
`sup_{x≥0} x·ρ^x = (e|ln ρ|)⁻¹`, from `e^{y−1} ≥ y`. -/
theorem nat_mul_pow_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (m : ℕ) :
    (m : ℝ) * ρ ^ m ≤ (Real.exp 1 * (-Real.log ρ))⁻¹ := by
  have hlog : 0 < -Real.log ρ := by
    have := Real.log_neg hρ0 hρ1
    linarith
  set y : ℝ := (m : ℝ) * (-Real.log ρ) with hy
  have hy0 : 0 ≤ y := by positivity
  -- `e·y ≤ e^y`
  have hkey : y * Real.exp 1 ≤ Real.exp y := by
    have h := Real.add_one_le_exp (y - 1)
    have h2 : Real.exp (y - 1) * Real.exp 1 = Real.exp y := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith [mul_le_mul_of_nonneg_right h (Real.exp_pos 1).le, Real.exp_pos (1 : ℝ)]
  -- `ρ^m = e^{−y}`, so `e^y · ρ^m = 1`
  have hpow : ρ ^ m = Real.exp (-y) := by
    rw [hy, show -((m : ℝ) * (-Real.log ρ)) = (m : ℝ) * Real.log ρ by ring,
      Real.exp_nat_mul, Real.exp_log hρ0]
  have hexp1 : Real.exp y * ρ ^ m = 1 := by
    rw [hpow, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h3 : y * Real.exp 1 * ρ ^ m ≤ 1 := by
    calc y * Real.exp 1 * ρ ^ m
        ≤ Real.exp y * ρ ^ m :=
          mul_le_mul_of_nonneg_right hkey (pow_pos hρ0 m).le
      _ = 1 := hexp1
  rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
  nlinarith [h3]

/-! ## The two-atom perturbed family: tilted measure and residuals -/

/-- The tilted measure of the perturbed family:
`η_d = (A/2)(δ_{β−d} + δ_{β+d})` (Theorem 12's display). -/
noncomputable def etaD (A β d : ℝ) : Measure ℝ :=
  ENNReal.ofReal (A / 2) • (Measure.dirac (β - d) + Measure.dirac (β + d))

/-- Moments of the two-atom tilted measure:
`μ_m = (A/2)[(β−d)^m + (β+d)^m]`. -/
theorem integral_pow_etaD (A β d : ℝ) (hA : 0 ≤ A) (m : ℕ) :
    ∫ u, u ^ m ∂(etaD A β d) = A / 2 * ((β - d) ^ m + (β + d) ^ m) := by
  unfold etaD
  rw [integral_smul_measure,
    integral_add_measure (integrable_dirac enorm_lt_top)
      (integrable_dirac enorm_lt_top),
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul]

/-- **De-tilting faithfulness**: the two-atom Lévy measure `ν̃_d` with
the paper's masses `(A/2)/(1−(β∓d))` tilts to exactly `η_d`:
`η_d = (1−u) dν̃_d`. -/
theorem twoAtomLevy_tilt_eq_etaD {β A d : ℝ}
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hA : 0 ≤ A)
    (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2))
    (lam1 lam2 : ℝ≥0)
    (hl1 : (lam1 : ℝ) = A / 2 / (1 - (β - d)))
    (hl2 : (lam2 : ℝ) = A / 2 / (1 - (β + d))) :
    (twoAtomLevy (β - d) (β + d) lam1 lam2).withDensity
        (fun u => ENNReal.ofReal (1 - u)) = etaD A β d := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  obtain ⟨hd0, hdle⟩ := hd
  have hd2 : d ≤ (1 - β) / 2 := by nlinarith
  have h1pos : (0 : ℝ) < 1 - (β - d) := by linarith
  have h2pos : (0 : ℝ) < 1 - (β + d) := by linarith
  rw [twoAtomLevy_withDensity_tilt]
  have e1 : ((lam1 : ℝ≥0∞)) * ENNReal.ofReal (1 - (β - d))
      = ENNReal.ofReal (A / 2) := by
    rw [← ENNReal.ofReal_coe_nnreal, hl1,
      ← ENNReal.ofReal_mul (div_nonneg (by linarith) h1pos.le)]
    congr 1
    exact div_mul_cancel₀ _ h1pos.ne'
  have e2 : ((lam2 : ℝ≥0∞)) * ENNReal.ofReal (1 - (β + d))
      = ENNReal.ofReal (A / 2) := by
    rw [← ENNReal.ofReal_coe_nnreal, hl2,
      ← ENNReal.ofReal_mul (div_nonneg (by linarith) h2pos.le)]
    congr 1
    exact div_mul_cancel₀ _ h2pos.ne'
  rw [e1, e2]
  unfold etaD
  rw [smul_add]

/-- The signed A1 residual of the family at level `m`:
`μ_{m+1} − β·μ_m = (Ad/2)[(β+d)^m − (β−d)^m]` — the paper's
`ε_m·|ln r|`. -/
theorem etaD_residual_formula {A β d : ℝ} (hA : 0 ≤ A) (m : ℕ) :
    (∫ u, u ^ (m + 1) ∂(etaD A β d)) - β * ∫ u, u ^ m ∂(etaD A β d)
      = A * d / 2 * ((β + d) ^ m - (β - d) ^ m) := by
  rw [integral_pow_etaD A β d hA, integral_pow_etaD A β d hA, pow_succ, pow_succ]
  ring

/-- The residuals are signed: `ε_m ≥ 0` (the family overshoots A1 from
above at every level). -/
theorem etaD_residual_nonneg {A β d : ℝ} (hA : 0 ≤ A) (hd0 : 0 ≤ d)
    (hdβ : d ≤ β) (m : ℕ) :
    0 ≤ (∫ u, u ^ (m + 1) ∂(etaD A β d)) - β * ∫ u, u ^ m ∂(etaD A β d) := by
  rw [etaD_residual_formula hA]
  have h : (β - d) ^ m ≤ (β + d) ^ m :=
    pow_le_pow_left₀ (by linarith) (by linarith) m
  have h2 : 0 ≤ A * d / 2 := by positivity
  nlinarith

/-- `ε₁·|ln r| = A·d²` **exactly** (`ε₀ = 0` is the `m = 0` case of
`etaD_residual_formula`) — the level pinning the lower bound of
part (i). -/
theorem etaD_residual_one {A β d : ℝ} (hA : 0 ≤ A) :
    (∫ u, u ^ 2 ∂(etaD A β d)) - β * ∫ u, u ^ 1 ∂(etaD A β d) = A * d ^ 2 := by
  rw [integral_pow_etaD A β d hA, integral_pow_etaD A β d hA]
  ring

/-- The `c₂` constant of Theorem 12(i): the explicit admissible value
`max((e·β·ln(2/(1+β)))⁻¹, 1)` of the paper's
`[e·min_{ρ∈[β,(1+β)/2]} ρ|ln ρ|]⁻¹ ∨ 1`. -/
noncomputable def c2 (β : ℝ) : ℝ :=
  max ((Real.exp 1 * β * Real.log (2 / (1 + β)))⁻¹) 1

theorem one_le_c2 (β : ℝ) : 1 ≤ c2 β := le_max_right _ _

theorem c2_pos (β : ℝ) : 0 < c2 β := lt_of_lt_of_le one_pos (one_le_c2 β)

/-- The supremum step of part (i): `m·ρ^{m−1} ≤ c₂(β)` for every
`ρ ∈ [β, (1+β)/2]`. -/
theorem nat_mul_pow_pred_le_c2 {β ρ : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hρl : β ≤ ρ) (hρu : ρ ≤ (1 + β) / 2) (m : ℕ) :
    (m : ℝ) * ρ ^ (m - 1) ≤ c2 β := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  have hρ0 : 0 < ρ := lt_of_lt_of_le hβ0 hρl
  have hρ1 : ρ < 1 := by linarith
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simpa using (c2_pos β).le
  -- the log of the midpoint bound
  have hmid : (0 : ℝ) < Real.log (2 / (1 + β)) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hloglb : Real.log (2 / (1 + β)) ≤ -Real.log ρ := by
    have h1 : Real.log ρ ≤ Real.log ((1 + β) / 2) :=
      Real.log_le_log hρ0 hρu
    have h2 : Real.log ((1 + β) / 2) = -Real.log (2 / (1 + β)) := by
      rw [show (1 + β) / 2 = (2 / (1 + β))⁻¹ by
            rw [inv_div], Real.log_inv]
    linarith [h1, h2 ▸ h1]
  have hlog : 0 < -Real.log ρ := lt_of_lt_of_le hmid hloglb
  -- `m·ρ^{m−1} = (m·ρ^m)/ρ ≤ (e·ρ·(−ln ρ))⁻¹ ≤ (e·β·ln(2/(1+β)))⁻¹`
  have h1 := nat_mul_pow_le hρ0 hρ1 m
  have hpow : ρ ^ m = ρ ^ (m - 1) * ρ := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  rw [hpow] at h1
  have h2 : (m : ℝ) * ρ ^ (m - 1) ≤ (Real.exp 1 * (-Real.log ρ))⁻¹ / ρ := by
    rw [le_div_iff₀ hρ0]
    nlinarith [h1]
  have h3 : (Real.exp 1 * (-Real.log ρ))⁻¹ / ρ
      = (Real.exp 1 * ρ * (-Real.log ρ))⁻¹ := by
    rw [div_eq_mul_inv, ← mul_inv]
    congr 1
    ring
  have h4 : (Real.exp 1 * ρ * (-Real.log ρ))⁻¹
      ≤ (Real.exp 1 * β * Real.log (2 / (1 + β)))⁻¹ := by
    have hposβ : 0 < Real.exp 1 * β * Real.log (2 / (1 + β)) := by
      have := Real.exp_pos (1 : ℝ)
      positivity
    refine inv_anti₀ hposβ ?_
    have h5 : β * Real.log (2 / (1 + β)) ≤ ρ * (-Real.log ρ) :=
      mul_le_mul hρl hloglb hmid.le hρ0.le
    nlinarith [Real.exp_pos (1 : ℝ)]
  calc (m : ℝ) * ρ ^ (m - 1)
      ≤ (Real.exp 1 * (-Real.log ρ))⁻¹ / ρ := h2
    _ = (Real.exp 1 * ρ * (-Real.log ρ))⁻¹ := h3
    _ ≤ (Real.exp 1 * β * Real.log (2 / (1 + β)))⁻¹ := h4
    _ ≤ c2 β := le_max_left _ _

/-- **Theorem 12(i), upper bound at every level**:
`ε_m·|ln r| ≤ c₂(β)·A·d²`. -/
theorem etaD_residual_le {A β d : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hA : 0 ≤ A) (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2)) (m : ℕ) :
    (∫ u, u ^ (m + 1) ∂(etaD A β d)) - β * ∫ u, u ^ m ∂(etaD A β d)
      ≤ c2 β * (A * d ^ 2) := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  obtain ⟨hd0, hdle⟩ := hd
  have hdβ : d < β := by nlinarith
  have hd2 : d ≤ (1 - β) / 2 := by nlinarith
  rw [etaD_residual_formula hA]
  have hmvt := pow_sub_pow_le (x := β + d) (y := β - d) m
    (by linarith) (by linarith)
  have hc2m := nat_mul_pow_pred_le_c2 ⟨hβ0, hβ1⟩
    (by linarith : β ≤ β + d) (by linarith : β + d ≤ (1 + β) / 2) m
  have h0 : 0 ≤ A * d / 2 := by positivity
  calc A * d / 2 * ((β + d) ^ m - (β - d) ^ m)
      ≤ A * d / 2 * ((m : ℝ) * (β + d) ^ (m - 1) * (β + d - (β - d))) :=
        mul_le_mul_of_nonneg_left hmvt h0
    _ = A * d ^ 2 * ((m : ℝ) * (β + d) ^ (m - 1)) := by ring
    _ ≤ A * d ^ 2 * c2 β := by
        refine mul_le_mul_of_nonneg_left hc2m (by positivity)
    _ = c2 β * (A * d ^ 2) := by ring

/-! ## Theorem 12(i): the residual supremum -/

/-- The family's **A1 residual** `ε(d) = sup_m ε_m`, with
`ε_m = (μ_{m+1} − β·μ_m)/|ln r|` the paper's normalized residuals. -/
noncomputable def epsResidual (A β d r : ℝ) : ℝ :=
  ⨆ m : ℕ, ((∫ u, u ^ (m + 1) ∂(etaD A β d)) - β * ∫ u, u ^ m ∂(etaD A β d))
    / |Real.log r|

/-- **Theorem 12(i), upper half**: `ε(d) ≤ c₂(β)·A·d²/|ln r|`. -/
theorem theorem12_residual_upper {A β d r : ℝ}
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hA : 0 ≤ A)
    (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2)) :
    epsResidual A β d r ≤ c2 β * (A * d ^ 2) / |Real.log r| := by
  refine ciSup_le fun m => ?_
  exact div_le_div_of_nonneg_right (etaD_residual_le hβ hA hd m) (abs_nonneg _)

/-- **Theorem 12(i), lower half**: `A·d²/|ln r| ≤ ε(d)` — pinned
exactly by the level-1 residual. -/
theorem theorem12_residual_lower {A β d r : ℝ}
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hA : 0 ≤ A)
    (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2)) :
    A * d ^ 2 / |Real.log r| ≤ epsResidual A β d r := by
  have hbdd : BddAbove (Set.range fun m : ℕ =>
      ((∫ u, u ^ (m + 1) ∂(etaD A β d)) - β * ∫ u, u ^ m ∂(etaD A β d))
        / |Real.log r|) := by
    refine ⟨c2 β * (A * d ^ 2) / |Real.log r|, ?_⟩
    rintro x ⟨m, rfl⟩
    exact div_le_div_of_nonneg_right (etaD_residual_le hβ hA hd m) (abs_nonneg _)
  have h1 := le_ciSup hbdd 1
  refine le_trans (le_of_eq ?_) h1
  have e2 : ((1 : ℕ) + 1) = 2 := rfl
  rw [e2, etaD_residual_one hA]

/-! ## Theorem 12(ii): the Wasserstein lower bound -/

/-- The one-jump point `e^A(β−d)` sits at distance exactly `e^A·d`
from the log-Poisson support `G = {e^A β^j : j ∈ ℕ}` when
`0 < d ≤ β(1−β)/2` (nearest point: `e^A β`, the one-jump atom). -/
theorem infDist_geom_minus {β d : ℝ} (A : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2)) :
    Metric.infDist (Real.exp A * (β - d))
        (Set.range fun j : ℕ => Real.exp A * β ^ j)
      = Real.exp A * d := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  obtain ⟨hd0, hdle⟩ := hd
  have hdβ : d < β := by nlinarith
  have hd2 : d ≤ (1 - β) / 2 := by nlinarith
  have hE := Real.exp_pos A
  refine le_antisymm ?_ ?_
  · have hmem : Real.exp A * β ^ 1
        ∈ Set.range fun j : ℕ => Real.exp A * β ^ j := ⟨1, rfl⟩
    refine le_trans (Metric.infDist_le_dist_of_mem hmem) (le_of_eq ?_)
    rw [Real.dist_eq, pow_one,
      show Real.exp A * (β - d) - Real.exp A * β = -(Real.exp A * d) by ring,
      abs_neg, abs_of_pos (by positivity)]
  · have hGne : (Set.range fun j : ℕ => Real.exp A * β ^ j).Nonempty :=
      ⟨Real.exp A * β ^ 0, ⟨0, rfl⟩⟩
    rw [Metric.le_infDist hGne]
    rintro y ⟨j, rfl⟩
    rw [Real.dist_eq,
      show Real.exp A * (β - d) - Real.exp A * β ^ j
        = Real.exp A * ((β - d) - β ^ j) by ring,
      abs_mul, abs_of_pos hE]
    refine mul_le_mul_of_nonneg_left ?_ hE.le
    rcases j with _ | _ | j
    · -- `j = 0`: distance `1 − β + d ≥ d`
      rw [pow_zero, abs_of_neg (by linarith : β - d - 1 < 0)]
      linarith
    · -- `j = 1`: distance exactly `d`
      rw [pow_one, show β - d - β = -d by ring, abs_neg, abs_of_pos hd0]
    · -- `j ≥ 2`: distance `≥ β − d − β² ≥ d` since `2d ≤ β(1−β)`
      have hpj : β ^ (j + 1 + 1) ≤ β ^ 2 :=
        pow_le_pow_of_le_one hβ0.le hβ1.le (by omega)
      have hgap : d ≤ β - d - β ^ (j + 1 + 1) := by nlinarith
      exact hgap.trans (le_abs_self _)

/-- The one-jump point `e^A(β+d)`: also at distance exactly `e^A·d`
from `G` (here `d ≤ (1−β)/2` keeps `e^A` no closer than `e^A β`). -/
theorem infDist_geom_plus {β d : ℝ} (A : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2)) :
    Metric.infDist (Real.exp A * (β + d))
        (Set.range fun j : ℕ => Real.exp A * β ^ j)
      = Real.exp A * d := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  obtain ⟨hd0, hdle⟩ := hd
  have hd2 : d ≤ (1 - β) / 2 := by nlinarith
  have hE := Real.exp_pos A
  refine le_antisymm ?_ ?_
  · have hmem : Real.exp A * β ^ 1
        ∈ Set.range fun j : ℕ => Real.exp A * β ^ j := ⟨1, rfl⟩
    refine le_trans (Metric.infDist_le_dist_of_mem hmem) (le_of_eq ?_)
    rw [Real.dist_eq, pow_one,
      show Real.exp A * (β + d) - Real.exp A * β = Real.exp A * d by ring,
      abs_of_pos (by positivity)]
  · have hGne : (Set.range fun j : ℕ => Real.exp A * β ^ j).Nonempty :=
      ⟨Real.exp A * β ^ 0, ⟨0, rfl⟩⟩
    rw [Metric.le_infDist hGne]
    rintro y ⟨j, rfl⟩
    rw [Real.dist_eq,
      show Real.exp A * (β + d) - Real.exp A * β ^ j
        = Real.exp A * ((β + d) - β ^ j) by ring,
      abs_mul, abs_of_pos hE]
    refine mul_le_mul_of_nonneg_left ?_ hE.le
    rcases j with _ | _ | j
    · -- `j = 0`: distance `1 − β − d ≥ d` (uses `d ≤ (1−β)/2`)
      rw [pow_zero, abs_of_neg (by linarith : β + d - 1 < 0)]
      linarith
    · -- `j = 1`: distance exactly `d`
      rw [pow_one, show β + d - β = d by ring, abs_of_pos hd0]
    · -- `j ≥ 2`: distance `≥ β + d − β² ≥ d`
      have hpj : β ^ (j + 1 + 1) ≤ β ^ 2 :=
        pow_le_pow_of_le_one hβ0.le hβ1.le (by omega)
      have hgap : d ≤ β + d - β ^ (j + 1 + 1) := by nlinarith
      exact hgap.trans (le_abs_self _)

/-- **Theorem 12(ii), first display**: the Wasserstein lower bound
`W₁(law W_{(d)}, law W₀) ≥ λ_d e^{−λ_d} e^A d`, by the test function
`f(w) = min(dist(w, G), e^A β(1−β)/2)`.  (Sharpening: the bound holds
for the log-Poisson target of *every* rate `lam`, not only the paper's
matched `lam = A/(1−β)` — and for every drift `A`: the drift-positivity
hypothesis of the printed statement is not needed, so it is no longer
carried here.) -/
theorem theorem12_W1_lower {β A d : ℝ}
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2))
    (lam1 lam2 lam : ℝ≥0) :
    ((lam1 : ℝ) + lam2) * Real.exp (-((lam1 : ℝ) + lam2)) * Real.exp A * d
      ≤ W1 (twoAtomCPLaw A (β - d) (β + d) lam1 lam2)
          (logPoissonLaw A (Real.log β) lam) := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  obtain ⟨hd0, hdle⟩ := hd
  have hdβ : d < β := by nlinarith
  have hd2 : d ≤ (1 - β) / 2 := by nlinarith
  have hE := Real.exp_pos A
  set G : Set ℝ := Set.range fun j : ℕ => Real.exp A * β ^ j with hG
  set cap : ℝ := Real.exp A * (β * (1 - β) / 2) with hcap
  have hcap0 : 0 < cap := by
    rw [hcap]
    exact mul_pos (Real.exp_pos A) (by nlinarith)
  set f : ℝ → ℝ := fun w => min (Metric.infDist w G) cap with hf
  -- `f` is an anchored 1-Lipschitz test function
  have hflip : LipschitzWith 1 f := (Metric.lipschitz_infDist_pt G).min_const cap
  have hf0 : f 0 = 0 := by
    have h0cl : (0 : ℝ) ∈ closure G := by
      have htend : Filter.Tendsto (fun j : ℕ => Real.exp A * β ^ j)
          Filter.atTop (nhds 0) := by
        have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul
          (Real.exp A)
        simpa using h
      exact mem_closure_of_tendsto htend
        (Filter.Eventually.of_forall fun j => ⟨j, rfl⟩)
    rw [hf]
    simp only []
    rw [Metric.infDist_zero_of_mem_closure h0cl]
    exact min_eq_left hcap0.le
  -- `f` vanishes on the target support
  have hfG : ∀ w ∈ G, f w = 0 := by
    intro w hw
    rw [hf]
    simp only []
    rw [Metric.infDist_zero_of_mem hw]
    exact min_eq_left hcap0.le
  -- `f` is `[0, cap]`-valued
  have hfnonneg : ∀ w, 0 ≤ f w := fun w =>
    le_min Metric.infDist_nonneg hcap0.le
  have hfle : ∀ w, f w ≤ cap := fun w => min_le_right _ _
  -- both laws live on `[0, e^A]`
  have hμbd : ∀ᵐ w ∂(twoAtomCPLaw A (β - d) (β + d) lam1 lam2),
      |w| ≤ Real.exp A := by
    filter_upwards [twoAtomCPLaw_ae_mem_Icc A lam1 lam2
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩] with w hw
    rw [abs_le]
    exact ⟨by linarith [hw.1], hw.2⟩
  have hνbd : ∀ᵐ w ∂(logPoissonLaw A (Real.log β) lam), |w| ≤ Real.exp A := by
    filter_upwards [logPoissonLaw_ae_mem_Icc A (Real.log β) lam
      (Real.log_neg hβ0 hβ1).le] with w hw
    rw [abs_le]
    exact ⟨by linarith [hw.1], hw.2⟩
  -- `E f(W₀) = 0`: the target is supported on `G`
  have hEν : ∫ w, f w ∂(logPoissonLaw A (Real.log β) lam) = 0 := by
    rw [logPoissonLaw, integral_map Measurable.of_discrete.aemeasurable
      hflip.continuous.aestronglyMeasurable]
    have hzero : ∀ n : ℕ, f (Real.exp (A + Real.log β * n)) = 0 := by
      intro n
      refine hfG _ ⟨n, ?_⟩
      rw [Real.exp_add, mul_comm (Real.log β) (n : ℝ), Real.exp_nat_mul,
        Real.exp_log hβ0]
    rw [integral_congr_ae (Filter.Eventually.of_forall hzero), integral_zero]
  -- `E f(W_{(d)}) ≥ λ_d e^{−λ_d} e^A d`: the one-jump events
  have hEμ : ((lam1 : ℝ) + lam2) * Real.exp (-((lam1 : ℝ) + lam2))
        * Real.exp A * d
      ≤ ∫ w, f w ∂(twoAtomCPLaw A (β - d) (β + d) lam1 lam2) := by
    rw [twoAtomCPLaw, integral_map Measurable.of_discrete.aemeasurable
      hflip.continuous.aestronglyMeasurable]
    set P : Measure (ℕ × ℕ) := (poissonMeasure lam1).prod (poissonMeasure lam2)
      with hP
    set F : ℕ × ℕ → ℝ :=
      fun p => f (Real.exp A * (β - d) ^ p.1 * (β + d) ^ p.2) with hF
    have hFnonneg : ∀ p, 0 ≤ F p := fun p => hfnonneg _
    have hFint : Integrable F P := by
      refine Integrable.mono' (integrable_const cap)
        (Measurable.of_discrete (f := F)).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun p => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg p)]
      exact hfle _
    have hsingle : ∀ q : ℕ × ℕ,
        ∫ p in ({q} : Set (ℕ × ℕ)), F p ∂P = P.real {q} * F q := by
      intro q
      rw [Measure.restrict_singleton, integral_smul_measure, integral_dirac,
        measureReal_def, smul_eq_mul]
    -- the two one-jump singletons
    have hdisj : Disjoint ({((1, 0) : ℕ × ℕ)} : Set (ℕ × ℕ))
        {((0, 1) : ℕ × ℕ)} := by
      rw [Set.disjoint_singleton]
      decide
    have hsub : ∫ p in ({((1, 0) : ℕ × ℕ)} ∪ {((0, 1) : ℕ × ℕ)}), F p ∂P
        ≤ ∫ p, F p ∂P :=
      setIntegral_le_integral hFint (Filter.Eventually.of_forall hFnonneg)
    have hunion : ∫ p in ({((1, 0) : ℕ × ℕ)} ∪ {((0, 1) : ℕ × ℕ)}), F p ∂P
        = P.real {((1, 0) : ℕ × ℕ)} * F (1, 0)
          + P.real {((0, 1) : ℕ × ℕ)} * F (0, 1) := by
      rw [setIntegral_union hdisj (measurableSet_singleton _)
        hFint.integrableOn hFint.integrableOn, hsingle, hsingle]
    -- the Poisson masses of the one-jump events
    have hmass10 : P.real {((1, 0) : ℕ × ℕ)}
        = (lam1 : ℝ) * Real.exp (-((lam1 : ℝ) + lam2)) := by
      rw [hP, measureReal_def, ← Set.singleton_prod_singleton,
        Measure.prod_prod, poissonMeasure_singleton, poissonMeasure_singleton,
        ← ENNReal.ofReal_mul (by positivity),
        ENNReal.toReal_ofReal (by positivity),
        show -((lam1 : ℝ) + lam2) = -(lam1 : ℝ) + -(lam2 : ℝ) by ring,
        Real.exp_add]
      simp only [pow_one, pow_zero, Nat.factorial_one, Nat.factorial_zero,
        Nat.cast_one, mul_one, div_one]
      ring
    have hmass01 : P.real {((0, 1) : ℕ × ℕ)}
        = (lam2 : ℝ) * Real.exp (-((lam1 : ℝ) + lam2)) := by
      rw [hP, measureReal_def, ← Set.singleton_prod_singleton,
        Measure.prod_prod, poissonMeasure_singleton, poissonMeasure_singleton,
        ← ENNReal.ofReal_mul (by positivity),
        ENNReal.toReal_ofReal (by positivity),
        show -((lam1 : ℝ) + lam2) = -(lam1 : ℝ) + -(lam2 : ℝ) by ring,
        Real.exp_add]
      simp only [pow_one, pow_zero, Nat.factorial_one, Nat.factorial_zero,
        Nat.cast_one, mul_one, div_one]
      ring
    -- the one-jump values of `f`
    have hFval10 : F (1, 0) = Real.exp A * d := by
      rw [hF]
      simp only [pow_one, pow_zero, mul_one]
      rw [hf]
      simp only []
      rw [hG, infDist_geom_minus A ⟨hβ0, hβ1⟩ ⟨hd0, hdle⟩]
      refine min_eq_left ?_
      rw [hcap]
      nlinarith
    have hFval01 : F (0, 1) = Real.exp A * d := by
      rw [hF]
      simp only [pow_one, pow_zero, mul_one]
      rw [hf]
      simp only []
      rw [hG, infDist_geom_plus A ⟨hβ0, hβ1⟩ ⟨hd0, hdle⟩]
      refine min_eq_left ?_
      rw [hcap]
      nlinarith
    calc ((lam1 : ℝ) + lam2) * Real.exp (-((lam1 : ℝ) + lam2))
          * Real.exp A * d
        = P.real {((1, 0) : ℕ × ℕ)} * F (1, 0)
            + P.real {((0, 1) : ℕ × ℕ)} * F (0, 1) := by
          rw [hmass10, hmass01, hFval10, hFval01]
          ring
      _ = ∫ p in ({((1, 0) : ℕ × ℕ)} ∪ {((0, 1) : ℕ × ℕ)}), F p ∂P :=
          hunion.symm
      _ ≤ ∫ p, F p ∂P := hsub
  -- assemble through the duality lower bound
  have hle := le_W1 hμbd hνbd hflip hf0
  rw [hEν, sub_zero] at hle
  exact hEμ.trans hle

/-! ## Theorem 12 assembled: the `c₁·√ε` lower bound -/

/-- The total jump rate of the family:
`λ_d = λ₁ + λ₂ = [A/(1−β)]/(1 − d²/(1−β)²)`. -/
theorem lamD_eq {β A d : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2))
    (lam1 lam2 : ℝ≥0)
    (hl1 : (lam1 : ℝ) = A / 2 / (1 - (β - d)))
    (hl2 : (lam2 : ℝ) = A / 2 / (1 - (β + d))) :
    (lam1 : ℝ) + lam2 = A * (1 - β) / ((1 - β) ^ 2 - d ^ 2) := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  obtain ⟨hd0, hdle⟩ := hd
  have hd2 : d ≤ (1 - β) / 2 := by nlinarith
  have h1pos : (0 : ℝ) < 1 - (β - d) := by linarith
  have h2pos : (0 : ℝ) < 1 - (β + d) := by linarith
  have hDpos : (0 : ℝ) < (1 - β) ^ 2 - d ^ 2 := by nlinarith
  rw [hl1, hl2]
  field_simp
  ring

/-- The rate window: `λ ≤ λ_d ≤ (4/3)·λ` for `d ≤ β(1−β)/2`,
`λ = A/(1−β)`. -/
theorem lamD_bounds {β A d : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hA : 0 < A)
    (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2))
    (lam1 lam2 : ℝ≥0)
    (hl1 : (lam1 : ℝ) = A / 2 / (1 - (β - d)))
    (hl2 : (lam2 : ℝ) = A / 2 / (1 - (β + d))) :
    A / (1 - β) ≤ (lam1 : ℝ) + lam2
      ∧ (lam1 : ℝ) + lam2 ≤ 4 / 3 * (A / (1 - β)) := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  obtain ⟨hd0, hdle⟩ := hd
  have hd2 : d ≤ (1 - β) / 2 := by nlinarith
  have hβ' : (0 : ℝ) < 1 - β := by linarith
  have hDpos : (0 : ℝ) < (1 - β) ^ 2 - d ^ 2 := by nlinarith
  rw [lamD_eq ⟨hβ0, hβ1⟩ ⟨hd0, hdle⟩ lam1 lam2 hl1 hl2]
  constructor
  · rw [div_le_div_iff₀ hβ' hDpos]
    nlinarith
  · rw [show (4 : ℝ) / 3 * (A / (1 - β)) = 4 * A / (3 * (1 - β)) from
        div_mul_div_comm 4 3 A (1 - β),
      div_le_div_iff₀ hDpos (by linarith)]
    nlinarith [mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ 2 * d)
      (by linarith : 2 * d ≤ 1 - β)]

/-- The explicit constant `c₁(β, A, r)` of Theorem 12(ii). -/
noncomputable def c1 (A β r : ℝ) : ℝ :=
  A / (1 - β) * Real.exp (-(4 / 3 * (A / (1 - β)))) * Real.exp A
    * Real.sqrt (|Real.log r| / (c2 β * A))

theorem c1_pos {A β r : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hA : 0 < A)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) : 0 < c1 A β r := by
  have hβ' : (0 : ℝ) < 1 - β := by linarith [hβ.2]
  have hlnr : 0 < |Real.log r| :=
    abs_pos.mpr (Real.log_neg hr.1 hr.2).ne
  unfold c1
  have hsq : 0 < Real.sqrt (|Real.log r| / (c2 β * A)) :=
    Real.sqrt_pos.mpr (div_pos hlnr (mul_pos (c2_pos β) hA))
  positivity

/-- **Theorem 12 (assembled)**: the family certifies the rate.  Its A1
residual is `ε(d) ≍ d²` (part (i)) while its Wasserstein distance to
the log-Poisson target is at least `c₁·√ε(d)` with `c₁ > 0` explicit:
**no propagation bound of order `o(√ε)` is possible**.  Combined with
Theorem 11, the exact propagation rate is `Θ(√ε)`. -/
theorem theorem12_rate_lower {β A r d : ℝ}
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hA : 0 < A) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2))
    (lam1 lam2 lam : ℝ≥0)
    (hl1 : (lam1 : ℝ) = A / 2 / (1 - (β - d)))
    (hl2 : (lam2 : ℝ) = A / 2 / (1 - (β + d)))
    (_hlam : (lam : ℝ) = A / (1 - β)) :
    c1 A β r * Real.sqrt (epsResidual A β d r)
      ≤ W1 (twoAtomCPLaw A (β - d) (β + d) lam1 lam2)
          (logPoissonLaw A (Real.log β) lam) := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  obtain ⟨hd0, hdle⟩ := hd
  have hβ' : (0 : ℝ) < 1 - β := by linarith
  have hlnr : 0 < |Real.log r| := abs_pos.mpr (Real.log_neg hr.1 hr.2).ne
  -- √ε(d) ≤ d·√(c₂A/|ln r|)
  have hsqrt : Real.sqrt (epsResidual A β d r)
      ≤ d * Real.sqrt (c2 β * A / |Real.log r|) := by
    have h1 : epsResidual A β d r ≤ d ^ 2 * (c2 β * A / |Real.log r|) := by
      refine (theorem12_residual_upper ⟨hβ0, hβ1⟩ hA.le ⟨hd0, hdle⟩).trans
        (le_of_eq ?_)
      ring
    calc Real.sqrt (epsResidual A β d r)
        ≤ Real.sqrt (d ^ 2 * (c2 β * A / |Real.log r|)) := Real.sqrt_le_sqrt h1
      _ = d * Real.sqrt (c2 β * A / |Real.log r|) := by
          rw [Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd0.le]
  -- the constant collapses: c₁·d·√(c₂A/|ln r|) = λ e^{−4λ/3} e^A d
  have hcollapse : c1 A β r * (d * Real.sqrt (c2 β * A / |Real.log r|))
      = A / (1 - β) * Real.exp (-(4 / 3 * (A / (1 - β)))) * Real.exp A * d := by
    unfold c1
    have hprod : Real.sqrt (|Real.log r| / (c2 β * A))
        * Real.sqrt (c2 β * A / |Real.log r|) = 1 := by
      have hne : c2 β * A * |Real.log r| ≠ 0 :=
        (mul_pos (mul_pos (c2_pos β) hA) hlnr).ne'
      rw [← Real.sqrt_mul (div_nonneg (abs_nonneg _)
            (mul_pos (c2_pos β) hA).le),
        show |Real.log r| / (c2 β * A) * (c2 β * A / |Real.log r|) = 1 by
          rw [div_mul_div_comm, mul_comm]
          exact div_self hne,
        Real.sqrt_one]
    calc A / (1 - β) * Real.exp (-(4 / 3 * (A / (1 - β)))) * Real.exp A
          * Real.sqrt (|Real.log r| / (c2 β * A))
          * (d * Real.sqrt (c2 β * A / |Real.log r|))
        = A / (1 - β) * Real.exp (-(4 / 3 * (A / (1 - β)))) * Real.exp A * d
            * (Real.sqrt (|Real.log r| / (c2 β * A))
              * Real.sqrt (c2 β * A / |Real.log r|)) := by ring
      _ = A / (1 - β) * Real.exp (-(4 / 3 * (A / (1 - β)))) * Real.exp A * d := by
          rw [hprod, mul_one]
  -- λ e^{−4λ/3} ≤ λ_d e^{−λ_d} on the rate window
  obtain ⟨hlo, hhi⟩ := lamD_bounds ⟨hβ0, hβ1⟩ hA ⟨hd0, hdle⟩ lam1 lam2 hl1 hl2
  have hmono : A / (1 - β) * Real.exp (-(4 / 3 * (A / (1 - β))))
      ≤ ((lam1 : ℝ) + lam2) * Real.exp (-((lam1 : ℝ) + lam2)) := by
    refine mul_le_mul hlo (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      ?_
    have : (0 : ℝ) < A / (1 - β) := div_pos hA hβ'
    linarith
  calc c1 A β r * Real.sqrt (epsResidual A β d r)
      ≤ c1 A β r * (d * Real.sqrt (c2 β * A / |Real.log r|)) := by
        refine mul_le_mul_of_nonneg_left hsqrt (c1_pos ⟨hβ0, hβ1⟩ hA hr).le
    _ = A / (1 - β) * Real.exp (-(4 / 3 * (A / (1 - β)))) * Real.exp A * d :=
        hcollapse
    _ ≤ ((lam1 : ℝ) + lam2) * Real.exp (-((lam1 : ℝ) + lam2))
          * Real.exp A * d := by
        have hEd : 0 ≤ Real.exp A * d := by positivity
        calc A / (1 - β) * Real.exp (-(4 / 3 * (A / (1 - β)))) * Real.exp A * d
            = A / (1 - β) * Real.exp (-(4 / 3 * (A / (1 - β))))
                * (Real.exp A * d) := by ring
          _ ≤ ((lam1 : ℝ) + lam2) * Real.exp (-((lam1 : ℝ) + lam2))
                * (Real.exp A * d) := mul_le_mul_of_nonneg_right hmono hEd
          _ = ((lam1 : ℝ) + lam2) * Real.exp (-((lam1 : ℝ) + lam2))
                * Real.exp A * d := by ring
    _ ≤ W1 (twoAtomCPLaw A (β - d) (β + d) lam1 lam2)
          (logPoissonLaw A (Real.log β) lam) :=
        theorem12_W1_lower ⟨hβ0, hβ1⟩ ⟨hd0, hdle⟩ lam1 lam2 lam

/-! ## Theorem 10's Wasserstein display, genuine-`W₁` form -/

/-- **Theorem 10 (reading (i), genuine Wasserstein form)**: under the
LK-form hypotheses with A1 residuals measured against the true limit,
the *normalized* tilted measure obeys
`W₁(η/‖η‖, δ_β) ≤ √((1+β)·ε/‖η‖)` — the paper's display, now with `W₁`
the dual-form Kantorovich–Rubinstein distance rather than its
first-absolute-moment unfolding.  (In the paper's normalization
`‖η‖ = |A|`, giving `√((1+β)|ln r|/|A|)·√ε`.) -/
theorem theorem10_wasserstein_W1 {ν : Measure ℝ} {a σ2 k β ε : ℝ}
    (hk : 0 < k) (hσ2 : 0 ≤ σ2) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν)
    (hres : ∀ m : ℕ, |lkPhi a σ2 ν k ((m + 1 : ℕ) * k)
      - (1 - β) * lkC0 a ν k - β * lkPhi a σ2 ν k (m * k)| ≤ ε)
    (hmass : 0 < (tiltedMeasure ν k).real Set.univ) :
    W1 ((tiltedMeasure ν k Set.univ)⁻¹ • tiltedMeasure ν k)
        (Measure.dirac β)
      ≤ Real.sqrt ((1 + β) * ε / (tiltedMeasure ν k).real Set.univ) := by
  obtain ⟨hσ0, hjump, hcomp, _hlim, _ht, _hdict⟩ :=
    theorem10_step0 hk hσ2 hβ hgint hres
  haveI hfin := isFiniteMeasure_tiltedMeasure hk
    (nu_Iio_lt_top hk (hgint 0 le_rfl)) hcomp
  have htop : tiltedMeasure ν k Set.univ ≠ ⊤ := measure_ne_top _ _
  have hne : tiltedMeasure ν k Set.univ ≠ 0 := by
    intro h
    rw [measureReal_def, h, ENNReal.toReal_zero] at hmass
    exact lt_irrefl _ hmass
  haveI : IsProbabilityMeasure
      ((tiltedMeasure ν k Set.univ)⁻¹ • tiltedMeasure ν k) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hne htop]⟩
  -- the normalized measure lives on `[0,1]`
  have hbar : ∀ᵐ u ∂((tiltedMeasure ν k Set.univ)⁻¹ • tiltedMeasure ν k),
      |u| ≤ 1 := by
    refine Measure.ae_smul_measure ?_ _
    filter_upwards [tiltedMeasure_ae_Icc hk] with u hu
    rw [abs_le]
    exact ⟨by linarith [hu.1], hu.2⟩
  rw [W1_dirac hbar β, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    ← measureReal_def]
  exact theorem10_wasserstein_known hk hσ2 hβ hgint hres hmass

end Freeburg

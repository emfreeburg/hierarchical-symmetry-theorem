/-
Freeburg formalization — Corollaries.lean
Corollary 19 (§7) and Corollaries 20–23 (§8) of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632 (v3 draft).
-/
import Freeburg.Basic
import Freeburg.LevyKhintchine
import Freeburg.PropagationLower

/-!
# Corollaries: conservation, spectrum geometry, native stability constants

The paper's closing corollaries are arithmetic consequences of the closed
form `ζ_p = γp + C(1−β^{p/k})` and of the stability theory:

* `Freeburg.corollary20_conservation` — an exact conservation law
  `ζ_{k₀} = z₀` pins the drift: `γ = (z₀ − C(1−β^{k₀/k}))/k₀`.
* `Freeburg.corollary21_unique_curve` — with `(C, β)` fixed and the
  conservation constraint imposed, the exponent curve is determined:
  two conserving curves with the same `(C, β)` coincide (so `β` alone
  parametrizes the family once `C = C_geom` is identified).
* `Freeburg.slCurve_hasDerivAt`, `Freeburg.corollary22_spectrum_width` —
  the singularity-exponent range of the closed form: the slope
  `h(p) = ζ′(p) = γ − (C ln β/k)β^{p/k}` runs from
  `h_max = γ + (C/k)|ln β|` at `p = 0` down to `h_min = γ` as
  `p → ∞`, so the spectrum width is `Δh = (C/k)|ln β|` exactly.
* `Freeburg.corollary23_native_stability` — Theorem 10's Wasserstein
  bound with the scale-free mass `‖η‖ = C(1−β)` substituted:
  `W₁(η/‖η‖, δ_β) ≤ √((1+β)/(C(1−β)))·√ε`.  Because the formalization
  is normalized to `|ln r| = 1` and `k = 1`, this single statement *is*
  both Corollary 23 (the discrete constants are scale-ratio-free) and
  Corollary 19 (the native continuous constants under the dictionary
  `ln r ↦ −1`) — the paper's remark that the two sets of constants are
  identical is here a single theorem.
* `Freeburg.corollary23_turbulence` — the She–Lévêque instantiation
  `(β, C) = (2/3, 2)`: the reading-(i) constant is `√(5/2)` exactly.

Everything in this file is sorry-free.
-/

open MeasureTheory Filter
open scoped Topology

namespace Freeburg

/-! ## Corollary 20: the conservation constraint -/

/-- **Corollary 20 (Conservation constraint)**: if the closed-form
exponent curve satisfies `ζ_{k₀} = z₀` at some index `k₀ ≠ 0`, the drift
is pinned: `γ = (z₀ − C(1−β^{k₀/k}))/k₀` — two observable parameters
reduce to one. -/
theorem corollary20_conservation {γ C β k k0 z0 : ℝ} (hk0 : k0 ≠ 0)
    (h : γ * k0 + C * (1 - β ^ (k0 / k)) = z0) :
    γ = (z0 - C * (1 - β ^ (k0 / k))) / k0 := by
  field_simp
  linarith

/-! ## Corollary 21: `β` alone determines the curve -/

/-- **Corollary 21 (Codimension identification)**: once the intensity is
identified (`C = C_geom`) and an exact conservation law is imposed, the
curve is a function of `β` alone — formally, two conserving closed-form
curves with the same `(C, β)` are identical at every order. -/
theorem corollary21_unique_curve {γ₁ γ₂ C β k k0 z0 : ℝ} (hk0 : k0 ≠ 0)
    (h₁ : γ₁ * k0 + C * (1 - β ^ (k0 / k)) = z0)
    (h₂ : γ₂ * k0 + C * (1 - β ^ (k0 / k)) = z0) :
    ∀ p : ℝ, γ₁ * p + C * (1 - β ^ (p / k))
      = γ₂ * p + C * (1 - β ^ (p / k)) := by
  have hγ : γ₁ = γ₂ := by
    have e₁ := corollary20_conservation hk0 h₁
    have e₂ := corollary20_conservation hk0 h₂
    rw [e₁, e₂]
  intro p
  rw [hγ]

/-! ## Corollary 22: the spectrum width -/

/-- The She–Lévêque exponent curve in exponential form,
`ζ(p) = γp + C(1 − e^{(p/k)ln β})` — equal to the `rpow` form for
`β > 0` (`Real.rpow_def_of_pos`). -/
noncomputable def slCurve (γ C β k p : ℝ) : ℝ :=
  γ * p + C * (1 - Real.exp (p / k * Real.log β))

lemma slCurve_eq_rpow {β : ℝ} (hβ : 0 < β) (γ C k p : ℝ) :
    slCurve γ C β k p = γ * p + C * (1 - β ^ (p / k)) := by
  rw [slCurve, Real.rpow_def_of_pos hβ, mul_comm (Real.log β)]

/-- The singularity exponent (local slope) of the closed form:
`h(p) = γ − (C ln β / k)·e^{(p/k)ln β}`. -/
noncomputable def slSlope (γ C β k p : ℝ) : ℝ :=
  γ - C * Real.log β / k * Real.exp (p / k * Real.log β)

/-- The closed-form curve is differentiable with derivative `slSlope`. -/
lemma slCurve_hasDerivAt (γ C β k p : ℝ) :
    HasDerivAt (slCurve γ C β k) (slSlope γ C β k p) p := by
  have h1 : HasDerivAt (fun q : ℝ => q / k * Real.log β)
      (Real.log β / k) p := by
    convert ((hasDerivAt_id p).div_const k).mul_const (Real.log β) using 1
    ring
  have h2 : HasDerivAt (fun q : ℝ => Real.exp (q / k * Real.log β))
      (Real.exp (p / k * Real.log β) * (Real.log β / k)) p :=
    (Real.hasDerivAt_exp _).comp p h1
  have h3 : HasDerivAt (fun q : ℝ => γ * q) γ p := by
    simpa using (hasDerivAt_id p).const_mul γ
  have h4 : HasDerivAt
      (fun q : ℝ => C * (1 - Real.exp (q / k * Real.log β)))
      (C * (0 - Real.exp (p / k * Real.log β) * (Real.log β / k))) p := by
    exact ((hasDerivAt_const p (1 : ℝ)).sub h2).const_mul C
  have hsum := h3.add h4
  have heq : slSlope γ C β k p
      = γ + C * (0 - Real.exp (p / k * Real.log β) * (Real.log β / k)) := by
    simp only [slSlope]
    ring
  unfold slCurve
  rw [heq]
  exact hsum

/-- **Corollary 22 (Spectrum width)**: for `β ∈ (0,1)`, `C > 0`,
`k > 0`, the slope of the closed form at `p = 0` is
`h_max = γ + (C/k)|ln β|`, its limit as `p → ∞` is `h_min = γ`, and the
width is `Δh = h_max − h_min = (C/k)|ln β|` exactly. -/
theorem corollary22_spectrum_width {γ C β k : ℝ}
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hk : 0 < k) :
    slSlope γ C β k 0 = γ + C / k * |Real.log β|
      ∧ Tendsto (slSlope γ C β k) atTop (𝓝 γ)
      ∧ slSlope γ C β k 0 - γ = C / k * |Real.log β| := by
  have hlog : Real.log β < 0 := Real.log_neg hβ.1 hβ.2
  have habs : |Real.log β| = -Real.log β := abs_of_neg hlog
  constructor
  · simp only [slSlope, zero_div, zero_mul, Real.exp_zero, mul_one, habs]
    ring
  constructor
  · have harg : Tendsto (fun p : ℝ => p / k * Real.log β) atTop atBot := by
      have hdiv : Tendsto (fun p : ℝ => p / k) atTop atTop :=
        tendsto_id.atTop_div_const hk
      exact hdiv.atTop_mul_const_of_neg' hlog
    have hexp : Tendsto (fun p : ℝ => Real.exp (p / k * Real.log β))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp harg
    have : Tendsto (fun p : ℝ =>
        γ - C * Real.log β / k * Real.exp (p / k * Real.log β))
        atTop (𝓝 (γ - C * Real.log β / k * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hexp)
    simpa [slSlope] using this
  · simp only [slSlope, zero_div, zero_mul, Real.exp_zero, mul_one, habs]
    ring

/-! ## Corollaries 19 and 23: the native / scale-ratio-free constants -/

/-- **Corollaries 19 and 23 (Stability with native, parameter-free
constants)**: substituting the mass identity `‖η‖ = C(1−β)` into
Theorem 10's Wasserstein display gives

  `W₁(η/‖η‖, δ_β) ≤ √((1+β)/(C(1−β))) · √ε`

with the constant depending only on `(β, C)`.  At the formalization's
normalization (`k = 1`, `|ln r| = 1`) this single statement carries both
readings of the paper: Corollary 23 (the discrete constants are
scale-ratio-free — every `|ln r|` has cancelled) and Corollary 19 (the
native continuous-cascade constants under the dictionary `ln r ↦ −1`,
where `‖η‖ = |A_c| = C(1−β)` exactly). -/
theorem corollary23_native_stability {ν : Measure ℝ} {a σ2 k β ε C : ℝ}
    (hk : 0 < k) (hσ2 : 0 ≤ σ2) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hC : 0 < C)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν)
    (hres : ∀ m : ℕ, |lkPhi a σ2 ν k ((m + 1 : ℕ) * k)
      - (1 - β) * lkC0 a ν k - β * lkPhi a σ2 ν k (m * k)| ≤ ε)
    (hmass : (tiltedMeasure ν k).real Set.univ = C * (1 - β)) :
    W1 ((tiltedMeasure ν k Set.univ)⁻¹ • tiltedMeasure ν k)
        (Measure.dirac β)
      ≤ Real.sqrt ((1 + β) / (C * (1 - β))) * Real.sqrt ε := by
  have h1β : (0 : ℝ) < 1 - β := by linarith [hβ.2]
  have hmasspos : 0 < (tiltedMeasure ν k).real Set.univ := by
    rw [hmass]; exact mul_pos hC h1β
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hres 0)
  have h := theorem10_wasserstein_W1 hk hσ2 hβ hgint hres hmasspos
  rw [hmass] at h
  calc W1 ((tiltedMeasure ν k Set.univ)⁻¹ • tiltedMeasure ν k)
        (Measure.dirac β)
      ≤ Real.sqrt ((1 + β) * ε / (C * (1 - β))) := h
    _ = Real.sqrt ((1 + β) / (C * (1 - β)) * ε) := by ring_nf
    _ = Real.sqrt ((1 + β) / (C * (1 - β))) * Real.sqrt ε :=
        Real.sqrt_mul
          (div_nonneg (by linarith [hβ.1]) (mul_pos hC h1β).le) ε

/-- **Corollary 23, She–Lévêque instantiation**: at the turbulence
parameters `(β, C) = (2/3, 2)` the reading-(i) constant is `√(5/2)`
(`≈ 1.58`) exactly: `W₁ ≤ √(5/2)·√ε`. -/
theorem corollary23_turbulence {ν : Measure ℝ} {a σ2 k ε : ℝ}
    (hk : 0 < k) (hσ2 : 0 ≤ σ2)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν)
    (hres : ∀ m : ℕ, |lkPhi a σ2 ν k ((m + 1 : ℕ) * k)
      - (1 - 2/3) * lkC0 a ν k - 2/3 * lkPhi a σ2 ν k (m * k)| ≤ ε)
    (hmass : (tiltedMeasure ν k).real Set.univ = 2 * (1 - 2/3)) :
    W1 ((tiltedMeasure ν k Set.univ)⁻¹ • tiltedMeasure ν k)
        (Measure.dirac (2/3))
      ≤ Real.sqrt (5 / 2) * Real.sqrt ε := by
  have h := corollary23_native_stability (C := 2) hk hσ2
    (by constructor <;> norm_num) (by norm_num) hgint hres hmass
  have : ((1 : ℝ) + 2/3) / (2 * (1 - 2/3)) = 5 / 2 := by norm_num
  rwa [this] at h

end Freeburg

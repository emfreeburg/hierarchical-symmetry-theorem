/-
Freeburg formalization — LevyKhintchine.lean
Theorem 7 (Log-ID Classification, forward direction) and
Theorem 10, Step 0, of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632.
-/
import Freeburg.Basic
import Freeburg.Dirac
import Freeburg.Stability

/-!
# Lévy–Khintchine-form cumulant calculus

The paper's Theorems 7 and 10 quantify over Lévy triplets `(a, σ², ν)`
in their hypotheses: the generator `log W` is infinitely divisible
*with that triplet*, so its cumulant generating function is
`ψ(p) = ap + σ²p²/2 + ∫ (e^{px} − 1 − px·1_{|x|≤1}) dν`.  This file
formalizes the class **definitionally at the cumulant level** — the
step-`k` cumulant increment `φ(p) = ψ(p+k) − ψ(p)` in the paper's
unsplit form (Theorem 7, Step 1)

  `φ(p) = ak + σ²k(p + k/2) + ∫ g_p dν`,
  `g_p(x) = e^{px}(e^{kx} − 1) − kx·1_{|x|≤1}`,

and proves the paper's Steps 1′–4 about it.  (The bridge from an
abstract infinitely divisible law to this form is the classical
Lévy–Khintchine representation theorem together with the moment-side
analytic continuation; it is *not* formalized — the hypotheses of the
paper's theorems hand us the triplet, so every printed statement is
faithfully covered.)

Main results:

* `Freeburg.gIntegrand_eq_sub` — Step 1: `g_p = f_{p+k} − f_p`, the
  difference of compensated LK integrands ("no splitting is performed").
* sign inventory (Step 1′): `gIntegrand_nonneg` (`g_p ≥ 0` on
  `[−1,∞)`), `gIntegrand_far_bounds` (`−1 ≤ g_p ≤ 0` below `−1`),
  `gIntegrand_le_k_abs`, monotonicity in `p`, and the shell lower
  bounds driving the divergence steps.
* `Freeburg.nu_Iio_lt_top` — the Lévy mass below `−1` is finite (from
  integrability of `g_0` alone).
* divergence trichotomy (Steps 2, 3, 3½): `tendsto_lkPhi_atTop_of_*` —
  a Gaussian component, positive jumps, or a non-integrable compensator
  region each force `φ(mk) → +∞` (so `δ_p → −∞`, killing A1).
* Step 0 of Theorem 10: `lkPhi_lattice_bddAbove_of_*` + the
  contradiction, packaged as `step0_conclusions`.
* the split form (legitimate *after* Step 3½): `lkPhi_split`, the limit
  `tendsto_lkPhi_c0`, and the tilted measure
  `η = (1−u) d(image of ν under e^{kx})` with its moment dictionary
  `integral_pow_tiltedMeasure : ∫ u^m dη = c₀ − φ(mk)`.
* `Freeburg.theorem7_forward_eta` — **Theorem 7, forward direction**:
  exact A1 forces `σ² = 0`, no positive jumps, integrability, and
  `η = |A| δ_β`; `Freeburg.theorem7_forward_nu` — the Lévy measure
  itself is `λ δ_b`, `b = ln β / k`.
* `Freeburg.theorem10_step0` — **Theorem 10, Step 0**: the same
  conclusions under approximate A1, with the exact moment dictionary
  feeding `Freeburg.Stability`.

Everything in this file is sorry-free.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Freeburg

/-! ## The integrands -/

/-- The Lévy–Khintchine truncation `x ↦ x·1_{|x|≤1}`. -/
noncomputable def lkCompensator (x : ℝ) : ℝ :=
  Set.indicator (Set.Icc (-1 : ℝ) 1) id x

lemma lkCompensator_of_mem {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    lkCompensator x = x :=
  Set.indicator_of_mem hx id

lemma lkCompensator_of_notMem {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) :
    lkCompensator x = 0 :=
  Set.indicator_of_notMem hx id

lemma abs_lkCompensator_le_one (x : ℝ) : |lkCompensator x| ≤ 1 := by
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · rw [lkCompensator_of_mem hx]
    exact abs_le.mpr ⟨hx.1, hx.2⟩
  · rw [lkCompensator_of_notMem hx]
    simp

lemma measurable_lkCompensator : Measurable lkCompensator :=
  measurable_id.indicator measurableSet_Icc

/-- The compensated Lévy–Khintchine integrand
`f_q(x) = e^{qx} − 1 − qx·1_{|x|≤1}`. -/
noncomputable def lkIntegrand (q x : ℝ) : ℝ :=
  Real.exp (q * x) - 1 - q * lkCompensator x

/-- The paper's `g_p(x) = e^{px}(e^{kx} − 1) − kx·1_{|x|≤1}` —
the step-`k` increment integrand (Theorem 7, Step 1). -/
noncomputable def gIntegrand (k p x : ℝ) : ℝ :=
  Real.exp (p * x) * (Real.exp (k * x) - 1) - k * lkCompensator x

/-- **Theorem 7, Step 1** of the paper: `g_p` is exactly the difference
of the two compensated Lévy–Khintchine integrands — *no splitting of the
integral is performed at this stage*. -/
lemma gIntegrand_eq_sub (k p x : ℝ) :
    gIntegrand k p x = lkIntegrand (p + k) x - lkIntegrand p x := by
  unfold gIntegrand lkIntegrand
  rw [show (p + k) * x = p * x + k * x by ring, Real.exp_add]
  ring

lemma measurable_gIntegrand (k p : ℝ) : Measurable (gIntegrand k p) := by
  unfold gIntegrand
  exact ((Real.measurable_exp.comp (measurable_const_mul p)).mul
    ((Real.measurable_exp.comp (measurable_const_mul k)).sub measurable_const)).sub
    (measurable_lkCompensator.const_mul k)

/-! ## The cumulant forms -/

/-- The Lévy–Khintchine cumulant generating function
`ψ(q) = aq + σ²q²/2 + ∫ f_q dν` — the paper's hypothesis hands us the
triplet `(a, σ², ν)`, and this is what "log-ID with that triplet" means
at the moment level. -/
noncomputable def lkPsi (a σ2 : ℝ) (ν : Measure ℝ) (q : ℝ) : ℝ :=
  a * q + σ2 * q ^ 2 / 2 + ∫ x, lkIntegrand q x ∂ν

/-- The step-`k` cumulant increment in the paper's unsplit form
(Theorem 7, Step 1): `φ(p) = ak + σ²k(p + k/2) + ∫ g_p dν`.
The incremental exponents of the paper are `δ_p = φ(p)/ln r`. -/
noncomputable def lkPhi (a σ2 : ℝ) (ν : Measure ℝ) (k p : ℝ) : ℝ :=
  a * k + σ2 * k * (p + k / 2) + ∫ x, gIntegrand k p x ∂ν

/-- Sanity identity: `φ(p) = ψ(p+k) − ψ(p)` whenever both LK integrands
are integrable, so `lkPhi` *is* the cumulant increment of the LK form. -/
theorem lkPhi_eq_lkPsi_sub {ν : Measure ℝ} (a σ2 k p : ℝ)
    (h1 : Integrable (lkIntegrand (p + k)) ν)
    (h2 : Integrable (lkIntegrand p) ν) :
    lkPhi a σ2 ν k p = lkPsi a σ2 ν (p + k) - lkPsi a σ2 ν p := by
  unfold lkPhi lkPsi
  have hg : ∫ x, gIntegrand k p x ∂ν
      = (∫ x, lkIntegrand (p + k) x ∂ν) - ∫ x, lkIntegrand p x ∂ν := by
    rw [← integral_sub h1 h2]
    exact integral_congr_ae (.of_forall fun x => gIntegrand_eq_sub k p x)
  rw [hg]
  ring

/-! ## Step 1′: the sign inventory of `g_p` -/

/-- `t ≤ e^t − 1` (the convexity inequality used throughout). -/
lemma le_exp_sub_one (t : ℝ) : t ≤ Real.exp t - 1 := by
  linarith [Real.add_one_le_exp t]

/-- **Step 1′, regions `(0,1]`, `(1,∞)`, `[−1,0)` combined**: for
`p ≥ 0` and `x ≥ −1`, the integrand is nonnegative: `g_p(x) ≥ 0`. -/
lemma gIntegrand_nonneg {k p : ℝ} (hk : 0 < k) (hp : 0 ≤ p)
    {x : ℝ} (hx : -1 ≤ x) : 0 ≤ gIntegrand k p x := by
  unfold gIntegrand
  rcases le_or_gt x 1 with hx1 | hx1
  · rw [lkCompensator_of_mem ⟨hx, hx1⟩]
    have hkx : k * x ≤ Real.exp (k * x) - 1 := le_exp_sub_one _
    rcases le_or_gt 0 x with hx0 | hx0
    · have h1 : (1 : ℝ) ≤ Real.exp (p * x) := by
        rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
        exact Real.exp_le_exp.mpr (by positivity)
      have h3 : 0 ≤ k * x := by positivity
      nlinarith
    · have h1 : Real.exp (p * x) ≤ 1 := by
        rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
        exact Real.exp_le_exp.mpr (by nlinarith)
      have h2 : Real.exp (k * x) - 1 ≤ 0 := by
        have : Real.exp (k * x) ≤ 1 := by
          rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
          exact Real.exp_le_exp.mpr (by nlinarith)
        linarith
      have h4 : Real.exp (k * x) - 1
          ≤ Real.exp (p * x) * (Real.exp (k * x) - 1) := by
        nlinarith [Real.exp_pos (p * x)]
      nlinarith
  · rw [lkCompensator_of_notMem (by
      intro hmem
      exact absurd hmem.2 (not_le.mpr hx1))]
    have h2 : 0 ≤ Real.exp (k * x) - 1 := by
      have : (1 : ℝ) ≤ Real.exp (k * x) := by
        rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
        exact Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have := Real.exp_pos (p * x)
    nlinarith

/-- **Step 1′, region `(−∞,−1)`**: there `g_p = e^{px}(e^{kx}−1)` lies
in `[−1, 0]` for every `p ≥ 0`. -/
lemma gIntegrand_far_bounds {k p : ℝ} (hk : 0 < k) (hp : 0 ≤ p)
    {x : ℝ} (hx : x < -1) :
    -1 ≤ gIntegrand k p x ∧ gIntegrand k p x ≤ 0 := by
  unfold gIntegrand
  rw [lkCompensator_of_notMem (by
    intro hmem
    exact absurd hmem.1 (not_le.mpr hx))]
  have hkx : Real.exp (k * x) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hpx : Real.exp (p * x) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h1 := Real.exp_pos (k * x)
  have h2 := Real.exp_pos (p * x)
  constructor <;> nlinarith

/-- The integrand never drops below `−1` anywhere (combining the
regions): the uniform lower bound of Step 1′. -/
lemma gIntegrand_ge_neg_one {k p : ℝ} (hk : 0 < k) (hp : 0 ≤ p) (x : ℝ) :
    -1 ≤ gIntegrand k p x := by
  rcases lt_or_ge x (-1) with hx | hx
  · exact (gIntegrand_far_bounds hk hp hx).1
  · linarith [gIntegrand_nonneg hk hp hx]

/-- **Step 1′, region `[−1,0)` upper bound**: `g_p(x) ≤ k|x|`
(for every real `p` — the exponential factor only helps). -/
lemma gIntegrand_le_k_abs {k p : ℝ} (hk : 0 < k)
    {x : ℝ} (hx1 : -1 ≤ x) (hx0 : x < 0) :
    gIntegrand k p x ≤ k * |x| := by
  unfold gIntegrand
  rw [lkCompensator_of_mem ⟨hx1, by linarith⟩, abs_of_neg hx0]
  have h2 : Real.exp (k * x) - 1 ≤ 0 := by
    have : Real.exp (k * x) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      exact Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have := Real.exp_pos (p * x)
  nlinarith

/-- Monotonicity in `p` (all regions): for fixed `x`, `p ↦ g_p(x)` is
monotone — the engine of the monotone-convergence steps. -/
lemma gIntegrand_mono {k : ℝ} (hk : 0 < k) (x : ℝ) :
    Monotone fun p => gIntegrand k p x := by
  intro p q hpq
  unfold gIntegrand
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hexp : Real.exp (q * x) ≤ Real.exp (p * x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hfac : Real.exp (k * x) - 1 ≤ 0 := by
      have : Real.exp (k * x) ≤ 1 := by
        rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
        exact Real.exp_le_exp.mpr (by nlinarith)
      linarith
    nlinarith
  · simp [hx]
  · have hexp : Real.exp (p * x) ≤ Real.exp (q * x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hfac : 0 ≤ Real.exp (k * x) - 1 := by
      have : (1 : ℝ) ≤ Real.exp (k * x) := by
        rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
        exact Real.exp_le_exp.mpr (by nlinarith)
      linarith
    nlinarith

/-- **Positive-shell lower bound** (drives Step 3): for `x ≥ δ > 0`,
`g_p(x) ≥ e^{pδ}(e^{kδ} − 1) − k`, a constant in `x` that diverges in
`p`. -/
lemma gIntegrand_ge_shell_pos {k p δ : ℝ} (hk : 0 < k) (hp : 0 ≤ p)
    (hδ : 0 < δ) {x : ℝ} (hxδ : δ ≤ x) :
    Real.exp (p * δ) * (Real.exp (k * δ) - 1) - k ≤ gIntegrand k p x := by
  unfold gIntegrand
  have hcomp : k * lkCompensator x ≤ k * 1 := by
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    calc lkCompensator x ≤ |lkCompensator x| := le_abs_self _
      _ ≤ 1 := abs_lkCompensator_le_one x
  have hexp1 : Real.exp (p * δ) ≤ Real.exp (p * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxδ hp)
  have hexp2 : Real.exp (k * δ) ≤ Real.exp (k * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxδ hk.le)
  have hfacδ : 0 ≤ Real.exp (k * δ) - 1 := by
    have : (1 : ℝ) ≤ Real.exp (k * δ) := by
      rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      exact Real.exp_le_exp.mpr (by positivity)
    linarith
  have hmul : Real.exp (p * δ) * (Real.exp (k * δ) - 1)
      ≤ Real.exp (p * x) * (Real.exp (k * x) - 1) := by
    have h1 := (Real.exp_pos (p * δ)).le
    nlinarith
  linarith

/-- **Negative-shell lower bound** (drives Step 3½): for
`−1 ≤ x ≤ −δ < 0`, `g_p(x) ≥ (1 − e^{−pδ})·k·|x|`: the integrand
captures the full compensator mass `k|x|` as `p → ∞`. -/
lemma gIntegrand_ge_shell_neg {k p δ : ℝ} (hk : 0 < k) (hp : 0 ≤ p)
    (hδ : 0 < δ) {x : ℝ} (hx1 : -1 ≤ x) (hxδ : x ≤ -δ) :
    (1 - Real.exp (-(p * δ))) * (k * |x|) ≤ gIntegrand k p x := by
  have hx0 : x < 0 := lt_of_le_of_lt hxδ (by linarith)
  unfold gIntegrand
  rw [lkCompensator_of_mem ⟨hx1, by linarith⟩, abs_of_neg hx0]
  -- 1 − e^{kx} ≤ k(−x), and e^{px} ≤ e^{−pδ}
  have hkx : 1 - Real.exp (k * x) ≤ k * (-x) := by
    have := le_exp_sub_one (k * x)
    nlinarith
  have hpx : Real.exp (p * x) ≤ Real.exp (-(p * δ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hkx0 : 0 ≤ 1 - Real.exp (k * x) := by
    have : Real.exp (k * x) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      exact Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hbound : Real.exp (p * x) * (1 - Real.exp (k * x))
      ≤ Real.exp (-(p * δ)) * (k * (-x)) := by
    have h1 := (Real.exp_pos (p * x)).le
    have h2 : 0 ≤ k * (-x) := by nlinarith
    nlinarith
  nlinarith [hbound]

/-- The exponential factor vanishes along the lattice for `x < 0`:
`e^{(mk)x} → 0`. -/
lemma tendsto_exp_lattice_neg {k x : ℝ} (hk : 0 < k) (hx : x < 0) :
    Tendsto (fun m : ℕ => Real.exp ((m * k) * x)) atTop (𝓝 0) := by
  have harg : Tendsto (fun m : ℕ => (m : ℝ) * k * x) atTop atBot := by
    have h1 : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun m : ℕ => (m : ℝ) * (k * x)) atTop atBot :=
      h1.atTop_mul_const_of_neg (by nlinarith)
    refine h2.congr fun m => by ring
  exact Real.tendsto_exp_atBot.comp harg

/-! ## Finiteness of the far mass -/

/-- The Lévy mass below `−1` is finite — from integrability of `g_0`
alone: on `(−∞,−1)`, `|g_0| = 1 − e^{kx} ≥ 1 − e^{−k} > 0`. -/
lemma nu_Iio_lt_top {ν : Measure ℝ} {k : ℝ} (hk : 0 < k)
    (hgint : Integrable (gIntegrand k 0) ν) :
    ν (Set.Iio (-1 : ℝ)) < ⊤ := by
  have hsub : Set.Iio (-1 : ℝ)
      ⊆ {x : ℝ | 1 - Real.exp (-k) ≤ ‖gIntegrand k 0 x‖} := by
    intro x hx
    simp only [Set.mem_Iio] at hx
    simp only [Set.mem_setOf_eq]
    unfold gIntegrand
    rw [lkCompensator_of_notMem (by
      intro hmem
      exact absurd hmem.1 (not_le.mpr hx))]
    rw [zero_mul, Real.exp_zero, one_mul, mul_zero, sub_zero,
      Real.norm_eq_abs]
    have h1 : Real.exp (k * x) ≤ Real.exp (-k) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp (k * x) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      exact Real.exp_le_exp.mpr (by nlinarith)
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hpos : 0 < 1 - Real.exp (-k) := by
    have : Real.exp (-k) < 1 := by
      rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      exact Real.exp_lt_exp.mpr (by linarith)
    linarith
  exact lt_of_le_of_lt (measure_mono hsub)
    (hgint.measure_norm_ge_lt_top hpos)

/-! ## The splitting bound

Every divergence step has the same shape: a region above `−1`
contributes a large positive amount, the region below `−1` costs at most
its (finite) mass.  This lemma packages the assembly. -/

/-- For any measurable `s ⊆ [−1, ∞)`:
`∫ g_p dν ≥ ∫_s g_p dν − ν((−∞,−1))`. -/
lemma setIntegral_g_sub_le {ν : Measure ℝ} {k p : ℝ} (hk : 0 < k)
    (hp : 0 ≤ p) (hgint : Integrable (gIntegrand k p) ν)
    (hfar : ν (Set.Iio (-1 : ℝ)) < ⊤)
    {s : Set ℝ} (hsub : s ⊆ Set.Ici (-1 : ℝ)) :
    (∫ x in s, gIntegrand k p x ∂ν) - (ν (Set.Iio (-1 : ℝ))).toReal
      ≤ ∫ x, gIntegrand k p x ∂ν := by
  have hsplit : ∫ x, gIntegrand k p x ∂ν
      = (∫ x in Set.Iio (-1 : ℝ), gIntegrand k p x ∂ν)
        + ∫ x in Set.Ici (-1 : ℝ), gIntegrand k p x ∂ν := by
    rw [← setIntegral_union (Set.Iio_disjoint_Ici le_rfl) measurableSet_Ici
      hgint.integrableOn hgint.integrableOn, Set.Iio_union_Ici,
      setIntegral_univ]
  have hfarbound : -(ν (Set.Iio (-1 : ℝ))).toReal
      ≤ ∫ x in Set.Iio (-1 : ℝ), gIntegrand k p x ∂ν := by
    have hnorm : ‖∫ x in Set.Iio (-1 : ℝ), gIntegrand k p x ∂ν‖
        ≤ 1 * (ν.real (Set.Iio (-1 : ℝ))) := by
      refine norm_setIntegral_le_of_norm_le_const hfar fun x hx => ?_
      rw [Real.norm_eq_abs]
      obtain ⟨h1, h2⟩ := gIntegrand_far_bounds hk hp hx
      rw [abs_le]
      exact ⟨h1, by linarith⟩
    rw [Real.norm_eq_abs, abs_le] at hnorm
    have := hnorm.1
    simp only [Measure.real] at this ⊢
    linarith
  have hmono : (∫ x in s, gIntegrand k p x ∂ν)
      ≤ ∫ x in Set.Ici (-1 : ℝ), gIntegrand k p x ∂ν := by
    refine setIntegral_mono_set hgint.integrableOn ?_ hsub.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    exact gIntegrand_nonneg hk hp hx
  linarith [hsplit, hfarbound, hmono]

/-! ## The divergence trichotomy (Theorem 7, Steps 2, 3, 3½)

Each of the three structural defects — a Gaussian component, positive
jumps, a non-integrable compensator region — forces the cumulant
increments `φ(mk)` to `+∞` along the lattice, i.e. `δ_p → −∞`:
incompatible with A1 (which keeps the lattice sequence bounded). -/

/-- **Theorem 7, Step 2**: a Gaussian component (`σ² > 0`) forces
`φ(mk) → +∞`.  *This eliminates all log-normal and mixed Gaussian-jump
generators.* -/
theorem tendsto_lkPhi_atTop_of_sigma_pos {ν : Measure ℝ} {a σ2 k : ℝ}
    (hk : 0 < k) (hσ : 0 < σ2)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν) :
    Tendsto (fun m : ℕ => lkPhi a σ2 ν k (m * k)) atTop atTop := by
  have hfar := nu_Iio_lt_top hk (hgint 0 le_rfl)
  set c : ℝ := (ν (Set.Iio (-1 : ℝ))).toReal with hc
  have hlow : ∀ m : ℕ,
      σ2 * k * k * m + (a * k + σ2 * k * (k / 2) - c)
        ≤ lkPhi a σ2 ν k (m * k) := by
    intro m
    have hint : (0 : ℝ) - c ≤ ∫ x, gIntegrand k (m * k) x ∂ν := by
      have h := setIntegral_g_sub_le hk (by positivity)
        (hgint (m * k) (by positivity)) hfar (Set.empty_subset _)
      simpa using h
    unfold lkPhi
    nlinarith [hint]
  refine tendsto_atTop_mono hlow ?_
  have h1 : Tendsto (fun m : ℕ => σ2 * k * k * m) atTop atTop := by
    have hpos : 0 < σ2 * k * k := by positivity
    have := tendsto_natCast_atTop_atTop (R := ℝ)
    exact Tendsto.const_mul_atTop hpos this
  exact tendsto_atTop_add_const_right atTop _ h1

/-- **Theorem 7, Step 3**: positive Lévy mass forces `φ(mk) → +∞`
(monotone growth of `g_p` on a positive shell).  *This eliminates all
generators with positive jumps.* -/
theorem tendsto_lkPhi_atTop_of_pos_jumps {ν : Measure ℝ} {a σ2 k : ℝ}
    (hk : 0 < k) (hσ : 0 ≤ σ2)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν)
    (hν : ν (Set.Ioi (0 : ℝ)) ≠ 0) :
    Tendsto (fun m : ℕ => lkPhi a σ2 ν k (m * k)) atTop atTop := by
  have hfar := nu_Iio_lt_top hk (hgint 0 le_rfl)
  set c : ℝ := (ν (Set.Iio (-1 : ℝ))).toReal with hc
  -- find a shell [δ, ∞) of positive measure
  have hshell : ∃ δ : ℝ, 0 < δ ∧ ν (Set.Ici δ) ≠ 0 := by
    by_contra hno
    push Not at hno
    have hcover : Set.Ioi (0 : ℝ)
        ⊆ ⋃ n : ℕ, Set.Ici (1 / ((n : ℝ) + 1)) := by
      intro x hx
      simp only [Set.mem_Ioi] at hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact Set.mem_iUnion.mpr ⟨n, le_of_lt hn⟩
    refine hν (measure_mono_null hcover (measure_iUnion_null fun n => ?_))
    exact hno (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨δ, hδ, hνδ⟩ := hshell
  -- the shell has finite measure (g is eventually ≥ 1 there)
  have hδfin : ν (Set.Ici δ) < ⊤ := by
    have hgrow : Tendsto (fun p : ℝ => Real.exp (p * δ) * (Real.exp (k * δ) - 1) - k)
        atTop atTop := by
      have hfac : 0 < Real.exp (k * δ) - 1 := by
        have : (1 : ℝ) < Real.exp (k * δ) := by
          rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
          exact Real.exp_lt_exp.mpr (by positivity)
        linarith
      have h1 : Tendsto (fun p : ℝ => p * δ) atTop atTop :=
        Tendsto.atTop_mul_const hδ tendsto_id
      have h2 : Tendsto (fun p : ℝ => Real.exp (p * δ)) atTop atTop :=
        Real.tendsto_exp_atTop.comp h1
      exact tendsto_atTop_add_const_right atTop _ (h2.atTop_mul_const hfac)
    obtain ⟨A, hA⟩ := eventually_atTop.mp (hgrow.eventually_ge_atTop 1)
    set p₀ : ℝ := max A 0 with hp₀def
    have hp₀0 : (0 : ℝ) ≤ p₀ := le_max_right _ _
    have hp₀1 : 1 ≤ Real.exp (p₀ * δ) * (Real.exp (k * δ) - 1) - k :=
      hA p₀ (le_max_left _ _)
    have hsub : Set.Ici δ ⊆ {x : ℝ | 1 ≤ ‖gIntegrand k p₀ x‖} := by
      intro x hx
      simp only [Set.mem_setOf_eq, Real.norm_eq_abs]
      have h := gIntegrand_ge_shell_pos hk hp₀0 hδ (Set.mem_Ici.mp hx)
      have h1 : 1 ≤ gIntegrand k p₀ x := le_trans hp₀1 h
      exact le_trans h1 (le_abs_self _)
    exact lt_of_le_of_lt (measure_mono hsub)
      ((hgint p₀ hp₀0).measure_norm_ge_lt_top one_pos)
  have hρ : 0 < (ν (Set.Ici δ)).toReal :=
    ENNReal.toReal_pos hνδ hδfin.ne
  set ρ : ℝ := (ν (Set.Ici δ)).toReal with hρdef
  -- the lower-bound sequence diverges
  have hlow : ∀ m : ℕ,
      (Real.exp ((m * k) * δ) * (Real.exp (k * δ) - 1) - k) * ρ + (a * k - c)
        ≤ lkPhi a σ2 ν k (m * k) := by
    intro m
    have hpm : (0 : ℝ) ≤ m * k := by positivity
    have hshellint : (Real.exp ((m * k) * δ) * (Real.exp (k * δ) - 1) - k) * ρ
        ≤ ∫ x in Set.Ici δ, gIntegrand k (m * k) x ∂ν := by
      refine setIntegral_ge_of_const_le_real measurableSet_Ici hδfin.ne
        (fun x hx => gIntegrand_ge_shell_pos hk hpm hδ (Set.mem_Ici.mp hx))
        ((hgint (m * k) hpm).integrableOn)
    have hassemble := setIntegral_g_sub_le (s := Set.Ici δ) hk hpm
      (hgint (m * k) hpm) hfar
      (fun x hx => le_trans (by linarith : (-1 : ℝ) ≤ δ) hx)
    have hσterm : 0 ≤ σ2 * k * ((m * k) + k / 2) := by positivity
    unfold lkPhi
    nlinarith [hshellint, hassemble]
  refine tendsto_atTop_mono hlow ?_
  have hfac : 0 < Real.exp (k * δ) - 1 := by
    have : (1 : ℝ) < Real.exp (k * δ) := by
      rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      exact Real.exp_lt_exp.mpr (by positivity)
    linarith
  have h1 : Tendsto (fun m : ℕ => Real.exp ((m * k) * δ)) atTop atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    have := tendsto_natCast_atTop_atTop (R := ℝ)
    have h2 : Tendsto (fun m : ℕ => (m : ℝ) * (k * δ)) atTop atTop :=
      this.atTop_mul_const (by positivity)
    exact h2.congr fun m => by ring
  have h2 : Tendsto
      (fun m : ℕ => (Real.exp ((m * k) * δ) * (Real.exp (k * δ) - 1) - k) * ρ)
      atTop atTop :=
    ((tendsto_atTop_add_const_right atTop (-k)
      (h1.atTop_mul_const hfac)).atTop_mul_const hρ)
  exact tendsto_atTop_add_const_right atTop _ h2

/-- **Theorem 7, Step 3½**: a non-integrable compensator region —
`∫_{[−1,0)} |x| dν = ∞` — forces `φ(mk) → +∞` (Fatou capture of the
compensator mass).  *This eliminates totally skewed stable generators of
index `α ∈ [1,2)`.* -/
theorem tendsto_lkPhi_atTop_of_compensator_infinite {ν : Measure ℝ}
    {a σ2 k : ℝ} (hk : 0 < k) (hσ : 0 ≤ σ2)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν)
    (hcomp : ∫⁻ x in Set.Ico (-1 : ℝ) 0, ENNReal.ofReal |x| ∂ν = ⊤) :
    Tendsto (fun m : ℕ => lkPhi a σ2 ν k (m * k)) atTop atTop := by
  have hfar := nu_Iio_lt_top hk (hgint 0 le_rfl)
  set c : ℝ := (ν (Set.Iio (-1 : ℝ))).toReal with hc
  -- shells [−1, −1/(n+1)]: finite ν-mass, exhaust the compensator mass
  set shell : ℕ → Set ℝ := fun n => Set.Icc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    with hshell
  have hshellmeas : ∀ n, MeasurableSet (shell n) := fun n => measurableSet_Icc
  have hshellsub : ∀ n, shell n ⊆ Set.Ici (-1 : ℝ) := fun n x hx => hx.1
  have hshellfin : ∀ n, ν (shell n) < ⊤ := by
    intro n
    set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
    have hδ : 0 < δ := by positivity
    have hE1 : Real.exp (-(1 * δ)) < 1 := by
      have h := Real.exp_lt_exp.mpr (show -(1 * δ) < 0 by nlinarith)
      rwa [Real.exp_zero] at h
    have hE0 : 0 < 1 - Real.exp (-(1 * δ)) := by linarith
    have hcn : 0 < (1 - Real.exp (-(1 * δ))) * (k * δ) := by positivity
    have hsub : shell n ⊆
        {x : ℝ | (1 - Real.exp (-(1 * δ))) * (k * δ) ≤ ‖gIntegrand k 1 x‖} := by
      intro x hx
      simp only [Set.mem_setOf_eq, Real.norm_eq_abs]
      have hx1 : -1 ≤ x := hx.1
      have hxδ : x ≤ -δ := hx.2
      have hlow := gIntegrand_ge_shell_neg hk zero_le_one hδ hx1 hxδ
      have habs : δ ≤ |x| := by
        rw [abs_of_neg (by linarith : x < 0)]
        linarith
      have h1 : (1 - Real.exp (-(1 * δ))) * (k * δ)
          ≤ (1 - Real.exp (-(1 * δ))) * (k * |x|) := by
        nlinarith
      exact le_trans (le_trans h1 hlow) (le_abs_self _)
    exact lt_of_le_of_lt (measure_mono hsub)
      ((hgint 1 zero_le_one).measure_norm_ge_lt_top hcn)
  -- the shell compensator masses tend to ⊤
  have hmono : Monotone shell := by
    intro i j hij x hx
    refine ⟨hx.1, le_trans hx.2 ?_⟩
    have hcast : ((i : ℝ)) + 1 ≤ (j : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).mpr hij
      linarith
    have h1 : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hcast
    linarith
  have hcup : Set.Ico (-1 : ℝ) 0 ⊆ ⋃ n, shell n := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < -x by
      linarith [hx.2])
    exact Set.mem_iUnion.mpr ⟨n, hx.1, by linarith⟩
  set W : Measure ℝ := ν.withDensity (fun x => ENNReal.ofReal |x|) with hW
  have hWshell : Tendsto (fun n => W (shell n)) atTop (𝓝 (W (⋃ n, shell n))) :=
    tendsto_measure_iUnion_atTop hmono
  have hWtop : W (⋃ n, shell n) = ⊤ := by
    refine eq_top_iff.mpr ?_
    calc (⊤ : ℝ≥0∞) = ∫⁻ x in Set.Ico (-1 : ℝ) 0, ENNReal.ofReal |x| ∂ν :=
          hcomp.symm
      _ = W (Set.Ico (-1 : ℝ) 0) := by
          rw [hW, withDensity_apply _ measurableSet_Ico]
      _ ≤ W (⋃ n, shell n) := measure_mono hcup
  rw [hWtop] at hWshell
  -- divergence: for every target b, find a shell then go far in m
  rw [tendsto_atTop]
  intro b
  set R : ℝ := max (2 * (b - a * k + c) / k) 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR1 : 2 * (b - a * k + c) / k ≤ R := le_max_left _ _
  -- choose a shell with compensator mass ≥ R
  obtain ⟨n, hn⟩ :=
    (hWshell.eventually (lt_mem_nhds
      (show ENNReal.ofReal R < ⊤ from ENNReal.ofReal_lt_top))).exists
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
  have hδ : 0 < δ := by positivity
  -- the real compensator mass of the chosen shell
  have hWfin : W (shell n) < ⊤ := by
    have hle : W (shell n) ≤ ν (shell n) := by
      rw [hW, withDensity_apply _ (hshellmeas n)]
      calc ∫⁻ x in shell n, ENNReal.ofReal |x| ∂ν
          ≤ ∫⁻ _x in shell n, 1 ∂ν := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem (hshellmeas n)] with x hx
            refine ENNReal.ofReal_le_one.mpr (abs_le.mpr ⟨hx.1, ?_⟩)
            linarith [hx.2, hδ]
        _ = ν (shell n) := by
            rw [setLIntegral_one]
    exact lt_of_le_of_lt hle (hshellfin n)
  have hIntOn : IntegrableOn (fun x : ℝ => |x|) (shell n) ν := by
    refine Integrable.mono' (integrableOn_const (C := (1 : ℝ)) (hshellfin n).ne)
      measurable_abs.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (hshellmeas n)] with x hx
    rw [Real.norm_eq_abs, abs_abs]
    refine abs_le.mpr ⟨hx.1, ?_⟩
    linarith [hx.2, hδ]
  have hIR : R ≤ ∫ x in shell n, |x| ∂ν := by
    have h1 : ∫ x in shell n, |x| ∂ν = (W (shell n)).toReal := by
      rw [hW, withDensity_apply _ (hshellmeas n),
        integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun x => abs_nonneg x)
          measurable_abs.aestronglyMeasurable.restrict]
    rw [h1]
    have h2 := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
      hWfin.ne).mpr hn.le
    rwa [ENNReal.toReal_ofReal hR0] at h2
  set I : ℝ := ∫ x in shell n, |x| ∂ν with hIdef
  -- go far enough in m that the exponential factor is ≤ 1/2
  have hexp : Tendsto (fun m : ℕ => Real.exp (-((m * k) * δ))) atTop (𝓝 0) := by
    have h := tendsto_exp_lattice_neg (x := -δ) hk (by linarith)
    refine h.congr fun m => ?_
    congr 1
    ring
  have hev2 : ∀ᶠ m : ℕ in atTop, Real.exp (-((m * k) * δ)) < 1 / 2 :=
    hexp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hev2] with m hm
  -- on the shell: g_{mk} ≥ (1 − e^{−mkδ})·k·|x| ≥ (k/2)|x|
  have hpm : (0 : ℝ) ≤ m * k := by positivity
  have hpoint : ∀ x ∈ shell n,
      ((1 - Real.exp (-((m * k) * δ))) * k) * |x| ≤ gIntegrand k (m * k) x := by
    intro x hx
    have h := gIntegrand_ge_shell_neg hk hpm hδ hx.1 hx.2
    calc ((1 - Real.exp (-((m * k) * δ))) * k) * |x|
        = (1 - Real.exp (-((m * k) * δ))) * (k * |x|) := by ring
      _ ≤ _ := h
  have hconstint : IntegrableOn
      (fun x : ℝ => ((1 - Real.exp (-((m * k) * δ))) * k) * |x|) (shell n) ν :=
    hIntOn.const_mul _
  have hmono2 : ((1 - Real.exp (-((m * k) * δ))) * k) * I
      ≤ ∫ x in shell n, gIntegrand k (m * k) x ∂ν := by
    have h1 : ∫ x in shell n, ((1 - Real.exp (-((m * k) * δ))) * k) * |x| ∂ν
        = ((1 - Real.exp (-((m * k) * δ))) * k) * I := by
      rw [hIdef, integral_const_mul]
    rw [← h1]
    exact setIntegral_mono_on hconstint ((hgint _ hpm).integrableOn)
      (hshellmeas n) hpoint
  have hassemble := setIntegral_g_sub_le hk hpm (hgint _ hpm) hfar
    (hshellsub n)
  have hE : (1 : ℝ) / 2 ≤ 1 - Real.exp (-((m * k) * δ)) := by linarith
  have hI0 : 0 ≤ I := le_trans hR0 hIR
  have hkI0 : 0 ≤ k * I := mul_nonneg hk.le hI0
  have h12 : (1 / 2) * (k * I)
      ≤ (1 - Real.exp (-((m * k) * δ))) * (k * I) :=
    mul_le_mul_of_nonneg_right hE hkI0
  have hkR : k * (2 * (b - a * k + c) / k) ≤ k * R :=
    mul_le_mul_of_nonneg_left hR1 hk.le
  have hkI : k * (2 * (b - a * k + c) / k) = 2 * (b - a * k + c) := by
    field_simp
  have hkIR : k * R ≤ k * I := mul_le_mul_of_nonneg_left hIR hk.le
  have hσterm : 0 ≤ σ2 * k * ((m * k : ℝ) + k / 2) := by positivity
  unfold lkPhi
  nlinarith [hmono2, hassemble, h12, hkR, hkI, hkIR, hσterm]

/-! ## Step 0: A1 keeps the lattice sequence bounded -/

/-- Exact A1 bounds the lattice sequence (closed form of Lemma 1). -/
lemma le_of_satisfiesA1 (φseq : ℕ → ℝ) (β L : ℝ)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hA1 : SatisfiesA1 φseq β L) :
    ∀ m, φseq m ≤ |L| + |φseq 0 - L| := by
  intro m
  have h := delta_closed_form φseq β L hA1 m
  have hβm : |β ^ m| ≤ 1 := by
    rw [abs_pow]
    refine pow_le_one₀ (abs_nonneg β) ?_
    rw [abs_of_pos hβ.1]
    exact hβ.2.le
  have h1 : φseq m = L + β ^ m * (φseq 0 - L) := by linarith
  have h2 : β ^ m * (φseq 0 - L) ≤ |β ^ m * (φseq 0 - L)| := le_abs_self _
  have h3 : |β ^ m * (φseq 0 - L)| ≤ |φseq 0 - L| := by
    rw [abs_mul]
    nlinarith [abs_nonneg (φseq 0 - L)]
  have h4 : L ≤ |L| := le_abs_self L
  linarith

/-- Approximate A1 bounds the lattice sequence (Theorem 10, Step 0:
the recurrence is a contraction, so errors accumulate geometrically). -/
lemma abs_le_of_approx_A1 (φseq : ℕ → ℝ) (β L ε : ℝ)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hres : ∀ m : ℕ, |φseq (m + 1) - (1 - β) * L - β * φseq m| ≤ ε) :
    ∀ m, |φseq m| ≤ max |φseq 0| (((1 - β) * |L| + ε) / (1 - β)) := by
  set C := max |φseq 0| (((1 - β) * |L| + ε) / (1 - β)) with hC
  have h1β : 0 < 1 - β := by linarith [hβ.2]
  have hC2 : ((1 - β) * |L| + ε) / (1 - β) ≤ C := le_max_right _ _
  have hkey : (1 - β) * |L| + ε ≤ (1 - β) * C := by
    rw [div_le_iff₀ h1β] at hC2
    nlinarith
  intro m
  induction m with
  | zero => exact le_max_left _ _
  | succ n ih =>
    have h := hres n
    have h2 : |φseq (n + 1)|
        ≤ |φseq (n + 1) - (1 - β) * L - β * φseq n|
          + |(1 - β) * L + β * φseq n| := by
      have heq : φseq (n + 1)
          = (φseq (n + 1) - (1 - β) * L - β * φseq n)
            + ((1 - β) * L + β * φseq n) := by ring
      calc |φseq (n + 1)|
          = |(φseq (n + 1) - (1 - β) * L - β * φseq n)
              + ((1 - β) * L + β * φseq n)| := by rw [← heq]
        _ ≤ _ := abs_add_le _ _
    have h3 : |(1 - β) * L + β * φseq n|
        ≤ (1 - β) * |L| + β * |φseq n| := by
      calc |(1 - β) * L + β * φseq n|
          ≤ |(1 - β) * L| + |β * φseq n| := abs_add_le _ _
        _ = (1 - β) * |L| + β * |φseq n| := by
            rw [abs_mul, abs_mul, abs_of_pos h1β, abs_of_pos hβ.1]
    have h4 : β * |φseq n| ≤ β * C := mul_le_mul_of_nonneg_left ih hβ.1.le
    have : |φseq (n + 1)| ≤ ε + (1 - β) * |L| + β * C := by linarith
    linarith

/-- A sequence with an upper bound does not tend to `+∞`. -/
lemma not_tendsto_atTop_of_le {f : ℕ → ℝ} {C : ℝ}
    (hbd : ∀ m, f m ≤ C) : ¬ Tendsto f atTop atTop := by
  intro h
  obtain ⟨m, hm⟩ := (h.eventually_ge_atTop (C + 1)).exists
  linarith [hbd m]

/-- **Theorem 10, Step 0 (structural conclusions)**: if the lattice
cumulant increments stay bounded above — as exact or approximate A1
forces — then `σ² = 0`, the Lévy measure has no positive jumps, and the
compensator region is integrable.  None of the divergence steps used the
exact form of A1: only boundedness enters. -/
theorem step0_conclusions {ν : Measure ℝ} {a σ2 k : ℝ}
    (hk : 0 < k) (hσ2 : 0 ≤ σ2)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν)
    {C : ℝ} (hbdd : ∀ m : ℕ, lkPhi a σ2 ν k (m * k) ≤ C) :
    σ2 = 0 ∧ ν (Set.Ioi (0 : ℝ)) = 0
      ∧ (∫⁻ x in Set.Ico (-1 : ℝ) 0, ENNReal.ofReal |x| ∂ν) ≠ ⊤ := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hσ
    exact not_tendsto_atTop_of_le hbdd
      (tendsto_lkPhi_atTop_of_sigma_pos hk
        (lt_of_le_of_ne hσ2 (Ne.symm hσ)) hgint)
  · by_contra hν
    exact not_tendsto_atTop_of_le hbdd
      (tendsto_lkPhi_atTop_of_pos_jumps hk hσ2 hgint hν)
  · by_contra hcomp
    exact not_tendsto_atTop_of_le hbdd
      (tendsto_lkPhi_atTop_of_compensator_infinite hk hσ2 hgint hcomp)

/-! ## The split form (legitimate only after Step 3½) -/

/-- The split constant
`c₀ = ak − k·∫_{(−∞,0)} x·1_{|x|≤1} dν` — in the paper's normalization
this is `δ_∞ · ln r`. -/
noncomputable def lkC0 (a : ℝ) (ν : Measure ℝ) (k : ℝ) : ℝ :=
  a * k - k * ∫ x in Set.Iio (0 : ℝ), lkCompensator x ∂ν

/-- `|x|` is integrable on the compensator region once Step 3½ holds. -/
lemma integrableOn_abs_Ico {ν : Measure ℝ}
    (hcomp : (∫⁻ x in Set.Ico (-1 : ℝ) 0, ENNReal.ofReal |x| ∂ν) ≠ ⊤) :
    IntegrableOn (fun x : ℝ => |x|) (Set.Ico (-1 : ℝ) 0) ν := by
  refine ⟨measurable_abs.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ x in Set.Ico (-1 : ℝ) 0, ‖|x|‖ₑ ∂ν
      = ∫⁻ x in Set.Ico (-1 : ℝ) 0, ENNReal.ofReal |x| ∂ν := by
        refine lintegral_congr fun x => ?_
        rw [Real.enorm_eq_ofReal_abs, abs_abs]
    _ < ⊤ := lt_top_iff_ne_top.mpr hcomp

/-- The truncation is integrable on `(−∞,0)` once Step 3½ holds
(it vanishes below `−1`). -/
lemma integrableOn_lkCompensator {ν : Measure ℝ}
    (hcomp : (∫⁻ x in Set.Ico (-1 : ℝ) 0, ENNReal.ofReal |x| ∂ν) ≠ ⊤) :
    IntegrableOn lkCompensator (Set.Iio (0 : ℝ)) ν := by
  rw [show Set.Iio (0 : ℝ) = Set.Iio (-1 : ℝ) ∪ Set.Ico (-1 : ℝ) 0 from
    (Set.Iio_union_Ico_eq_Iio (by norm_num)).symm]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_congr_fun (g := fun _ => (0 : ℝ)) ?_
      measurableSet_Iio).mpr (integrableOn_zero)
    intro x hx
    exact lkCompensator_of_notMem (by
      intro hmem
      exact absurd hmem.1 (not_le.mpr hx))
  · refine (integrableOn_abs_Ico hcomp).mono' ?_ ?_
    · exact measurable_lkCompensator.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
      rw [Real.norm_eq_abs, lkCompensator_of_mem ⟨hx.1, by linarith [hx.2]⟩]

/-- The pure exponential part `e^{px}(e^{kx}−1)` is integrable on
`(−∞,0)` once Step 3½ holds: dominated by `1` below `−1` and by `k|x|`
on `[−1,0)`. -/
lemma integrableOn_expPart {ν : Measure ℝ} {k p : ℝ} (hk : 0 < k)
    (hp : 0 ≤ p) (hfar : ν (Set.Iio (-1 : ℝ)) < ⊤)
    (hcomp : (∫⁻ x in Set.Ico (-1 : ℝ) 0, ENNReal.ofReal |x| ∂ν) ≠ ⊤) :
    IntegrableOn (fun x : ℝ => Real.exp (p * x) * (Real.exp (k * x) - 1))
      (Set.Iio (0 : ℝ)) ν := by
  have hcont : Continuous
      (fun x : ℝ => Real.exp (p * x) * (Real.exp (k * x) - 1)) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
        continuous_const))
  have hbound : ∀ x : ℝ, x < 0 →
      ‖Real.exp (p * x) * (Real.exp (k * x) - 1)‖ ≤ min 1 (k * |x|) := by
    intro x hx
    have hpx : Real.exp (p * x) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (show p * x ≤ 0 by nlinarith)
      rwa [Real.exp_zero] at h
    have hkx : Real.exp (k * x) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (show k * x ≤ 0 by nlinarith)
      rwa [Real.exp_zero] at h
    have hkx2 : 1 - Real.exp (k * x) ≤ k * |x| := by
      have := le_exp_sub_one (k * x)
      rw [abs_of_neg hx]
      nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonpos (by linarith : Real.exp (k * x) - 1 ≤ 0)]
    refine le_min ?_ ?_
    · nlinarith [Real.exp_pos (p * x), Real.exp_pos (k * x)]
    · nlinarith [Real.exp_pos (p * x), hkx2,
        (Real.exp_pos (p * x)).le, abs_nonneg x]
  rw [show Set.Iio (0 : ℝ) = Set.Iio (-1 : ℝ) ∪ Set.Ico (-1 : ℝ) 0 from
    (Set.Iio_union_Ico_eq_Iio (by norm_num)).symm]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono'
      (integrableOn_const (C := (1 : ℝ)) hfar.ne)
      hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    exact le_trans (hbound x (by linarith [Set.mem_Iio.mp hx]))
      (min_le_left _ _)
  · refine Integrable.mono'
      ((integrableOn_abs_Ico hcomp).const_mul k)
      hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    exact le_trans (hbound x hx.2) (min_le_right _ _)

/-- The integrand vanishes at the origin. -/
lemma gIntegrand_zero (k p : ℝ) : gIntegrand k p 0 = 0 := by
  unfold gIntegrand
  rw [lkCompensator_of_mem (by constructor <;> norm_num)]
  simp

/-- **The split form** (Theorem 7, Step 3½, final display): once
`σ² = 0`, no positive jumps, and the compensator region is integrable,
`φ(p) = c₀ + ∫_{(−∞,0)} e^{px}(e^{kx}−1) dν`. -/
theorem lkPhi_split {ν : Measure ℝ} {a σ2 k : ℝ} (hk : 0 < k)
    {p : ℝ} (hp : 0 ≤ p)
    (hgint : Integrable (gIntegrand k p) ν)
    (hσ0 : σ2 = 0) (hjump : ν (Set.Ioi (0 : ℝ)) = 0)
    (hfar : ν (Set.Iio (-1 : ℝ)) < ⊤)
    (hcomp : (∫⁻ x in Set.Ico (-1 : ℝ) 0, ENNReal.ofReal |x| ∂ν) ≠ ⊤) :
    lkPhi a σ2 ν k p
      = lkC0 a ν k
        + ∫ x in Set.Iio (0 : ℝ),
            Real.exp (p * x) * (Real.exp (k * x) - 1) ∂ν := by
  unfold lkPhi lkC0
  rw [hσ0]
  have hzero : ∫ x in Set.Ici (0 : ℝ), gIntegrand k p x ∂ν = 0 := by
    have hae : Set.Ici (0 : ℝ) =ᵐ[ν] ({0} : Set ℝ) := by
      rw [ae_eq_set]
      constructor
      · rw [show Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 by
          ext x
          simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff,
            Set.mem_Ioi]
          constructor
          · rintro ⟨h1, h2⟩
            exact lt_of_le_of_ne h1 (Ne.symm h2)
          · intro h
            exact ⟨h.le, ne_of_gt h⟩]
        exact hjump
      · rw [show ({0} : Set ℝ) \ Set.Ici 0 = ∅ by
          ext x
          simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_Ici,
            Set.mem_empty_iff_false, iff_false, not_and, not_not]
          rintro rfl
          exact le_rfl]
        exact measure_empty
    rw [setIntegral_congr_set hae,
      setIntegral_congr_fun (g := fun _ => (0 : ℝ))
        (measurableSet_singleton 0)
        (fun x hx => by
          rw [Set.mem_singleton_iff.mp hx]
          exact gIntegrand_zero k p)]
    simp
  have hsplit : ∫ x, gIntegrand k p x ∂ν
      = ∫ x in Set.Iio (0 : ℝ), gIntegrand k p x ∂ν := by
    have h := setIntegral_union (Set.Iio_disjoint_Ici (le_refl (0 : ℝ)))
      measurableSet_Ici hgint.integrableOn hgint.integrableOn
    rw [Set.Iio_union_Ici, setIntegral_univ] at h
    rw [h, hzero, add_zero]
  have hgdiff : ∫ x in Set.Iio (0 : ℝ), gIntegrand k p x ∂ν
      = (∫ x in Set.Iio (0 : ℝ),
          Real.exp (p * x) * (Real.exp (k * x) - 1) ∂ν)
        - k * ∫ x in Set.Iio (0 : ℝ), lkCompensator x ∂ν := by
    have heq : ∀ x : ℝ, gIntegrand k p x
        = Real.exp (p * x) * (Real.exp (k * x) - 1)
          - k * lkCompensator x := fun x => rfl
    rw [show (fun x => gIntegrand k p x)
        = fun x => Real.exp (p * x) * (Real.exp (k * x) - 1)
            - k * lkCompensator x from funext heq]
    rw [integral_sub (integrableOn_expPart hk hp hfar hcomp)
      ((integrableOn_lkCompensator hcomp).const_mul k),
      integral_const_mul]
  rw [hsplit, hgdiff]
  ring

/-- **The lattice limit**: `φ(mk) → c₀` (dominated convergence on the
split form) — this identifies the paper's `δ_∞` as `c₀ / ln r`. -/
theorem tendsto_lkPhi_c0 {ν : Measure ℝ} {a σ2 k : ℝ} (hk : 0 < k)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν)
    (hσ0 : σ2 = 0) (hjump : ν (Set.Ioi (0 : ℝ)) = 0)
    (hfar : ν (Set.Iio (-1 : ℝ)) < ⊤)
    (hcomp : (∫⁻ x in Set.Ico (-1 : ℝ) 0, ENNReal.ofReal |x| ∂ν) ≠ ⊤) :
    Tendsto (fun m : ℕ => lkPhi a σ2 ν k (m * k)) atTop (𝓝 (lkC0 a ν k)) := by
  have hrw : ∀ m : ℕ, lkPhi a σ2 ν k (m * k)
      = lkC0 a ν k
        + ∫ x in Set.Iio (0 : ℝ),
            Real.exp ((m * k) * x) * (Real.exp (k * x) - 1) ∂ν := fun m =>
    lkPhi_split hk (by positivity) (hgint _ (by positivity)) hσ0 hjump
      hfar hcomp
  have hDCT : Tendsto
      (fun m : ℕ => ∫ x in Set.Iio (0 : ℝ),
        Real.exp ((m * k) * x) * (Real.exp (k * x) - 1) ∂ν)
      atTop (𝓝 0) := by
    have key := tendsto_integral_of_dominated_convergence
      (μ := ν.restrict (Set.Iio (0 : ℝ)))
      (F := fun (m : ℕ) (x : ℝ) =>
        Real.exp ((m * k) * x) * (Real.exp (k * x) - 1))
      (f := fun _ => (0 : ℝ))
      (fun x => min 1 (k * |x|)) ?_ ?_ ?_ ?_
    · simpa using key
    · intro m
      exact (((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul
        ((Real.continuous_exp.comp
          (continuous_const.mul continuous_id)).sub
          continuous_const))).aestronglyMeasurable.restrict
    · -- the bound is integrable on (−∞,0)
      rw [show Set.Iio (0 : ℝ) = Set.Iio (-1 : ℝ) ∪ Set.Ico (-1 : ℝ) 0 from
        (Set.Iio_union_Ico_eq_Iio (by norm_num)).symm]
      refine IntegrableOn.union ?_ ?_
      · refine Integrable.mono'
          (integrableOn_const (C := (1 : ℝ)) hfar.ne)
          ((continuous_const.min
            (continuous_const.mul continuous_abs)).aestronglyMeasurable.restrict) ?_
        refine Filter.Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (by positivity))]
        exact min_le_left _ _
      · refine Integrable.mono'
          ((integrableOn_abs_Ico hcomp).const_mul k)
          ((continuous_const.min
            (continuous_const.mul continuous_abs)).aestronglyMeasurable.restrict) ?_
        refine Filter.Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (by positivity))]
        exact min_le_right _ _
    · intro m
      filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
      have hx0 : x < 0 := Set.mem_Iio.mp hx
      have hpx : Real.exp ((m * k) * x) ≤ 1 := by
        have h := Real.exp_le_exp.mpr
          (show (m * k : ℝ) * x ≤ 0 by
            nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) hk.le])
        rwa [Real.exp_zero] at h
      have hkx : Real.exp (k * x) ≤ 1 := by
        have h := Real.exp_le_exp.mpr (show k * x ≤ 0 by nlinarith)
        rwa [Real.exp_zero] at h
      have hkx2 : 1 - Real.exp (k * x) ≤ k * |x| := by
        have := le_exp_sub_one (k * x)
        rw [abs_of_neg hx0]
        nlinarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_nonpos (by linarith : Real.exp (k * x) - 1 ≤ 0)]
      refine le_min ?_ ?_
      · nlinarith [Real.exp_pos ((m * k : ℝ) * x), Real.exp_pos (k * x)]
      · nlinarith [Real.exp_pos ((m * k : ℝ) * x),
          (Real.exp_pos ((m * k : ℝ) * x)).le, abs_nonneg x]
    · filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
      have hx0 : x < 0 := Set.mem_Iio.mp hx
      have hlim : Tendsto (fun m : ℕ => Real.exp ((m * k) * x)) atTop (𝓝 0) :=
        tendsto_exp_lattice_neg hk hx0
      have := hlim.mul_const (Real.exp (k * x) - 1)
      simpa using this
  have := hDCT.const_add (lkC0 a ν k)
  simp only [add_zero] at this
  exact this.congr fun m => (hrw m).symm

/-! ## The tilted measure and its moment dictionary (Theorem 7, Step 4) -/

/-- The tilted measure `η = (1−u)·d(image of ν|_{(−∞,0)} under e^{kx})`
of Theorem 7, Step 4: the compactifying substitution `u = e^{kx}` maps
the negative axis into `(0,1)`, and the tilt `1−u` converts the lattice
deviations into moments. -/
noncomputable def tiltedMeasure (ν : Measure ℝ) (k : ℝ) : Measure ℝ :=
  ((ν.restrict (Set.Iio (0 : ℝ))).map fun x => Real.exp (k * x)).withDensity
    fun u => ENNReal.ofReal (1 - u)

lemma measurable_expMap (k : ℝ) : Measurable fun x : ℝ => Real.exp (k * x) :=
  Real.measurable_exp.comp (measurable_const_mul k)

/-- The base image measure lives on `(0,1)`. -/
lemma ae_map_mem_Ioo {ν : Measure ℝ} {k : ℝ} (hk : 0 < k) :
    ∀ᵐ u ∂((ν.restrict (Set.Iio (0 : ℝ))).map fun x => Real.exp (k * x)),
      u ∈ Set.Ioo (0 : ℝ) 1 := by
  refine (MeasureTheory.ae_map_iff (measurable_expMap k).aemeasurable ?_).mpr ?_
  · exact measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    have hx0 : x < 0 := Set.mem_Iio.mp hx
    refine ⟨Real.exp_pos _, ?_⟩
    have h := Real.exp_lt_exp.mpr (show k * x < 0 by nlinarith)
    rwa [Real.exp_zero] at h

/-- The tilted measure is concentrated on `[0,1]` — the support
hypothesis consumed by `Dirac.lean` and `Stability.lean`. -/
theorem tiltedMeasure_ae_Icc {ν : Measure ℝ} {k : ℝ} (hk : 0 < k) :
    ∀ᵐ u ∂(tiltedMeasure ν k), u ∈ Set.Icc (0 : ℝ) 1 := by
  have hac : tiltedMeasure ν k
      ≪ (ν.restrict (Set.Iio (0 : ℝ))).map fun x => Real.exp (k * x) :=
    withDensity_absolutelyContinuous _ _
  exact Filter.Eventually.filter_mono hac.ae_le
    ((ae_map_mem_Ioo hk).mono fun u hu => ⟨hu.1.le, hu.2.le⟩)

/-- The tilted measure has finite total mass once Step 3½ holds. -/
theorem isFiniteMeasure_tiltedMeasure {ν : Measure ℝ} {k : ℝ} (hk : 0 < k)
    (hfar : ν (Set.Iio (-1 : ℝ)) < ⊤)
    (hcomp : (∫⁻ x in Set.Ico (-1 : ℝ) 0, ENNReal.ofReal |x| ∂ν) ≠ ⊤) :
    IsFiniteMeasure (tiltedMeasure ν k) := by
  constructor
  unfold tiltedMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_map
      (show Measurable fun u : ℝ => ENNReal.ofReal (1 - u) from
        (measurable_const.sub measurable_id).ennreal_ofReal)
      (measurable_expMap k)]
  calc ∫⁻ x, ENNReal.ofReal (1 - Real.exp (k * x))
        ∂(ν.restrict (Set.Iio (0 : ℝ)))
      = (∫⁻ x in Set.Iio (-1 : ℝ),
          ENNReal.ofReal (1 - Real.exp (k * x)) ∂ν)
        + ∫⁻ x in Set.Ico (-1 : ℝ) 0,
            ENNReal.ofReal (1 - Real.exp (k * x)) ∂ν := by
        rw [show (∫⁻ x, ENNReal.ofReal (1 - Real.exp (k * x))
            ∂(ν.restrict (Set.Iio (0 : ℝ))))
          = ∫⁻ x in Set.Iio (0 : ℝ),
              ENNReal.ofReal (1 - Real.exp (k * x)) ∂ν from rfl,
          show Set.Iio (0 : ℝ) = Set.Iio (-1 : ℝ) ∪ Set.Ico (-1 : ℝ) 0 from
            (Set.Iio_union_Ico_eq_Iio (by norm_num)).symm,
          lintegral_union measurableSet_Ico
            (show Disjoint (Set.Iio (-1 : ℝ)) (Set.Ico (-1 : ℝ) 0) from
              Set.disjoint_left.mpr fun x hx hx2 =>
                absurd hx2.1 (not_le.mpr hx))]
    _ ≤ ν (Set.Iio (-1 : ℝ))
        + ENNReal.ofReal k * ∫⁻ x in Set.Ico (-1 : ℝ) 0,
            ENNReal.ofReal |x| ∂ν := by
        refine add_le_add ?_ ?_
        · calc ∫⁻ x in Set.Iio (-1 : ℝ),
              ENNReal.ofReal (1 - Real.exp (k * x)) ∂ν
              ≤ ∫⁻ _x in Set.Iio (-1 : ℝ), 1 ∂ν := by
                refine lintegral_mono fun x => ?_
                refine ENNReal.ofReal_le_one.mpr ?_
                linarith [Real.exp_pos (k * x)]
            _ = ν (Set.Iio (-1 : ℝ)) := by rw [setLIntegral_one]
        · rw [← lintegral_const_mul _ measurable_abs.ennreal_ofReal]
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
          rw [← ENNReal.ofReal_mul hk.le]
          refine ENNReal.ofReal_le_ofReal ?_
          have hx0 : x < 0 := hx.2
          have := le_exp_sub_one (k * x)
          rw [abs_of_neg hx0]
          nlinarith
    _ < ⊤ := by
        refine ENNReal.add_lt_top.mpr ⟨hfar, ?_⟩
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lt_top_iff_ne_top.mpr hcomp)

/-- **The moment dictionary** (Theorem 7, Step 4; Theorem 10, Step 1):
`∫ u^m dη = c₀ − φ(mk)` — the moments of the tilted measure are exactly
the deviations of the lattice cumulant increments from their limit. -/
theorem integral_pow_tiltedMeasure {ν : Measure ℝ} {a σ2 k : ℝ}
    (hk : 0 < k) (hσ0 : σ2 = 0) (hjump : ν (Set.Ioi (0 : ℝ)) = 0)
    (hfar : ν (Set.Iio (-1 : ℝ)) < ⊤)
    (hcomp : (∫⁻ x in Set.Ico (-1 : ℝ) 0, ENNReal.ofReal |x| ∂ν) ≠ ⊤)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν) (m : ℕ) :
    ∫ u, u ^ m ∂(tiltedMeasure ν k)
      = lkC0 a ν k - lkPhi a σ2 ν k (m * k) := by
  have hpm : (0 : ℝ) ≤ (m : ℝ) * k := by positivity
  have hB : lkC0 a ν k - lkPhi a σ2 ν k (m * k)
      = ∫ x in Set.Iio (0 : ℝ),
          (1 - Real.exp (k * x)) * Real.exp (k * x) ^ m ∂ν := by
    rw [lkPhi_split (p := (m : ℝ) * k) hk hpm (hgint _ hpm) hσ0 hjump
      hfar hcomp]
    rw [show lkC0 a ν k - (lkC0 a ν k
          + ∫ x in Set.Iio (0 : ℝ),
              Real.exp ((m * k) * x) * (Real.exp (k * x) - 1) ∂ν)
        = -(∫ x in Set.Iio (0 : ℝ),
              Real.exp ((m * k) * x) * (Real.exp (k * x) - 1) ∂ν) by ring,
      ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hexp : Real.exp ((m * k : ℝ) * x) = Real.exp (k * x) ^ m := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    show -(Real.exp ((m * k : ℝ) * x) * (Real.exp (k * x) - 1))
        = (1 - Real.exp (k * x)) * Real.exp (k * x) ^ m
    rw [hexp]
    ring
  have hA : ∫ u, u ^ m ∂(tiltedMeasure ν k)
      = ∫ x in Set.Iio (0 : ℝ),
          (1 - Real.exp (k * x)) * Real.exp (k * x) ^ m ∂ν := by
    unfold tiltedMeasure
    rw [integral_withDensity_eq_integral_toReal_smul
      (show Measurable fun u : ℝ => ENNReal.ofReal (1 - u) from
        (measurable_const.sub measurable_id).ennreal_ofReal)
      (Filter.Eventually.of_forall fun u => ENNReal.ofReal_lt_top) _]
    rw [integral_map (measurable_expMap k).aemeasurable
      (show AEStronglyMeasurable
          (fun u : ℝ => (ENNReal.ofReal (1 - u)).toReal • u ^ m)
          ((ν.restrict (Set.Iio (0 : ℝ))).map fun x => Real.exp (k * x)) from
        (((measurable_const.sub measurable_id).ennreal_ofReal.ennreal_toReal).smul
          (measurable_id.pow_const m)).aestronglyMeasurable)]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    have hx0 : x < 0 := Set.mem_Iio.mp hx
    have h1 : (0 : ℝ) ≤ 1 - Real.exp (k * x) := by
      have h := Real.exp_le_exp.mpr (show k * x ≤ 0 by nlinarith)
      rw [Real.exp_zero] at h
      linarith
    rw [ENNReal.toReal_ofReal h1, smul_eq_mul]
  rw [hA, hB]

/-! ## Theorem 7, forward direction -/

/-- **Theorem 7 (Log-ID Classification), forward direction**, at the
level of the tilted measure: exact A1 on the lattice cumulant increments
with `β ∈ (0,1)` forces `σ² = 0`, no positive jumps, an integrable
compensator region, and `η = (Lφ − φ(0))·δ_β` — the geometric rigidity
of Step 4.  Inverting the tilt identifies the Lévy measure as a single
atom: the generator is log-Poisson. -/
theorem theorem7_forward_eta {ν : Measure ℝ} {a σ2 k β Lφ : ℝ}
    (hk : 0 < k) (hσ2 : 0 ≤ σ2) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν)
    (hA1 : SatisfiesA1 (fun m => lkPhi a σ2 ν k (m * k)) β Lφ) :
    σ2 = 0 ∧ ν (Set.Ioi (0 : ℝ)) = 0
      ∧ (∫⁻ x in Set.Ico (-1 : ℝ) 0, ENNReal.ofReal |x| ∂ν) ≠ ⊤
      ∧ tiltedMeasure ν k
          = ENNReal.ofReal (Lφ - lkPhi a σ2 ν k 0) • Measure.dirac β := by
  obtain ⟨hσ0, hjump, hcomp⟩ := step0_conclusions hk hσ2 hgint
    (le_of_satisfiesA1 _ β Lφ hβ hA1)
  have hfar := nu_Iio_lt_top hk (hgint 0 le_rfl)
  have hLc0 : Lφ = lkC0 a ν k := by
    have h1 := tendsto_delta _ β Lφ hβ.1.le hβ.2 hA1
    have h2 := tendsto_lkPhi_c0 (a := a) (σ2 := σ2) hk hgint hσ0 hjump
      hfar hcomp
    exact tendsto_nhds_unique h1 h2
  haveI := isFiniteMeasure_tiltedMeasure hk hfar hcomp
  refine ⟨hσ0, hjump, hcomp, ?_⟩
  refine eq_dirac_of_geometric_moments (tiltedMeasure_ae_Icc hk) ?_
  intro m _
  rw [integral_pow_tiltedMeasure hk hσ0 hjump hfar hcomp hgint m, ← hLc0]
  have hcf := delta_closed_form _ β Lφ hA1 m
  simp only [Nat.cast_zero, zero_mul] at hcf
  linear_combination (-1 : ℝ) * hcf

/-! ## Theorem 10, Step 0 (packaged for the stability theory) -/

/-- **Theorem 10, Steps 0–1 (packaged)**: under *approximate* A1 on the
lattice cumulant increments — residuals bounded by `ε` against a fitted
constant `Lφ` — the structural conclusions hold, the limit
`c₀ = lim φ(mk)` exists, the fitted constant is `ε`-close to it
(`(1−β)·|Lφ − c₀| ≤ ε`, Step 0's display), and the tilted measure
realizes the exact moment dictionary `∫ u^m dη = c₀ − φ(mk)` — exactly
the hypotheses consumed by the variance and Wasserstein estimates of
`Freeburg.Stability`. -/
theorem theorem10_step0 {ν : Measure ℝ} {a σ2 k β Lφ ε : ℝ}
    (hk : 0 < k) (hσ2 : 0 ≤ σ2) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν)
    (hres : ∀ m : ℕ, |lkPhi a σ2 ν k ((m + 1 : ℕ) * k)
      - (1 - β) * Lφ - β * lkPhi a σ2 ν k (m * k)| ≤ ε) :
    σ2 = 0 ∧ ν (Set.Ioi (0 : ℝ)) = 0
      ∧ (∫⁻ x in Set.Ico (-1 : ℝ) 0, ENNReal.ofReal |x| ∂ν) ≠ ⊤
      ∧ Tendsto (fun m : ℕ => lkPhi a σ2 ν k (m * k)) atTop
          (𝓝 (lkC0 a ν k))
      ∧ (1 - β) * |Lφ - lkC0 a ν k| ≤ ε
      ∧ ∀ m : ℕ, ∫ u, u ^ m ∂(tiltedMeasure ν k)
          = lkC0 a ν k - lkPhi a σ2 ν k (m * k) := by
  have hbdd' := abs_le_of_approx_A1
    (fun m => lkPhi a σ2 ν k (m * k)) β Lφ ε hβ hres
  have hbdd : ∀ m : ℕ, lkPhi a σ2 ν k (m * k)
      ≤ max |lkPhi a σ2 ν k ((0 : ℕ) * k)|
          (((1 - β) * |Lφ| + ε) / (1 - β)) := fun m =>
    le_trans (le_abs_self _) (hbdd' m)
  obtain ⟨hσ0, hjump, hcomp⟩ := step0_conclusions hk hσ2 hgint hbdd
  have hfar := nu_Iio_lt_top hk (hgint 0 le_rfl)
  have hlim := tendsto_lkPhi_c0 (a := a) (σ2 := σ2) hk hgint hσ0 hjump
    hfar hcomp
  refine ⟨hσ0, hjump, hcomp, hlim, ?_, fun m =>
    integral_pow_tiltedMeasure hk hσ0 hjump hfar hcomp hgint m⟩
  have hlim1 : Tendsto (fun m : ℕ => lkPhi a σ2 ν k ((m + 1 : ℕ) * k))
      atTop (𝓝 (lkC0 a ν k)) := by
    have h := hlim.comp (tendsto_add_atTop_nat 1)
    exact h.congr fun m => by simp [Function.comp]
  have habs : Tendsto (fun m : ℕ =>
      |lkPhi a σ2 ν k ((m + 1 : ℕ) * k)
        - (1 - β) * Lφ - β * lkPhi a σ2 ν k (m * k)|) atTop
      (𝓝 |lkC0 a ν k - (1 - β) * Lφ - β * lkC0 a ν k|) := by
    refine Tendsto.abs ?_
    exact (hlim1.sub_const ((1 - β) * Lφ)).sub (hlim.const_mul β)
  have hle := le_of_tendsto habs
    (Filter.Eventually.of_forall fun m => hres m)
  calc (1 - β) * |Lφ - lkC0 a ν k|
      = |lkC0 a ν k - (1 - β) * Lφ - β * lkC0 a ν k| := by
        rw [show lkC0 a ν k - (1 - β) * Lφ - β * lkC0 a ν k
            = (1 - β) * (lkC0 a ν k - Lφ) by ring, abs_mul,
          abs_of_pos (by linarith [hβ.2] : (0 : ℝ) < 1 - β),
          abs_sub_comm]
    _ ≤ ε := hle

/-! ## The tilt inversion: the Lévy measure is a single atom -/

/-- **Inverting the tilt** (the last line of Theorem 7's proof): if
`η = (1−u)·dν̃ = A·δ_β` with `ν̃` the image measure on `(0,1)` and
`β ∈ (0,1)`, then `ν̃ = (A/(1−β))·δ_β` — because `1−u ≠ 0` on `(0,1)`. -/
theorem map_eq_smul_dirac_of_tilted_eq {ν : Measure ℝ} {k β A : ℝ}
    (hk : 0 < k) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (heta : tiltedMeasure ν k = ENNReal.ofReal A • Measure.dirac β) :
    (ν.restrict (Set.Iio (0 : ℝ))).map (fun x => Real.exp (k * x))
      = ENNReal.ofReal (A / (1 - β)) • Measure.dirac β := by
  set ν' : Measure ℝ :=
    (ν.restrict (Set.Iio (0 : ℝ))).map fun x => Real.exp (k * x) with hν'
  have haeIoo : ∀ᵐ u ∂ν', u ∈ Set.Ioo (0 : ℝ) 1 := ae_map_mem_Ioo hk
  have hβ1 : 0 < 1 - β := by linarith [hβ.2]
  -- off the atom, ν' vanishes (the tilt is positive on (0,1))
  have hcompl : ν' ({β}ᶜ) = 0 := by
    have hη : tiltedMeasure ν k ({β}ᶜ) = 0 := by
      rw [heta, Measure.smul_apply,
        Measure.dirac_apply' _ (measurableSet_singleton β).compl]
      simp
    rw [show tiltedMeasure ν k
        = ν'.withDensity fun u => ENNReal.ofReal (1 - u) from rfl,
      withDensity_apply _ (measurableSet_singleton β).compl] at hη
    have h0 := (lintegral_eq_zero_iff'
      (show AEMeasurable (fun u : ℝ => ENNReal.ofReal (1 - u))
          (ν'.restrict ({β}ᶜ)) from
        ((measurable_const.sub measurable_id).ennreal_ofReal).aemeasurable)).mp
      hη
    have hfalse : ∀ᵐ u ∂(ν'.restrict ({β}ᶜ)), False := by
      filter_upwards [h0, ae_restrict_of_ae haeIoo] with u h1 h2
      simp only [Pi.zero_apply] at h1
      exact absurd h1
        (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith [h2.2])))
    have h2 := ae_iff.mp hfalse
    simp only [not_false_iff, Set.setOf_true] at h2
    rwa [Measure.restrict_apply_univ] at h2
  have hoff : ∀ s : Set ℝ, β ∉ s → ν' s = 0 := by
    intro s hs
    refine measure_mono_null (fun x hx => ?_) hcompl
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact hs hx
  -- the atom mass: (1−β)·ν'{β} = A
  have hatom : ν' {β} = ENNReal.ofReal (A / (1 - β)) := by
    have hη : tiltedMeasure ν k {β} = ENNReal.ofReal A := by
      rw [heta, Measure.smul_apply,
        Measure.dirac_apply' _ (measurableSet_singleton β)]
      simp
    rw [show tiltedMeasure ν k
        = ν'.withDensity fun u => ENNReal.ofReal (1 - u) from rfl,
      withDensity_apply _ (measurableSet_singleton β),
      lintegral_singleton (fun u => ENNReal.ofReal (1 - u)) β] at hη
    rw [ENNReal.ofReal_div_of_pos hβ1]
    exact (ENNReal.eq_div_iff
      (ENNReal.ofReal_pos.mpr hβ1).ne' ENNReal.ofReal_ne_top).mpr hη
  -- assemble the measure equality
  ext s hs
  rw [Measure.smul_apply, Measure.dirac_apply' β hs, smul_eq_mul]
  by_cases hβs : β ∈ s
  · rw [Set.indicator_of_mem hβs, Pi.one_apply, mul_one]
    have hc : ν' sᶜ = 0 := hoff _ (by simp [hβs])
    have huniv : ν' s = ν' Set.univ := by
      have h := measure_add_measure_compl (μ := ν') hs
      rwa [hc, add_zero] at h
    have hsing : ν' {β} = ν' Set.univ := by
      have h := measure_add_measure_compl (μ := ν')
        (measurableSet_singleton β)
      have hc2 : ν' {β}ᶜ = 0 := hoff _ (by simp)
      rwa [hc2, add_zero] at h
    rw [huniv, ← hsing, hatom]
  · rw [Set.indicator_of_notMem hβs, mul_zero]
    exact hoff s hβs

/-- **Theorem 7 (Log-ID Classification), forward direction — the Lévy
measure**: under exact A1 with `β ∈ (0,1)` (and the Lévy convention
`ν{0} = 0`), the Lévy measure is the single atom

  `ν = λ·δ_b`,  `b = ln β / k < 0`,  `λ = (Lφ − φ(0))/(1−β)`.

The generator `log W` is compound Poisson with deterministic jump `b`
and rate `λ`: **the log-Poisson distribution**.  Together with `σ² = 0`
(in `theorem7_forward_eta`) this is the full forward direction. -/
theorem theorem7_forward_nu {ν : Measure ℝ} {a σ2 k β Lφ : ℝ}
    (hk : 0 < k) (hσ2 : 0 ≤ σ2) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hzero : ν ({0} : Set ℝ) = 0)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν)
    (hA1 : SatisfiesA1 (fun m => lkPhi a σ2 ν k (m * k)) β Lφ) :
    ν = ENNReal.ofReal ((Lφ - lkPhi a σ2 ν k 0) / (1 - β))
        • Measure.dirac (Real.log β / k) := by
  obtain ⟨hσ0, hjump, hcomp, heta⟩ :=
    theorem7_forward_eta hk hσ2 hβ hgint hA1
  have hmap := map_eq_smul_dirac_of_tilted_eq hk hβ heta
  -- ν is carried by (−∞,0)
  have hIci : ν (Set.Ici (0 : ℝ)) = 0 := by
    have hsplit : Set.Ici (0 : ℝ) = {0} ∪ Set.Ioi 0 := by
      ext x
      simp only [Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_Ioi]
      constructor
      · intro h
        rcases eq_or_lt_of_le h with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr h'
      · rintro (rfl | h)
        · exact le_rfl
        · exact h.le
    rw [hsplit]
    exact measure_union_null hzero hjump
  have hrestrict : ν = ν.restrict (Set.Iio (0 : ℝ)) := by
    ext s hs
    rw [Measure.restrict_apply hs]
    refine le_antisymm ?_ (measure_mono Set.inter_subset_left)
    calc ν s = ν ((s ∩ Set.Iio 0) ∪ (s ∩ Set.Ici 0)) := by
          rw [← Set.inter_union_distrib_left, Set.Iio_union_Ici,
            Set.inter_univ]
      _ ≤ ν (s ∩ Set.Iio 0) + ν (s ∩ Set.Ici 0) := measure_union_le _ _
      _ = ν (s ∩ Set.Iio 0) := by
          rw [measure_mono_null Set.inter_subset_right hIci, add_zero]
  have hS : Measurable fun u : ℝ => Real.log u / k :=
    Real.measurable_log.div_const k
  calc ν = ν.restrict (Set.Iio (0 : ℝ)) := hrestrict
    _ = ((ν.restrict (Set.Iio (0 : ℝ))).map
          (fun x => Real.exp (k * x))).map (fun u => Real.log u / k) := by
        rw [Measure.map_map hS (measurable_expMap k)]
        rw [show ((fun u : ℝ => Real.log u / k)
            ∘ fun x : ℝ => Real.exp (k * x)) = id from funext fun x => by
          simp only [Function.comp_apply, id_eq, Real.log_exp]
          rw [mul_comm, mul_div_assoc, div_self hk.ne', mul_one]]
        rw [Measure.map_id]
    _ = (ENNReal.ofReal ((Lφ - lkPhi a σ2 ν k 0) / (1 - β))
          • Measure.dirac β).map (fun u => Real.log u / k) := by
        rw [hmap]
    _ = ENNReal.ofReal ((Lφ - lkPhi a σ2 ν k 0) / (1 - β))
          • Measure.dirac (Real.log β / k) := by
        rw [Measure.map_smul, Measure.map_dirac' hS]

/-! ## Theorem 10, assembled: the sharp variance and Wasserstein bounds -/

/-- The moment residuals of the tilted measure coincide (up to sign)
with the A1 residuals of the cumulant increments — Theorem 10, Step 1,
in the form consumed by `Freeburg.Stability`. -/
lemma tilted_residual_bound {ν : Measure ℝ} {a σ2 k β L ε : ℝ}
    (hdict : ∀ m : ℕ, ∫ u, u ^ m ∂(tiltedMeasure ν k)
      = lkC0 a ν k - lkPhi a σ2 ν k (m * k))
    (hres : ∀ m : ℕ, |lkPhi a σ2 ν k ((m + 1 : ℕ) * k)
      - (1 - β) * L - β * lkPhi a σ2 ν k (m * k)| ≤ ε) (m : ℕ) :
    |(∫ u, u ^ (m + 1) ∂(tiltedMeasure ν k))
        - β * (∫ u, u ^ m ∂(tiltedMeasure ν k))
        - (1 - β) * (lkC0 a ν k - L)| ≤ ε := by
  rw [hdict (m + 1), hdict m]
  have h := hres m
  rw [show (lkC0 a ν k - lkPhi a σ2 ν k ((m + 1 : ℕ) * k))
      - β * (lkC0 a ν k - lkPhi a σ2 ν k (m * k))
      - (1 - β) * (lkC0 a ν k - L)
      = -(lkPhi a σ2 ν k ((m + 1 : ℕ) * k)
          - (1 - β) * L - β * lkPhi a σ2 ν k (m * k)) by ring, abs_neg]
  exact h

/-- **Theorem 10 (assembled, reading (i): true limit known)**: if the
A1 residuals are measured against the true limit `c₀`, then
`∫(u−β)² dη ≤ (1+β)·ε` — the sharp constant of the paper. -/
theorem theorem10_variance_known {ν : Measure ℝ} {a σ2 k β ε : ℝ}
    (hk : 0 < k) (hσ2 : 0 ≤ σ2) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν)
    (hres : ∀ m : ℕ, |lkPhi a σ2 ν k ((m + 1 : ℕ) * k)
      - (1 - β) * lkC0 a ν k - β * lkPhi a σ2 ν k (m * k)| ≤ ε) :
    ∫ u, (u - β) ^ 2 ∂(tiltedMeasure ν k) ≤ (1 + β) * ε := by
  obtain ⟨hσ0, hjump, hcomp, _hlim, _ht, hdict⟩ :=
    theorem10_step0 hk hσ2 hβ hgint hres
  haveI := isFiniteMeasure_tiltedMeasure hk
    (nu_Iio_lt_top hk (hgint 0 le_rfl)) hcomp
  refine variance_le_of_residual_bounds β ε hβ.1.le
    (tiltedMeasure_ae_Icc hk) ?_ ?_
  · have h := tilted_residual_bound hdict hres 0
    simpa using h
  · have h := tilted_residual_bound hdict hres 1
    simpa using h

/-- **Theorem 10 (assembled, reading (ii): fitted constant)**: if the
A1 residuals are measured against an arbitrary fitted constant `Lφ`,
then `∫(u−β)² dη ≤ 2·ε` — the sharp fitted constant, via the offset
cancellation `ε₁ − βε₀ = (h₁ − βh₀) + (1−β)t`. -/
theorem theorem10_variance_fitted {ν : Measure ℝ} {a σ2 k β Lφ ε : ℝ}
    (hk : 0 < k) (hσ2 : 0 ≤ σ2) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν)
    (hres : ∀ m : ℕ, |lkPhi a σ2 ν k ((m + 1 : ℕ) * k)
      - (1 - β) * Lφ - β * lkPhi a σ2 ν k (m * k)| ≤ ε) :
    ∫ u, (u - β) ^ 2 ∂(tiltedMeasure ν k) ≤ 2 * ε := by
  obtain ⟨hσ0, hjump, hcomp, _hlim, ht, hdict⟩ :=
    theorem10_step0 hk hσ2 hβ hgint hres
  haveI := isFiniteMeasure_tiltedMeasure hk
    (nu_Iio_lt_top hk (hgint 0 le_rfl)) hcomp
  have htabs : |(1 - β) * (lkC0 a ν k - Lφ)| ≤ ε := by
    rw [abs_mul, abs_of_pos (by linarith [hβ.2] : (0 : ℝ) < 1 - β),
      abs_sub_comm]
    exact ht
  refine variance_le_of_fitted_residual_bounds β ε
    ((1 - β) * (lkC0 a ν k - Lφ)) hβ.1.le hβ.2.le htabs
    (tiltedMeasure_ae_Icc hk) ?_ ?_
  · have h := tilted_residual_bound hdict hres 0
    simpa using h
  · have h := tilted_residual_bound hdict hres 1
    simpa using h

/-- **Theorem 10 (assembled, reading (i), Wasserstein form)**: the
normalized first absolute moment — which for a Dirac target *is*
`W₁(η/‖η‖, δ_β)` — obeys the paper's displayed bound
`≤ √((1+β)·ε/‖η‖)`, with the sharp constant.  (In the paper's
normalization `‖η‖ = |A|` exactly, giving `√((1+β)|ln r|/|A|)·√ε`.) -/
theorem theorem10_wasserstein_known {ν : Measure ℝ} {a σ2 k β ε : ℝ}
    (hk : 0 < k) (hσ2 : 0 ≤ σ2) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand k p) ν)
    (hres : ∀ m : ℕ, |lkPhi a σ2 ν k ((m + 1 : ℕ) * k)
      - (1 - β) * lkC0 a ν k - β * lkPhi a σ2 ν k (m * k)| ≤ ε)
    (hmass : 0 < (tiltedMeasure ν k).real Set.univ) :
    ((tiltedMeasure ν k).real Set.univ)⁻¹
        * ∫ u, |u - β| ∂(tiltedMeasure ν k)
      ≤ Real.sqrt ((1 + β) * ε / (tiltedMeasure ν k).real Set.univ) := by
  obtain ⟨hσ0, hjump, hcomp, _hlim, _ht, hdict⟩ :=
    theorem10_step0 hk hσ2 hβ hgint hres
  haveI := isFiniteMeasure_tiltedMeasure hk
    (nu_Iio_lt_top hk (hgint 0 le_rfl)) hcomp
  refine normalized_abs_moment_le β ε hβ.1.le hmass
    (tiltedMeasure_ae_Icc hk) ?_ ?_
  · have h := tilted_residual_bound hdict hres 0
    simpa using h
  · have h := tilted_residual_bound hdict hres 1
    simpa using h

end Freeburg

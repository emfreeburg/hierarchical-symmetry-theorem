/-
Freeburg formalization — Continuous.lean
Theorem 17 (v3 corrected form) and Theorem 18 (forward, five-moment route) of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632 (v3 draft).
-/
import Freeburg.Basic
import Freeburg.Dirac
import Freeburg.LevyKhintchine

/-!
# Continuous cascades: the finite-window identifiability boundary (§7)

This file formalizes the **corrected (v3) Theorem 17** — "Four orders do not
identify the class; five contiguous orders do" — and the five-moment route to
Theorem 18's forward direction, at the generator (cumulant) level of
`LevyKhintchine.lean`: triplets `(a, σ², ν)` with `ζ_q = q − ψ(q)`,
`ψ = lkPsi`.  Conventions: `k = 1` (as in `Propagation.lean`; general `k` is
the substitution `x ↦ kx`), She–Lévêque curve `ζ^SL_q = γq + C(1−β^q)`.

The engine is the **squared-tilt second difference**: with
`sqIntegrand p x = e^{px}(e^x−1)²` (nonnegative on *both* sides of `x = 0` —
a square, which is what removes every divergence argument),

  `ψ(p+2) − 2ψ(p+1) + ψ(p) = σ² + ∫ sqIntegrand p dν`     (`lkPsi_second_diff`)

while on the She–Lévêque side the same second difference is `A′β^p`,
`A′ = C(1−β)²`.  Matching `ζ` at the five points `{0,1,2,3,4}` pins the three
moments `σ² + r_m = A′β^m` (`m = 0,1,2`), and the test integral
`∫ (e^x−β)²(e^x−1)² dν = r₂ − 2βr₁ + β²r₀ = −σ²(1−β)²` is simultaneously
`≥ 0` and `≤ 0`: hence `σ² = 0`, the test vanishes, and the measure is carried
by `{x : e^x ∈ {β, 1}}`; the Lévy convention `ν{0} = 0` then forces
`ν = C·δ_{ln β}` — the compound Poisson cascade generator.

Main results:

* `Freeburg.lkPsi_second_diff` — the second-difference identity.
* `Freeburg.eq_smul_dirac_of_ae_const` — a measure a.e. equal to a constant
  is a Dirac multiple (the Icc-free endgame of `Dirac.lean`).
* `Freeburg.theorem17_five_point_rigidity` — **Theorem 17(ii)**: exact
  agreement with `ζ^SL` at `q ∈ {0,1,2,3,4}` forces `σ² = 0` and
  `ν = C·δ_{ln β}`.  No divergence steps, no moments beyond `q = 4`,
  and no sign hypothesis on `C` (nonnegativity of `C` is a conclusion).
* `Freeburg.theorem18_forward_fiveMoment` — **Theorem 18, forward (route B
  of the v3 proof)**: lattice A1 consumed only through the closed form of
  Lemma 1 at `m ≤ 4` already forces the CPC — with integrability
  hypotheses strictly weaker than (S_c): only `ψ` finite on the window.
* `Freeburg.theorem17_one_sided` — **Theorem 17(i), one-sidedness**: any
  triplet matching `ζ^SL` on `{0,1,2,3}` has `ζ_4 ≤ ζ^SL_4`, with equality
  iff it *is* the CPC; and (attenuation-only case `ν((0,∞)) = 0`) the
  deficit is at most `A′β(1−β) = Cβ(1−β)³`.
* `Freeburg.nu3`, `Freeburg.theorem17_impersonation_three_point` —
  **Theorem 17(i), the printed three-point family** at
  `(β, C, γ) = (2/3, 2, 1/3)`, exact rationals: for every `s ∈ (0,2]` the
  three-atom generator matches `ζ^SL` on `{0,1,2}` and overshoots `ζ^SL_3`
  by exactly `77s/2700` (at `s = 1/2`: the paper's `+77/5400`); the family
  is injective in `s` (a genuine continuum) and never a single atom.
* `Freeburg.nu4`, `Freeburg.theorem17_impersonation_four_point` —
  **Theorem 17(i), the maximal window**: a two-atom generator matching
  `ζ^SL` on `{0,1,2,3}` exactly, with `ζ_4 − ζ^SL_4 = −34/2025`
  (`≈ −0.01679`, the strict undershoot).

Deviations from the paper, all documented here: `k = 1`; the (M2)
probabilistic layer (existence of the scale-invariant measure `M` for a
given triplet, and the Barral–Mandelbrot identification) stays an
unformalized classical bridge exactly as the Lévy–Khintchine representation
theorem does; "ψ finite on `[0,4k]`" is rendered as integrability of the
five lattice LK integrands (the honest minimal hypothesis — the proofs use
nothing else); the drift is existentially quantified in the impersonation
statements (the paper re-fixes it by (M2) for each family member; any drift
matching `ζ_1` works and the compensator bookkeeping is absorbed by it);
part (i)'s witnesses are at the paper's exhibited parameters
`(β, C) = (2/3, 2)`, and the printed "continuum" is kernel-checked on the
window `{0,1,2}` (`nu3` with `nu3_injOn`) while the maximal window
`{0,1,2,3}` carries a single checked witness (`nu4`) — the continuum there
(moving atom positions) is paper-level.
Everything in this file is sorry-free.
-/

open MeasureTheory
open scoped ENNReal

namespace Freeburg

/-! ## The squared-tilt integrand and the second-difference identity -/

/-- The squared-tilt integrand `e^{px}(e^x − 1)²` — the `Δ²` of the
Lévy–Khintchine integrand family.  Being a square times a positive factor,
it is nonnegative on **both** sides of `x = 0`: amplifying jumps (`x > 0`)
contribute with the same sign as attenuating ones.  This is the v3 proof's
replacement for the divergence steps of Theorem 7. -/
noncomputable def sqIntegrand (p x : ℝ) : ℝ :=
  Real.exp (p * x) * (Real.exp x - 1) ^ 2

lemma sqIntegrand_nonneg (p x : ℝ) : 0 ≤ sqIntegrand p x :=
  mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)

lemma measurable_sqIntegrand (p : ℝ) : Measurable (sqIntegrand p) :=
  (Real.measurable_exp.comp (measurable_const_mul p)).mul
    ((Real.measurable_exp.sub measurable_const).pow_const 2)

/-- `Δ²` of the compensated LK integrand is the squared-tilt integrand:
`f_{p+2} − 2f_{p+1} + f_p = e^{px}(e^x−1)²` — the compensator and the
constant cancel exactly. -/
lemma sqIntegrand_eq_lk (p x : ℝ) :
    sqIntegrand p x
      = lkIntegrand (p + 2) x - 2 * lkIntegrand (p + 1) x + lkIntegrand p x := by
  unfold sqIntegrand lkIntegrand
  rw [show (p + 2) * x = p * x + (x + x) by ring,
    show (p + 1) * x = p * x + x by ring, Real.exp_add, Real.exp_add,
    Real.exp_add]
  ring

/-- Integrability of the squared-tilt integrand from integrability of the
three LK integrands it differences. -/
lemma integrable_sqIntegrand {ν : Measure ℝ} {p : ℝ}
    (h0 : Integrable (lkIntegrand p) ν)
    (h1 : Integrable (lkIntegrand (p + 1)) ν)
    (h2 : Integrable (lkIntegrand (p + 2)) ν) :
    Integrable (sqIntegrand p) ν := by
  have : Integrable
      (fun x => lkIntegrand (p + 2) x - 2 * lkIntegrand (p + 1) x
        + lkIntegrand p x) ν := (h2.sub (h1.const_mul 2)).add h0
  exact this.congr (Filter.Eventually.of_forall fun x =>
    (sqIntegrand_eq_lk p x).symm)

/-- **The second-difference identity** (v3 Theorem 17, proof display
(7.1)): `ψ(p+2) − 2ψ(p+1) + ψ(p) = σ² + ∫ e^{px}(e^x−1)² dν`.
Drift and compensator cancel exactly; the Gaussian term contributes `σ²`. -/
theorem lkPsi_second_diff {ν : Measure ℝ} (a σ2 : ℝ) {p : ℝ}
    (h0 : Integrable (lkIntegrand p) ν)
    (h1 : Integrable (lkIntegrand (p + 1)) ν)
    (h2 : Integrable (lkIntegrand (p + 2)) ν) :
    lkPsi a σ2 ν (p + 2) - 2 * lkPsi a σ2 ν (p + 1) + lkPsi a σ2 ν p
      = σ2 + ∫ x, sqIntegrand p x ∂ν := by
  unfold lkPsi
  have hcongr : ∫ x, sqIntegrand p x ∂ν
      = ∫ x, (lkIntegrand (p + 2) x - 2 * lkIntegrand (p + 1) x
        + lkIntegrand p x) ∂ν :=
    integral_congr_ae (.of_forall fun x => sqIntegrand_eq_lk p x)
  have houter : ∫ x, (lkIntegrand (p + 2) x - 2 * lkIntegrand (p + 1) x
        + lkIntegrand p x) ∂ν
      = (∫ x, (lkIntegrand (p + 2) x - 2 * lkIntegrand (p + 1) x) ∂ν)
        + ∫ x, lkIntegrand p x ∂ν :=
    integral_add (h2.sub (h1.const_mul 2)) h0
  have hinner : ∫ x, (lkIntegrand (p + 2) x - 2 * lkIntegrand (p + 1) x) ∂ν
      = (∫ x, lkIntegrand (p + 2) x ∂ν)
        - ∫ x, 2 * lkIntegrand (p + 1) x ∂ν :=
    integral_sub h2 (h1.const_mul 2)
  have hcm : ∫ x, 2 * lkIntegrand (p + 1) x ∂ν
      = 2 * ∫ x, lkIntegrand (p + 1) x ∂ν :=
    integral_const_mul 2 _
  rw [hcongr, houter, hinner, hcm]
  ring

/-! ## The Icc-free Dirac endgame -/

/-- A measure that is a.e. equal to a constant point, with `ν{pt}`-mass
recorded through the total mass, is a Dirac multiple.  This is the endgame
of `Dirac.eq_dirac_of_geometric_moments` with the `Icc 0 1` support
hypothesis removed — concentration alone suffices. -/
theorem eq_smul_dirac_of_ae_const {ν : Measure ℝ} [IsFiniteMeasure ν]
    {b : ℝ} (hae : ∀ᵐ x ∂ν, x = b) :
    ν = ENNReal.ofReal (ν.real Set.univ) • Measure.dirac b := by
  have hnull : ∀ s : Set ℝ, b ∉ s → ν s = 0 := by
    intro s hbs
    refine measure_mono_null ?_ (ae_iff.mp hae)
    intro x hxs
    simp only [Set.mem_setOf_eq]
    intro hx
    exact hbs (hx ▸ hxs)
  ext s hs
  rw [Measure.smul_apply, Measure.dirac_apply' b hs, smul_eq_mul]
  by_cases hbs : b ∈ s
  · rw [Set.indicator_of_mem hbs, Pi.one_apply, mul_one]
    have hcompl : ν sᶜ = 0 := hnull sᶜ (by simp [hbs])
    have huniv : ν s = ν Set.univ := by
      have h := measure_add_measure_compl (μ := ν) hs
      rwa [hcompl, add_zero] at h
    rw [huniv, Measure.real, ENNReal.ofReal_toReal (measure_ne_top ν _)]
  · rw [Set.indicator_of_notMem hbs, mul_zero]
    exact hnull s hbs

/-! ## Theorem 17(ii): five-point rigidity -/

section Rigidity

variable {ν : Measure ℝ} {a σ2 γ C β : ℝ}

/-- The five-point matching hypothesis, in the paper's `ζ` form:
`ζ_q = q − ψ(q)` agrees with the She–Lévêque curve `γq + C(1−β^q)` at the
lattice points `q = 0, 1, 2, 3, 4`. -/
def MatchesSLUpTo (a σ2 : ℝ) (ν : Measure ℝ) (γ C β : ℝ) (n : ℕ) : Prop :=
  ∀ q : ℕ, q ≤ n → (q : ℝ) - lkPsi a σ2 ν q = γ * q + C * (1 - β ^ q)

/-- From five-point `ζ` matching, the three squared-tilt moments are pinned:
`σ² + ∫ e^{mx}(e^x−1)² dν = C(1−β)² β^m` for `m = 0, 1, 2`. -/
lemma moment_eqs_of_matches
    (hint : ∀ q : ℕ, q ≤ 4 → Integrable (lkIntegrand q) ν)
    (hm : MatchesSLUpTo a σ2 ν γ C β 4) :
    ∀ m : ℕ, m ≤ 2 →
      σ2 + ∫ x, sqIntegrand (m : ℝ) x ∂ν = C * (1 - β) ^ 2 * β ^ m := by
  intro m hm2
  have h0 := hint m (by omega)
  have h1 := hint (m + 1) (by omega)
  have h2 := hint (m + 2) (by omega)
  push_cast at h1 h2
  have hdiff := lkPsi_second_diff (ν := ν) a σ2 (p := (m : ℝ)) h0 h1 h2
  -- rewrite the three ψ values through the matching hypothesis
  have e0 : lkPsi a σ2 ν m = (m : ℝ) - (γ * m + C * (1 - β ^ m)) := by
    have := hm m (by omega); linarith
  have e1 : lkPsi a σ2 ν ((m : ℝ) + 1)
      = ((m : ℝ) + 1) - (γ * ((m : ℝ) + 1) + C * (1 - β ^ (m + 1))) := by
    have := hm (m + 1) (by omega); push_cast at this; linarith
  have e2 : lkPsi a σ2 ν ((m : ℝ) + 2)
      = ((m : ℝ) + 2) - (γ * ((m : ℝ) + 2) + C * (1 - β ^ (m + 2))) := by
    have := hm (m + 2) (by omega); push_cast at this; linarith
  rw [e0, e1, e2] at hdiff
  linear_combination -hdiff

/-- **The rigidity core**: three squared-tilt moment equations
`σ² + r_m = C(1−β)²β^m` (`m = 0,1,2`) alone force `σ² = 0` and
`ν = C·δ_{ln β}`.  Factored out so that both the five-point theorem and
the one-sidedness equality case can consume it. -/
theorem rigidity_of_moment_eqs
    (hσ2 : 0 ≤ σ2) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hν0 : ν ({0} : Set ℝ) = 0)
    (hsq : ∀ m : ℕ, m ≤ 2 → Integrable (sqIntegrand (m : ℝ)) ν)
    (hmom : ∀ m : ℕ, m ≤ 2 →
      σ2 + ∫ x, sqIntegrand (m : ℝ) x ∂ν = C * (1 - β) ^ 2 * β ^ m) :
    σ2 = 0 ∧ ν = ENNReal.ofReal C • Measure.dirac (Real.log β) := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  -- the test function (e^x − β)²(e^x − 1)² and its expansion
  set T : ℝ → ℝ := fun x => (Real.exp x - β) ^ 2 * (Real.exp x - 1) ^ 2
    with hTdef
  have hTexp : ∀ x, T x
      = sqIntegrand 2 x - 2 * β * sqIntegrand 1 x + β ^ 2 * sqIntegrand 0 x := by
    intro x
    simp only [hTdef, sqIntegrand]
    rw [show (2 : ℝ) * x = x + x by ring, show (1 : ℝ) * x = x by ring,
      Real.exp_add]
    simp [Real.exp_zero]
    ring
  have hTint : Integrable T ν := by
    have : Integrable (fun x =>
        sqIntegrand 2 x - 2 * β * sqIntegrand 1 x + β ^ 2 * sqIntegrand 0 x) ν := by
      have i0 := hsq 0 (by omega); have i1 := hsq 1 (by omega)
      have i2 := hsq 2 (by omega)
      push_cast at i0 i1 i2
      exact (i2.sub (i1.const_mul _)).add (i0.const_mul _)
    exact this.congr (Filter.Eventually.of_forall fun x => (hTexp x).symm)
  -- the test integral equals −σ²(1−β)²
  have hTval : ∫ x, T x ∂ν = -(σ2 * (1 - β) ^ 2) := by
    have m0 := hmom 0 (by omega); have m1 := hmom 1 (by omega)
    have m2 := hmom 2 (by omega)
    push_cast at m0 m1 m2
    have i0 := hsq 0 (by omega); have i1 := hsq 1 (by omega)
    have i2 := hsq 2 (by omega)
    push_cast at i0 i1 i2
    have hcongr : ∫ x, T x ∂ν
        = ∫ x, (sqIntegrand 2 x - 2 * β * sqIntegrand 1 x
          + β ^ 2 * sqIntegrand 0 x) ∂ν :=
      integral_congr_ae (.of_forall fun x => hTexp x)
    have houter : ∫ x, (sqIntegrand 2 x - 2 * β * sqIntegrand 1 x
          + β ^ 2 * sqIntegrand 0 x) ∂ν
        = (∫ x, (sqIntegrand 2 x - 2 * β * sqIntegrand 1 x) ∂ν)
          + ∫ x, β ^ 2 * sqIntegrand 0 x ∂ν :=
      integral_add (i2.sub (i1.const_mul _)) (i0.const_mul _)
    have hinner : ∫ x, (sqIntegrand 2 x - 2 * β * sqIntegrand 1 x) ∂ν
        = (∫ x, sqIntegrand 2 x ∂ν) - ∫ x, 2 * β * sqIntegrand 1 x ∂ν :=
      integral_sub i2 (i1.const_mul _)
    have hcm1 : ∫ x, 2 * β * sqIntegrand 1 x ∂ν
        = 2 * β * ∫ x, sqIntegrand 1 x ∂ν := integral_const_mul _ _
    have hcm0 : ∫ x, β ^ 2 * sqIntegrand 0 x ∂ν
        = β ^ 2 * ∫ x, sqIntegrand 0 x ∂ν := integral_const_mul _ _
    rw [hcongr, houter, hinner, hcm1, hcm0]
    linear_combination β ^ 2 * m0 - 2 * β * m1 + m2
  -- nonnegativity of the test integral
  have hTnn : 0 ≤ ∫ x, T x ∂ν :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- σ² = 0
  have hσ0 : σ2 = 0 := by
    have h1β : 0 < (1 - β) ^ 2 := pow_pos (by linarith) 2
    nlinarith [hTnn, hTval]
  refine ⟨hσ0, ?_⟩
  -- the test vanishes, so ν is carried by {ln β} ∪ {0}; ν{0} = 0 kills 0
  have hTzero : ∫ x, T x ∂ν = 0 := by rw [hTval, hσ0]; ring
  have hae0 : T =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (sq_nonneg _) (sq_nonneg _)) hTint).mp hTzero
  have hne0 : ∀ᵐ x ∂ν, x ≠ 0 := by
    rw [ae_iff]
    simpa using hν0
  have hae : ∀ᵐ x ∂ν, x = Real.log β := by
    filter_upwards [hae0, hne0] with x hx hx0
    simp only [Pi.zero_apply, hTdef] at hx
    rcases mul_eq_zero.mp hx with h | h
    · have : Real.exp x = β := by
        have := sq_eq_zero_iff.mp h; linarith
      rw [← this, Real.log_exp]
    · exfalso
      have h1 : Real.exp x = 1 := by
        have := sq_eq_zero_iff.mp h; linarith
      have h0 : Real.exp x = Real.exp 0 := by rw [Real.exp_zero]; exact h1
      exact hx0 (Real.exp_eq_exp.mp h0)
  -- mass: r₀ = (β−1)²·‖ν‖ and r₀ = C(1−β)², so ‖ν‖ = C
  have hconst : (fun x => sqIntegrand 0 x) =ᵐ[ν]
      (fun _ => (β - 1) ^ 2) := by
    filter_upwards [hae] with x hx
    simp only [sqIntegrand, hx, zero_mul, Real.exp_zero, one_mul,
      Real.exp_log hβ0]
  have hsq0 : Integrable (sqIntegrand (0 : ℝ)) ν := by
    have := hsq 0 (by omega); push_cast at this; exact this
  have h1β : (β - 1) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.mpr hβ1.ne)
  haveI : IsFiniteMeasure ν := by
    have hic : Integrable (fun _ : ℝ => (β - 1) ^ 2) ν := hsq0.congr hconst
    rcases (integrable_const_iff).mp hic with h | h
    · exact absurd h h1β
    · exact h
  have hr0 : ∫ x, sqIntegrand 0 x ∂ν = (β - 1) ^ 2 * ν.real Set.univ := by
    rw [integral_congr_ae hconst, integral_const, smul_eq_mul, mul_comm]
  have hmass : ν.real Set.univ = C := by
    have m0 := hmom 0 (by omega)
    push_cast at m0
    rw [hσ0, zero_add, hr0] at m0
    refine mul_left_cancel₀ h1β ?_
    rw [m0]; ring
  rw [← hmass]
  exact eq_smul_dirac_of_ae_const hae

/-- Integrability of the three squared-tilt integrands from the five
lattice LK integrands. -/
lemma sq_integrable_of_lattice
    (hint : ∀ q : ℕ, q ≤ 4 → Integrable (lkIntegrand q) ν) :
    ∀ m : ℕ, m ≤ 2 → Integrable (sqIntegrand (m : ℝ)) ν := by
  intro m hm2
  have h1 := hint (m + 1) (by omega)
  have h2 := hint (m + 2) (by omega)
  push_cast at h1 h2
  exact integrable_sqIntegrand (hint m (by omega)) h1 h2

/-- **Theorem 17(ii) (Five-point rigidity)** of the v3 paper: let the
generator triplet `(a, σ², ν)` have `σ² ≥ 0`, the Lévy convention
`ν{0} = 0`, and LK integrands integrable at the five lattice points
(the rendering of "`ψ` finite on `[0,4]`").  If `ζ_q = q − ψ(q)` equals the
She–Lévêque curve `γq + C(1−β^q)`, `β ∈ (0,1)`, at `q ∈ {0,1,2,3,4}`, then

  `σ² = 0`  and  `ν = C·δ_{ln β}` :

the generator **is** the compound Poisson cascade.  No impersonator exists.
Note the absence of any hypothesis on the sign of `C` (the moment equations
force `C ≥ 0` en route), of any divergence bookkeeping, and of any moment
beyond `q = 4`. -/
theorem theorem17_five_point_rigidity
    (hσ2 : 0 ≤ σ2) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hν0 : ν ({0} : Set ℝ) = 0)
    (hint : ∀ q : ℕ, q ≤ 4 → Integrable (lkIntegrand q) ν)
    (hm : MatchesSLUpTo a σ2 ν γ C β 4) :
    σ2 = 0 ∧ ν = ENNReal.ofReal C • Measure.dirac (Real.log β) :=
  rigidity_of_moment_eqs hσ2 hβ hν0 (sq_integrable_of_lattice hint)
    (moment_eqs_of_matches hint hm)

end Rigidity

/-! ## Theorem 18, forward direction — the five-moment route (v3 proof) -/

section Theorem18

variable {ν : Measure ℝ} {a σ2 β L : ℝ}

lemma lkIntegrand_zero_fun (x : ℝ) : lkIntegrand 0 x = 0 := by
  unfold lkIntegrand
  simp

/-- `ψ(0) = 0` for every triplet. -/
lemma lkPsi_zero (a σ2 : ℝ) (ν : Measure ℝ) : lkPsi a σ2 ν 0 = 0 := by
  unfold lkPsi
  rw [integral_congr_ae (.of_forall fun x => lkIntegrand_zero_fun x)]
  simp

/-- **Theorem 18, forward direction, route B of the v3 proof**: A1 on the
generator exponents — stated on the increments
`δ_m = ζ_{m+1} − ζ_m`, `ζ_q = q − ψ(q)`, exactly as in Lemma 1 — together
with integrability of the LK integrands at the five lattice points alone
(strictly weaker than (S_c): no all-orders hypothesis, no divergence
bookkeeping) forces the compound Poisson cascade:

  `σ² = 0`,  `ν = C·δ_{ln β}`,  `C = (δ₀ − L)/(1−β)`.

The full-lattice A1 hypothesis is used only through the closed form of
Lemma 1 at `m ≤ 4` (`zeta_gamma_C`); rigidity is `theorem17_five_point_rigidity`. -/
theorem theorem18_forward_fiveMoment
    (hσ2 : 0 ≤ σ2) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hν0 : ν ({0} : Set ℝ) = 0)
    (hint : ∀ q : ℕ, q ≤ 4 → Integrable (lkIntegrand q) ν)
    (hA1 : SatisfiesA1
      (fun m => (((m + 1 : ℕ) : ℝ) - lkPsi a σ2 ν ((m + 1 : ℕ) : ℝ))
        - ((m : ℝ) - lkPsi a σ2 ν m)) β L) :
    σ2 = 0 ∧ ν = ENNReal.ofReal
      ((((1 : ℝ) - lkPsi a σ2 ν 1) - L) / (1 - β))
      • Measure.dirac (Real.log β) := by
  set δ : ℕ → ℝ := fun m =>
    (((m + 1 : ℕ) : ℝ) - lkPsi a σ2 ν ((m + 1 : ℕ) : ℝ))
      - ((m : ℝ) - lkPsi a σ2 ν m) with hδdef
  have hβ1 : β ≠ 1 := hβ.2.ne
  -- ζ telescopes the increments, and ζ₀ = 0
  have hzeta : ∀ q : ℕ, (q : ℝ) - lkPsi a σ2 ν q
      = ∑ j ∈ Finset.range q, δ j := by
    intro q
    rw [Finset.sum_range_sub
      (f := fun m : ℕ => (m : ℝ) - lkPsi a σ2 ν m)]
    simp [lkPsi_zero]
  -- Lemma 1 closed form at `k = 1`
  have hcf : ∀ q : ℕ, (q : ℝ) - lkPsi a σ2 ν q
      = L * q + (δ 0 - L) / (1 - β) * (1 - β ^ q) := by
    intro q
    rw [hzeta q]
    have := zeta_gamma_C δ β L 1 one_ne_zero hβ1 hA1 q
    simpa using this
  have hmatch : MatchesSLUpTo a σ2 ν L ((δ 0 - L) / (1 - β)) β 4 :=
    fun q _ => hcf q
  have hδ0 : δ 0 = (1 : ℝ) - lkPsi a σ2 ν 1 := by
    simp [hδdef, lkPsi_zero]
  rw [← hδ0]
  exact theorem17_five_point_rigidity hσ2 hβ hν0 hint hmatch

end Theorem18

/-! ## Theorem 17(i): one-sidedness at the next order -/

section OneSided

variable {ν : Measure ℝ} {a σ2 γ C β : ℝ}

/-- Under four-point matching, the fourth-order gap is exactly the third
moment residual: `ψ(4) − ψ^SL(4) = (σ² + r₂) − C(1−β)²β²`. -/
lemma psi4_gap_of_matches
    (hint : ∀ q : ℕ, q ≤ 4 → Integrable (lkIntegrand q) ν)
    (hm : MatchesSLUpTo a σ2 ν γ C β 3) :
    lkPsi a σ2 ν 4 - ((4 : ℝ) - (γ * 4 + C * (1 - β ^ (4 : ℕ))))
      = (σ2 + ∫ x, sqIntegrand (2 : ℝ) x ∂ν) - C * (1 - β) ^ 2 * β ^ 2 := by
  have h2 := hint 2 (by omega)
  have h3 := hint 3 (by omega)
  have h4 := hint 4 (by omega)
  push_cast at h3 h4
  have hdiff := lkPsi_second_diff (ν := ν) a σ2 (p := (2 : ℝ)) h2
    (by norm_num at h3 ⊢; exact h3) (by norm_num at h4 ⊢; exact h4)
  have e2 : lkPsi a σ2 ν 2 = (2 : ℝ) - (γ * 2 + C * (1 - β ^ (2 : ℕ))) := by
    have := hm 2 (by omega); push_cast at this; linarith
  have e3 : lkPsi a σ2 ν 3 = (3 : ℝ) - (γ * 3 + C * (1 - β ^ (3 : ℕ))) := by
    have := hm 3 (by omega); push_cast at this; linarith
  have h23 : (2 : ℝ) + 2 = 4 := by norm_num
  have h21 : (2 : ℝ) + 1 = 3 := by norm_num
  rw [h23, h21, e2, e3] at hdiff
  linear_combination hdiff

/-- Cauchy–Schwarz for the squared-tilt moments: `r₁² ≤ r₀ r₂`, by the
quadratic-discriminant argument on `t ↦ ∫ (t e^x + 1)²(e^x−1)² dν ≥ 0`. -/
lemma sq_moment_cauchy_schwarz
    (hsq : ∀ m : ℕ, m ≤ 2 → Integrable (sqIntegrand (m : ℝ)) ν) :
    (∫ x, sqIntegrand (1 : ℝ) x ∂ν) ^ 2
      ≤ (∫ x, sqIntegrand (0 : ℝ) x ∂ν) * ∫ x, sqIntegrand (2 : ℝ) x ∂ν := by
  have i0 := hsq 0 (by omega); have i1 := hsq 1 (by omega)
  have i2 := hsq 2 (by omega)
  push_cast at i0 i1 i2
  set r0 := ∫ x, sqIntegrand (0 : ℝ) x ∂ν
  set r1 := ∫ x, sqIntegrand (1 : ℝ) x ∂ν
  set r2 := ∫ x, sqIntegrand (2 : ℝ) x ∂ν
  have key : ∀ t : ℝ, 0 ≤ r2 * (t * t) + 2 * r1 * t + r0 := by
    intro t
    have hexp : ∀ x : ℝ, (t * Real.exp x + 1) ^ 2 * (Real.exp x - 1) ^ 2
        = t ^ 2 * sqIntegrand 2 x + 2 * t * sqIntegrand 1 x
          + sqIntegrand 0 x := by
      intro x
      simp only [sqIntegrand]
      rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add, one_mul, zero_mul,
        Real.exp_zero]
      ring
    have hnn : 0 ≤ ∫ x, (t * Real.exp x + 1) ^ 2 * (Real.exp x - 1) ^ 2 ∂ν :=
      integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hcongr : ∫ x, (t * Real.exp x + 1) ^ 2 * (Real.exp x - 1) ^ 2 ∂ν
        = ∫ x, (t ^ 2 * sqIntegrand 2 x + 2 * t * sqIntegrand 1 x
          + sqIntegrand 0 x) ∂ν :=
      integral_congr_ae (.of_forall fun x => hexp x)
    have houter : ∫ x, (t ^ 2 * sqIntegrand 2 x + 2 * t * sqIntegrand 1 x
          + sqIntegrand 0 x) ∂ν
        = (∫ x, (t ^ 2 * sqIntegrand 2 x + 2 * t * sqIntegrand 1 x) ∂ν)
          + ∫ x, sqIntegrand 0 x ∂ν :=
      integral_add ((i2.const_mul _).add (i1.const_mul _)) i0
    have hinner : ∫ x, (t ^ 2 * sqIntegrand 2 x + 2 * t * sqIntegrand 1 x) ∂ν
        = (∫ x, t ^ 2 * sqIntegrand 2 x ∂ν)
          + ∫ x, 2 * t * sqIntegrand 1 x ∂ν :=
      integral_add (i2.const_mul _) (i1.const_mul _)
    have hc2 : ∫ x, t ^ 2 * sqIntegrand 2 x ∂ν = t ^ 2 * r2 :=
      integral_const_mul _ _
    have hc1 : ∫ x, 2 * t * sqIntegrand 1 x ∂ν = 2 * t * r1 :=
      integral_const_mul _ _
    rw [hcongr, houter, hinner, hc2, hc1] at hnn
    nlinarith [hnn]
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-- **Theorem 17(i), one-sidedness** (v3): any generator triplet matching
`ζ^SL` at `q ∈ {0,1,2,3}` satisfies `ζ_4 ≤ ζ^SL_4` — every four-point
impersonator is at least as intermittent at the next order — and equality
holds iff the triplet **is** the compound Poisson cascade. -/
theorem theorem17_one_sided
    (hσ2 : 0 ≤ σ2) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hν0 : ν ({0} : Set ℝ) = 0)
    (hint : ∀ q : ℕ, q ≤ 4 → Integrable (lkIntegrand q) ν)
    (hm : MatchesSLUpTo a σ2 ν γ C β 3) :
    ((4 : ℝ) - lkPsi a σ2 ν 4) ≤ γ * 4 + C * (1 - β ^ (4 : ℕ))
      ∧ (((4 : ℝ) - lkPsi a σ2 ν 4) = γ * 4 + C * (1 - β ^ (4 : ℕ))
        ↔ σ2 = 0 ∧ ν = ENNReal.ofReal C • Measure.dirac (Real.log β)) := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  have hsq := sq_integrable_of_lattice hint
  have hgap := psi4_gap_of_matches hint hm
  -- the two pinned moments
  have hmom01 : ∀ m : ℕ, m ≤ 1 →
      σ2 + ∫ x, sqIntegrand (m : ℝ) x ∂ν = C * (1 - β) ^ 2 * β ^ m := by
    intro m hm1
    have h0 := hint m (by omega)
    have h1 := hint (m + 1) (by omega)
    have h2 := hint (m + 2) (by omega)
    push_cast at h1 h2
    have hdiff := lkPsi_second_diff (ν := ν) a σ2 (p := (m : ℝ)) h0 h1 h2
    have e0 : lkPsi a σ2 ν m = (m : ℝ) - (γ * m + C * (1 - β ^ m)) := by
      have := hm m (by omega); linarith
    have e1 : lkPsi a σ2 ν ((m : ℝ) + 1)
        = ((m : ℝ) + 1) - (γ * ((m : ℝ) + 1) + C * (1 - β ^ (m + 1))) := by
      have := hm (m + 1) (by omega); push_cast at this; linarith
    have e2 : lkPsi a σ2 ν ((m : ℝ) + 2)
        = ((m : ℝ) + 2) - (γ * ((m : ℝ) + 2) + C * (1 - β ^ (m + 2))) := by
      have := hm (m + 2) (by omega); push_cast at this; linarith
    rw [e0, e1, e2] at hdiff
    linear_combination -hdiff
  set r0 := ∫ x, sqIntegrand (0 : ℝ) x ∂ν with hr0def
  set r1 := ∫ x, sqIntegrand (1 : ℝ) x ∂ν with hr1def
  set r2 := ∫ x, sqIntegrand (2 : ℝ) x ∂ν with hr2def
  have m0 : σ2 + r0 = C * (1 - β) ^ 2 := by
    have := hmom01 0 (by omega); push_cast at this; simpa using this
  have m1 : σ2 + r1 = C * (1 - β) ^ 2 * β := by
    have := hmom01 1 (by omega); push_cast at this; simpa using this
  have hCS : r1 ^ 2 ≤ r0 * r2 := sq_moment_cauchy_schwarz hsq
  have hr0nn : 0 ≤ r0 := integral_nonneg fun x => sqIntegrand_nonneg _ x
  have hr1nn : 0 ≤ r1 := integral_nonneg fun x => sqIntegrand_nonneg _ x
  have hr2nn : 0 ≤ r2 := integral_nonneg fun x => sqIntegrand_nonneg _ x
  -- the inequality: σ² + r₂ ≥ A′β²
  have hA'nn : 0 ≤ C * (1 - β) ^ 2 := by nlinarith [hσ2, hr0nn, m0]
  have hineq : C * (1 - β) ^ 2 * β ^ 2 ≤ σ2 + r2 := by
    rcases hr0nn.eq_or_lt with h0 | h0pos
    · -- degenerate case r₀ = 0: the generator is trivial
      have hr1z : r1 = 0 := by nlinarith [hCS, sq_nonneg r1, h0]
      have hA'z : C * (1 - β) ^ 2 * (1 - β) = 0 := by
        nlinarith [m0, m1, h0, hr1z]
      have hA'0 : C * (1 - β) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hA'z with h | h
        · exact h
        · exact absurd h (by intro h; linarith [hβ1, h])
      nlinarith [hr2nn, hσ2, hA'0]
    · -- main case r₀ > 0: multiply through and use Cauchy–Schwarz
      have e0 : r0 = C * (1 - β) ^ 2 - σ2 := by linarith [m0]
      have e1 : r1 = C * (1 - β) ^ 2 * β - σ2 := by linarith [m1]
      have hCS' : (C * (1 - β) ^ 2 * β - σ2) ^ 2
          ≤ (C * (1 - β) ^ 2 - σ2) * r2 := by
        rw [← e0, ← e1]; exact hCS
      have hkey : 0 ≤ (σ2 + r2 - C * (1 - β) ^ 2 * β ^ 2)
          * (C * (1 - β) ^ 2 - σ2) := by
        nlinarith [hCS',
          mul_nonneg (mul_nonneg hA'nn hσ2) (sq_nonneg (1 - β))]
      have h0pos' : 0 < C * (1 - β) ^ 2 - σ2 := by rw [← e0]; exact h0pos
      by_contra hcon
      have hcon' : σ2 + r2 < C * (1 - β) ^ 2 * β ^ 2 := not_le.mp hcon
      have hneg : (σ2 + r2 - C * (1 - β) ^ 2 * β ^ 2)
          * (C * (1 - β) ^ 2 - σ2) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) h0pos'
      linarith [hkey, hneg]
  constructor
  · -- ζ₄ ≤ ζ^SL₄
    have := hgap
    push_cast at this ⊢
    linarith [hineq, this]
  · constructor
    · -- equality ⟹ CPC, via the rigidity core
      intro heq
      have hmom2 : σ2 + r2 = C * (1 - β) ^ 2 * β ^ 2 := by
        push_cast at hgap heq ⊢
        linarith [hgap, heq]
      refine rigidity_of_moment_eqs hσ2 ⟨hβ0, hβ1⟩ hν0 hsq ?_
      intro m hm2
      interval_cases m
      · simpa using m0
      · simpa using m1
      · simpa using hmom2
    · -- CPC ⟹ equality: compute r₂ on the Dirac generator
      rintro ⟨hσ0, hνeq⟩
      have hCnn : 0 ≤ C := by
        have hr0' : r0 = C * (1 - β) ^ 2 := by rw [hσ0] at m0; linarith
        have h1β : 0 < (1 - β) ^ 2 := pow_pos (by linarith) 2
        nlinarith [hr0nn, hr0', h1β]
      have hr2val : r2 = C * (1 - β) ^ 2 * β ^ 2 := by
        rw [hr2def, hνeq, integral_smul_measure]
        rw [integral_dirac]
        simp only [sqIntegrand, smul_eq_mul]
        rw [ENNReal.toReal_ofReal hCnn,
          show (2 : ℝ) * Real.log β = Real.log β + Real.log β by ring,
          Real.exp_add, Real.exp_log hβ0]
        ring
      linarith [hgap, hr2val, hσ0]

/-- **Theorem 17(i), the deficit budget** (v3): for attenuation-only
generators (`ν((0,∞)) = 0`, no amplifying jumps), the fourth-order
undershoot of any four-point impersonator is at most
`C(1−β)²·β(1−β) = Cβ(1−β)³`.  (Sharpening found while formalizing:
no sign hypothesis on `σ²` is needed — the `m = 1` moment equation
cancels it.) -/
theorem theorem17_one_sided_budget
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hint : ∀ q : ℕ, q ≤ 4 → Integrable (lkIntegrand q) ν)
    (hjump : ν (Set.Ioi (0 : ℝ)) = 0)
    (hm : MatchesSLUpTo a σ2 ν γ C β 3) :
    (γ * 4 + C * (1 - β ^ (4 : ℕ))) - ((4 : ℝ) - lkPsi a σ2 ν 4)
      ≤ C * β * (1 - β) ^ 3 := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  have hsq := sq_integrable_of_lattice hint
  have hgap := psi4_gap_of_matches hint hm
  -- a.e. x ≤ 0, hence r₂ ≤ r₁ pointwise
  have hae : ∀ᵐ x ∂ν, x ≤ 0 := by
    rw [ae_iff]
    have : {x : ℝ | ¬x ≤ 0} = Set.Ioi 0 := by
      ext x; simp [Set.mem_Ioi, not_le]
    rwa [this]
  have i1 := hsq 1 (by omega); have i2 := hsq 2 (by omega)
  push_cast at i1 i2
  have hr21 : ∫ x, sqIntegrand (2 : ℝ) x ∂ν
      ≤ ∫ x, sqIntegrand (1 : ℝ) x ∂ν := by
    refine integral_mono_ae i2 i1 ?_
    filter_upwards [hae] with x hx
    simp only [sqIntegrand]
    have hex : Real.exp x ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hx
    have h2x : Real.exp (2 * x) ≤ Real.exp (1 * x) := by
      apply Real.exp_le_exp.mpr; nlinarith
    exact mul_le_mul_of_nonneg_right h2x (sq_nonneg _)
  -- Δ² at m = 1 pins σ² + r₁
  have h1 := hint 1 (by omega)
  have h2 := hint 2 (by omega)
  have h3 := hint 3 (by omega)
  push_cast at h1 h2 h3
  have hdiff := lkPsi_second_diff (ν := ν) a σ2 (p := (1 : ℝ)) h1
    (by norm_num at h2 ⊢; exact h2) (by norm_num at h3 ⊢; exact h3)
  have e1 : lkPsi a σ2 ν 1 = (1 : ℝ) - (γ * 1 + C * (1 - β ^ (1 : ℕ))) := by
    have := hm 1 (by omega); push_cast at this; linarith
  have e2 : lkPsi a σ2 ν 2 = (2 : ℝ) - (γ * 2 + C * (1 - β ^ (2 : ℕ))) := by
    have := hm 2 (by omega); push_cast at this; linarith
  have e3 : lkPsi a σ2 ν 3 = (3 : ℝ) - (γ * 3 + C * (1 - β ^ (3 : ℕ))) := by
    have := hm 3 (by omega); push_cast at this; linarith
  have h12 : (1 : ℝ) + 2 = 3 := by norm_num
  have h11 : (1 : ℝ) + 1 = 2 := by norm_num
  rw [h12, h11, e1, e2, e3] at hdiff
  push_cast at hdiff hgap ⊢
  nlinarith [hgap, hdiff, hr21]

end OneSided

/-! ## Theorem 17(i): the explicit impersonators (exact rationals) -/

section Witnesses

/-- Integral against a nonnegative Dirac multiple. -/
lemma integral_ofReal_smul_dirac (f : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    ∫ y, f y ∂(ENNReal.ofReal c • Measure.dirac x) = c * f x := by
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hc,
    smul_eq_mul]

lemma integrable_ofReal_smul_dirac (f : ℝ → ℝ) (c : ℝ) (x : ℝ) :
    Integrable f (ENNReal.ofReal c • Measure.dirac x) :=
  (integrable_dirac (by simp [enorm_lt_top])).smul_measure ENNReal.ofReal_ne_top

/-- Integral against a three-atom measure. -/
lemma integral_three_atoms (f : ℝ → ℝ) {c1 c2 c3 : ℝ}
    (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) (x1 x2 x3 : ℝ) :
    ∫ y, f y ∂(ENNReal.ofReal c1 • Measure.dirac x1
      + (ENNReal.ofReal c2 • Measure.dirac x2
        + ENNReal.ofReal c3 • Measure.dirac x3))
      = c1 * f x1 + (c2 * f x2 + c3 * f x3) := by
  rw [integral_add_measure (integrable_ofReal_smul_dirac f c1 x1)
      ((integrable_ofReal_smul_dirac f c2 x2).add_measure
        (integrable_ofReal_smul_dirac f c3 x3)),
    integral_add_measure (integrable_ofReal_smul_dirac f c2 x2)
      (integrable_ofReal_smul_dirac f c3 x3),
    integral_ofReal_smul_dirac f h1, integral_ofReal_smul_dirac f h2,
    integral_ofReal_smul_dirac f h3]

/-- Integral against a two-atom measure. -/
lemma integral_two_atoms (f : ℝ → ℝ) {c1 c2 : ℝ}
    (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (x1 x2 : ℝ) :
    ∫ y, f y ∂(ENNReal.ofReal c1 • Measure.dirac x1
      + ENNReal.ofReal c2 • Measure.dirac x2)
      = c1 * f x1 + c2 * f x2 := by
  rw [integral_add_measure (integrable_ofReal_smul_dirac f c1 x1)
      (integrable_ofReal_smul_dirac f c2 x2),
    integral_ofReal_smul_dirac f h1, integral_ofReal_smul_dirac f h2]

/-- The drift-eliminated combination at order 2:
`f₂ − 2f₁ = (e^x − 1)²` (compensators cancel). -/
lemma lkIntegrand_comb2 (x : ℝ) :
    lkIntegrand 2 x - 2 * lkIntegrand 1 x = (Real.exp x - 1) ^ 2 := by
  unfold lkIntegrand
  rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add, one_mul]
  ring

/-- The drift-eliminated combination at order 3:
`f₃ − 3f₁ = e^{3x} − 3e^x + 2`. -/
lemma lkIntegrand_comb3 (x : ℝ) :
    lkIntegrand 3 x - 3 * lkIntegrand 1 x
      = Real.exp x ^ 3 - 3 * Real.exp x + 2 := by
  unfold lkIntegrand
  rw [show (3 : ℝ) * x = x + (x + x) by ring, Real.exp_add, Real.exp_add,
    one_mul]
  ring

/-- The drift-eliminated combination at order 4:
`f₄ − 4f₁ = e^{4x} − 4e^x + 3`. -/
lemma lkIntegrand_comb4 (x : ℝ) :
    lkIntegrand 4 x - 4 * lkIntegrand 1 x
      = Real.exp x ^ 4 - 4 * Real.exp x + 3 := by
  unfold lkIntegrand
  rw [show (4 : ℝ) * x = x + (x + (x + x)) by ring, Real.exp_add,
    Real.exp_add, Real.exp_add, one_mul]
  ring

/-- Two Dirac positions with positive mass force equality of the points:
a two-plus-atom measure is no Dirac multiple. -/
lemma ne_smul_dirac_of_two_atoms {μ : Measure ℝ} {x y : ℝ} (hxy : x ≠ y)
    (hx : μ {x} ≠ 0) (hy : μ {y} ≠ 0) :
    ∀ (c : ℝ≥0∞) (b : ℝ), μ ≠ c • Measure.dirac b := by
  intro c b h
  have hbx : b = x := by
    by_contra hbx
    apply hx
    rw [h, Measure.smul_apply,
      Measure.dirac_apply' b (measurableSet_singleton x),
      Set.indicator_of_notMem (by simpa using hbx), smul_eq_mul, mul_zero]
  have hby : b = y := by
    by_contra hby
    apply hy
    rw [h, Measure.smul_apply,
      Measure.dirac_apply' b (measurableSet_singleton y),
      Set.indicator_of_notMem (by simpa using hby), smul_eq_mul, mul_zero]
  exact hxy (hbx ▸ hby)

/-- Singleton mass of a three-atom measure at its second atom. -/
lemma three_atoms_mass_snd {c1 c2 c3 : ℝ} {x1 x2 x3 : ℝ}
    (h12 : x1 ≠ x2) (h32 : x3 ≠ x2) :
    (ENNReal.ofReal c1 • Measure.dirac x1
      + (ENNReal.ofReal c2 • Measure.dirac x2
        + ENNReal.ofReal c3 • Measure.dirac x3)) {x2}
      = ENNReal.ofReal c2 := by
  rw [Measure.add_apply, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' x1 (measurableSet_singleton x2),
    Measure.dirac_apply' x2 (measurableSet_singleton x2),
    Measure.dirac_apply' x3 (measurableSet_singleton x2),
    Set.indicator_of_notMem (by simpa using h12),
    Set.indicator_of_mem (Set.mem_singleton x2),
    Set.indicator_of_notMem (by simpa using h32)]
  simp

/-- **The printed three-point impersonator family** (v3 Theorem 17(i),
proof), at the paper's parameters `(β, C, γ) = (2/3, 2, 1/3)`,
`(v₁, v₂) = (3/10, 9/10)`, `c = 1`: for `s ∈ (0, 2]`, the CPC atom loses
mass `s` and the two side atoms gain `w₁ = 5s/27`, `w₂ = 55s/27`
(in x-space: atoms at `ln v_i`). -/
noncomputable def nu3 (s : ℝ) : Measure ℝ :=
  ENNReal.ofReal (2 - s) • Measure.dirac (Real.log (2 / 3))
    + (ENNReal.ofReal (5 * s / 27) • Measure.dirac (Real.log (3 / 10))
      + ENNReal.ofReal (55 * s / 27) • Measure.dirac (Real.log (9 / 10)))

/-- **Theorem 17(i), three-point impersonation** (v3, exact rationals):
for every `s ∈ (0, 2]` there is a drift making the three-atom generator
`nu3 s` (with `σ² = 0`) match `ζ^SL` exactly at `q ∈ {0, 1, 2}`, while
overshooting at `q = 3` by exactly `77s/2700` (`s = 1/2`: the paper's
`+77/5400 ≈ +0.0143`) — and `nu3 s` is never a Dirac multiple: the
physically typical window cannot certify the log-Poisson class. -/
theorem theorem17_impersonation_three_point {s : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) 2) :
    ∃ a : ℝ,
      MatchesSLUpTo a 0 (nu3 s) (1 / 3) 2 (2 / 3) 2
      ∧ ((3 : ℝ) - lkPsi a 0 (nu3 s) 3)
          - ((1 / 3 : ℝ) * 3 + 2 * (1 - (2 / 3 : ℝ) ^ (3 : ℕ)))
          = 77 * s / 2700
      ∧ ∀ (c : ℝ≥0∞) (b : ℝ), nu3 s ≠ c • Measure.dirac b := by
  obtain ⟨hs0, hs2⟩ := hs
  have hm1 : (0 : ℝ) ≤ 2 - s := by linarith
  have hm2 : (0 : ℝ) ≤ 5 * s / 27 := by linarith
  have hm3 : (0 : ℝ) ≤ 55 * s / 27 := by linarith
  have hv1 : Real.exp (Real.log (2 / 3 : ℝ)) = 2 / 3 :=
    Real.exp_log (by norm_num)
  have hv2 : Real.exp (Real.log (3 / 10 : ℝ)) = 3 / 10 :=
    Real.exp_log (by norm_num)
  have hv3 : Real.exp (Real.log (9 / 10 : ℝ)) = 9 / 10 :=
    Real.exp_log (by norm_num)
  set D : ℝ → ℝ := fun q =>
    (2 - s) * lkIntegrand q (Real.log (2 / 3))
      + (5 * s / 27 * lkIntegrand q (Real.log (3 / 10))
        + 55 * s / 27 * lkIntegrand q (Real.log (9 / 10))) with hD
  have hψ : ∀ q : ℝ, lkPsi (-(D 1)) 0 (nu3 s) q = -(D 1) * q + D q := by
    intro q
    unfold lkPsi nu3
    rw [integral_three_atoms (lkIntegrand q) hm1 hm2 hm3]
    simp only [hD]
    ring
  -- the two drift-eliminated rational identities
  have hD2 : D 2 - 2 * D 1 = 2 / 9 := by
    have k1 := lkIntegrand_comb2 (Real.log (2 / 3))
    have k2 := lkIntegrand_comb2 (Real.log (3 / 10))
    have k3 := lkIntegrand_comb2 (Real.log (9 / 10))
    rw [hv1] at k1; rw [hv2] at k2; rw [hv3] at k3
    simp only [hD]
    nlinarith [k1, k2, k3]
  have hD3 : D 3 - 3 * D 1 = 16 / 27 - 77 * s / 2700 := by
    have k1 := lkIntegrand_comb3 (Real.log (2 / 3))
    have k2 := lkIntegrand_comb3 (Real.log (3 / 10))
    have k3 := lkIntegrand_comb3 (Real.log (9 / 10))
    rw [hv1] at k1; rw [hv2] at k2; rw [hv3] at k3
    simp only [hD]
    nlinarith [k1, k2, k3]
  refine ⟨-(D 1), ?_, ?_, ?_⟩
  · -- matching at q = 0, 1, 2
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
  · -- the deviation at q = 3
    rw [hψ 3]
    norm_num
    linarith [hD3]
  · -- never a Dirac multiple
    have h12 : Real.log (2 / 3 : ℝ) ≠ Real.log (3 / 10 : ℝ) := by
      intro h
      have := congrArg Real.exp h
      rw [hv1, hv2] at this
      norm_num at this
    have h32 : Real.log (9 / 10 : ℝ) ≠ Real.log (3 / 10 : ℝ) := by
      intro h
      have := congrArg Real.exp h
      rw [hv3, hv2] at this
      norm_num at this
    have h23 : Real.log (3 / 10 : ℝ) ≠ Real.log (9 / 10 : ℝ) :=
      fun h => h32 h.symm
    have hx2 : nu3 s {Real.log (3 / 10 : ℝ)} ≠ 0 := by
      unfold nu3
      rw [three_atoms_mass_snd h12 h32]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
    have hx3 : nu3 s {Real.log (9 / 10 : ℝ)} ≠ 0 := by
      unfold nu3
      have hmass : (ENNReal.ofReal (2 - s) • Measure.dirac (Real.log (2 / 3))
          + (ENNReal.ofReal (5 * s / 27) • Measure.dirac (Real.log (3 / 10))
            + ENNReal.ofReal (55 * s / 27)
              • Measure.dirac (Real.log (9 / 10))))
            {Real.log (9 / 10 : ℝ)} = ENNReal.ofReal (55 * s / 27) := by
        rw [Measure.add_apply, Measure.add_apply, Measure.smul_apply,
          Measure.smul_apply, Measure.smul_apply,
          Measure.dirac_apply' _ (measurableSet_singleton _),
          Measure.dirac_apply' _ (measurableSet_singleton _),
          Measure.dirac_apply' _ (measurableSet_singleton _),
          Set.indicator_of_notMem (by
            simpa using (by
              intro h
              have := congrArg Real.exp h
              rw [hv1, hv3] at this
              norm_num at this : Real.log (2 / 3 : ℝ) ≠ Real.log (9 / 10 : ℝ))),
          Set.indicator_of_notMem (by simpa using h23),
          Set.indicator_of_mem (Set.mem_singleton _)]
        simp
      rw [hmass]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
    exact ne_smul_dirac_of_two_atoms h23 hx2 hx3

/-- **The three-point family is a genuine continuum**: `s ↦ nu3 s` is
injective on `(0, 2]` (the printed "one-parameter family of genuine Lévy
measures"). -/
theorem nu3_injOn : Set.InjOn nu3 (Set.Ioc (0 : ℝ) 2) := by
  intro s hs t ht h
  have h12 : Real.log (2 / 3 : ℝ) ≠ Real.log (3 / 10 : ℝ) := by
    intro h'
    have := congrArg Real.exp h'
    rw [Real.exp_log (by norm_num), Real.exp_log (by norm_num)] at this
    norm_num at this
  have h32 : Real.log (9 / 10 : ℝ) ≠ Real.log (3 / 10 : ℝ) := by
    intro h'
    have := congrArg Real.exp h'
    rw [Real.exp_log (by norm_num), Real.exp_log (by norm_num)] at this
    norm_num at this
  have hmass := congrArg (fun μ => μ {Real.log (3 / 10 : ℝ)}) h
  simp only [nu3] at hmass
  rw [three_atoms_mass_snd h12 h32, three_atoms_mass_snd h12 h32] at hmass
  have hs0 : (0 : ℝ) ≤ 5 * s / 27 := by linarith [hs.1]
  have ht0 : (0 : ℝ) ≤ 5 * t / 27 := by linarith [ht.1]
  have := (ENNReal.ofReal_eq_ofReal_iff hs0 ht0).mp hmass
  linarith

/-- **The maximal-window impersonator** (v3 Theorem 17(i), proof): the
two-atom ρ-space construction at `(β, C) = (2/3, 2)`, atoms
`(v₁, v₂) = (2/5, 19/20)` with exact rational Lévy masses
`850/2673` and `12800/297` (i.e. squared-tilt weights `34/297`, `32/297`). -/
noncomputable def nu4 : Measure ℝ :=
  ENNReal.ofReal (850 / 2673) • Measure.dirac (Real.log (2 / 5))
    + ENNReal.ofReal (12800 / 297) • Measure.dirac (Real.log (19 / 20))

/-- **Theorem 17(i), maximal-window impersonation** (v3, exact rationals):
there is a drift making the two-atom generator `nu4` (with `σ² = 0`) match
`ζ^SL` exactly at `q ∈ {0, 1, 2, 3}` — the full four-point window — while
undershooting at `q = 4` by exactly `34/2025 ≈ 0.01679`; and `nu4` is not
a Dirac multiple.  Together with `theorem17_five_point_rigidity` this
shows the identifiability boundary sits exactly between four and five
contiguous orders. -/
theorem theorem17_impersonation_four_point :
    ∃ a : ℝ,
      MatchesSLUpTo a 0 nu4 (1 / 3) 2 (2 / 3) 3
      ∧ ((4 : ℝ) - lkPsi a 0 nu4 4)
          - ((1 / 3 : ℝ) * 4 + 2 * (1 - (2 / 3 : ℝ) ^ (4 : ℕ)))
          = -(34 / 2025)
      ∧ ∀ (c : ℝ≥0∞) (b : ℝ), nu4 ≠ c • Measure.dirac b := by
  have hm1 : (0 : ℝ) ≤ 850 / 2673 := by norm_num
  have hm2 : (0 : ℝ) ≤ 12800 / 297 := by norm_num
  have hv1 : Real.exp (Real.log (2 / 5 : ℝ)) = 2 / 5 :=
    Real.exp_log (by norm_num)
  have hv2 : Real.exp (Real.log (19 / 20 : ℝ)) = 19 / 20 :=
    Real.exp_log (by norm_num)
  set D : ℝ → ℝ := fun q =>
    850 / 2673 * lkIntegrand q (Real.log (2 / 5))
      + 12800 / 297 * lkIntegrand q (Real.log (19 / 20)) with hD
  have hψ : ∀ q : ℝ, lkPsi (-(D 1)) 0 nu4 q = -(D 1) * q + D q := by
    intro q
    unfold lkPsi nu4
    rw [integral_two_atoms (lkIntegrand q) hm1 hm2]
    simp only [hD]
    ring
  have hD2 : D 2 - 2 * D 1 = 2 / 9 := by
    have k1 := lkIntegrand_comb2 (Real.log (2 / 5))
    have k2 := lkIntegrand_comb2 (Real.log (19 / 20))
    rw [hv1] at k1; rw [hv2] at k2
    simp only [hD]
    nlinarith [k1, k2]
  have hD3 : D 3 - 3 * D 1 = 16 / 27 := by
    have k1 := lkIntegrand_comb3 (Real.log (2 / 5))
    have k2 := lkIntegrand_comb3 (Real.log (19 / 20))
    rw [hv1] at k1; rw [hv2] at k2
    simp only [hD]
    nlinarith [k1, k2]
  have hD4 : D 4 - 4 * D 1 = 8008 / 7425 := by
    have k1 := lkIntegrand_comb4 (Real.log (2 / 5))
    have k2 := lkIntegrand_comb4 (Real.log (19 / 20))
    rw [hv1] at k1; rw [hv2] at k2
    simp only [hD]
    nlinarith [k1, k2]
  refine ⟨-(D 1), ?_, ?_, ?_⟩
  · intro q hq
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
  · rw [hψ 4]
    norm_num
    linarith [hD4]
  · have h12 : Real.log (2 / 5 : ℝ) ≠ Real.log (19 / 20 : ℝ) := by
      intro h
      have := congrArg Real.exp h
      rw [hv1, hv2] at this
      norm_num at this
    have hx1 : nu4 {Real.log (2 / 5 : ℝ)} ≠ 0 := by
      unfold nu4
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        Measure.dirac_apply' _ (measurableSet_singleton _),
        Measure.dirac_apply' _ (measurableSet_singleton _),
        Set.indicator_of_mem (Set.mem_singleton _),
        Set.indicator_of_notMem (by simpa using h12.symm)]
      simp
    have hx2 : nu4 {Real.log (19 / 20 : ℝ)} ≠ 0 := by
      unfold nu4
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        Measure.dirac_apply' _ (measurableSet_singleton _),
        Measure.dirac_apply' _ (measurableSet_singleton _),
        Set.indicator_of_notMem (by simpa using h12),
        Set.indicator_of_mem (Set.mem_singleton _)]
      simp
    exact ne_smul_dirac_of_two_atoms h12 hx1 hx2

end Witnesses

end Freeburg

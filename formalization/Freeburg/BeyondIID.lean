/-
Freeburg formalization — BeyondIID.lean
Section 6 (beyond independence) of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632 (v3 draft).
-/
import Freeburg.Basic
import Freeburg.LogPoissonLaw

/-!
# Beyond independence: what A1 does and does not determine (§6)

Section 6's four results, in the scoped forms of the Phase-5 runbook —
each formalizes the printed proof's *mathematical content*, with the two
classical bridges (de Finetti; Perron–Frobenius analyticity) stated as
hypotheses exactly where the paper cites them:

* `Freeburg.theorem13_asymptotic_classification` — **Theorem 13**: under
  the standing assumptions (S) the lattice exponent sequence
  `ζ_m = Λ(mk)/ln r` satisfies A1 **iff** it equals the log-Poisson
  closed form `Lm + C(1−β^m)`, `C = (ζ₁ − L)/(1−β)` — the "deliberately
  easy" direction-pair, both directions pure algebra riding on Lemma 1.
* `Freeburg.theorem14_even_block_moments`,
  `Freeburg.theorem14_marginal_ne_logPoisson` — **Theorem 14, the
  law-level counterexample's quantitative core**: the interleaved
  construction's two-slot block product `W₁W₂ = e^{2a + bA}`,
  `A ∼ Poisson(2λ)`, *is* `logPoissonLaw (2a) b (2λ)` and its moments
  equal `exp(2·Λ_LP(m))` exactly — the i.i.d. log-Poisson values — while
  the one-step marginal (the phase mixture
  `½·logPoisson(a,b,2λ) + ½·δ_{e^a}`) is **not** the log-Poisson(λ)
  marginal: its mass at `e^a` is `½(1 + e^{−2λ}) > e^{−λ}`.  (The full
  stationary-ergodic process realization — sequence space, phase shift,
  Kolmogorov 0–1 — is the classical layer and is not re-proved here;
  the paper's numbers `0.531` vs `0.250` at `λ = 2 ln 2` are instances
  of the strict inequality proved below.)
* `Freeburg.corollary15_conditional` — **Corollary 15 (exchangeable
  rigidity), conditional form**: taking the de Finetti decomposition as
  hypothesis (a directing kernel `κ` with conditionally-i.i.d. moment
  identities at `n = 1, 2`), the paper's argument is formalized in full:
  variance vanishes, the conditional moments are a.s. *exactly* the A1
  lattice moments simultaneously at all orders, and Phase-1 determinacy
  (`theorem3_law_uniqueness_W`) applies pointwise: **a.e. directing
  measure is the log-Poisson law** — the mixture is degenerate.
  De Finetti itself is deliberately out of scope (documented).
* `Freeburg.theorem16_growth_contradiction`,
  `Freeburg.theorem16_scoped` — **Theorem 16 (finite-state
  impossibility), growth-contradiction core**: if `Λ` agrees with the
  log-Poisson cumulant `Λ_LP` on all of `ℝ` (the conclusion the paper
  draws from Perron–Frobenius simplicity + the identity theorem — the
  unformalized bridge, stated as a hypothesis) while satisfying the
  finite-alphabet linear bound `Λ(p) ≤ p·f_min` for `p ≤ 0`, then
  `False`: with `b < 0`, `λ > 0` the log-Poisson cumulant grows
  superlinearly as `p → −∞` (`e^x ≥ x²/4` beats any line).

Everything in this file is sorry-free.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Freeburg

/-! ## Theorem 13: the asymptotic-statistics classification -/

/-- **Theorem 13 (Asymptotic-statistics classification)**: under (S),
with `ζ_m = Λ(mk)/ln r` the lattice exponents (`ζ₀ = 0` since
`m_n(0) = 1`), A1 on the increments holds **iff** `ζ` is the log-Poisson
closed form `ζ_m = Lm + C(1−β^m)`, `C = (ζ₁ − L)/(1−β)` — so every
observable computed from lattice exponents coincides with the i.i.d.
log-Poisson cascade's.  Both directions are pure algebra (Lemma 1 and
the Proposition-5 computation); this is the paper's "deliberately easy"
theorem, and the formalization is correspondingly thin. -/
theorem theorem13_asymptotic_classification {ζseq : ℕ → ℝ} {β L : ℝ}
    (hβ1 : β ≠ 1) (hζ0 : ζseq 0 = 0) :
    SatisfiesA1 (fun m => ζseq (m + 1) - ζseq m) β L
      ↔ ∀ m : ℕ, ζseq m
          = L * m + (ζseq 1 - L) / (1 - β) * (1 - β ^ m) := by
  constructor
  · intro hA1 m
    have htel : ζseq m
        = ∑ j ∈ Finset.range m, (ζseq (j + 1) - ζseq j) := by
      rw [Finset.sum_range_sub (f := ζseq), hζ0, sub_zero]
    have hcf := zeta_gamma_C (fun m => ζseq (m + 1) - ζseq m) β L 1
      one_ne_zero hβ1 hA1 m
    rw [htel, hcf, hζ0]
    norm_num
  · intro hcf m
    have h0 := hcf m
    have h1 := hcf (m + 1)
    have h2 := hcf (m + 2)
    push_cast at h0 h1 h2
    linear_combination h2 - h1 - β * (h1 - h0)

/-! ## Theorem 14: the quantitative core of the law-level counterexample -/

/-- **Theorem 14(i), block level**: the interleaved construction's
two-slot product `W₁W₂ = e^{2a+bA}`, `A ∼ Poisson(2λ)`, has moments

  `E[(W₁W₂)^m] = exp(2·(am + λ(e^{bm}−1))) = exp(2·Λ_LP(m))`

**exactly** — the even-window moments of the i.i.d. log-Poisson cascade,
at every order.  (The block-product law is literally
`logPoissonLaw (2a) b (2λ)`, so this is the doubled-intensity moment
formula; the odd-window sandwich and the limit `Λ = Λ_LP` are the
paper's remaining two lines.) -/
theorem theorem14_even_block_moments (a b : ℝ) (lam : ℝ≥0) (m : ℕ) :
    ∫ w, w ^ m ∂(logPoissonLaw (2 * a) b (2 * lam))
      = Real.exp (2 * (a * m + (lam : ℝ) * (Real.exp (b * m) - 1))) := by
  rw [integral_pow_logPoissonLaw]
  push_cast
  ring_nf

/-- The phase-mixture marginal of the interleaved construction:
`½·law(e^{a+bA'}) + ½·δ_{e^a}`, `A' ∼ Poisson(2λ)` — jump slots of
doubled intensity alternating with deterministic slots, seen through a
uniform phase. -/
noncomputable def interleavedMarginal (a b : ℝ) (lam : ℝ≥0) : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • logPoissonLaw a b (2 * lam)
    + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (Real.exp a)

/-- The mass of the log-Poisson law at the top atom `e^a` is the
Poisson vacancy probability `e^{−λ}` (for `b ≠ 0` only `n = 0` lands
there). -/
lemma logPoissonLaw_mass_top (a : ℝ) {b : ℝ} (hb : b ≠ 0) (lam : ℝ≥0) :
    logPoissonLaw a b lam {Real.exp a}
      = ENNReal.ofReal (Real.exp (-(lam : ℝ))) := by
  rw [logPoissonLaw, Measure.map_apply Measurable.of_discrete
    (measurableSet_singleton _)]
  have hpre : (fun n : ℕ => Real.exp (a + b * n)) ⁻¹' {Real.exp a}
      = {0} := by
    ext n
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      have heq := Real.exp_eq_exp.mp h
      have hbn : b * (n : ℝ) = 0 := by linarith
      rcases mul_eq_zero.mp hbn with h' | h'
      · exact absurd h' hb
      · exact_mod_cast h'
    · intro h
      subst h
      norm_num
  rw [hpre, poissonMeasure_singleton]
  simp

/-- **Theorem 14(ii): the marginal is not log-Poisson.**  For `λ > 0`,
`b ≠ 0`, the interleaved marginal differs from the matched log-Poisson
marginal: its mass at the top atom `e^a` is `½(1 + e^{−2λ})`, strictly
above the log-Poisson vacancy `e^{−λ}` (the gap is `½(1−e^{−λ})² > 0`;
at the paper's `λ = 2 ln 2`: `0.531` vs `0.250`).  The statement is the
paper's printed comparison — inequality with the *matched-parameter*
log-Poisson law, which is what refutes per-step determination; it does
not assert inequality with every log-Poisson law.  Together with (i),
A1-exact asymptotics do **not** determine the per-step law. -/
theorem theorem14_marginal_ne_logPoisson (a : ℝ) {b : ℝ} (hb : b ≠ 0)
    {lam : ℝ≥0} (hlam : 0 < lam) :
    interleavedMarginal a b lam ≠ logPoissonLaw a b lam := by
  intro h
  have hmass := congrArg (fun μ : Measure ℝ => μ {Real.exp a}) h
  simp only [interleavedMarginal, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul] at hmass
  rw [logPoissonLaw_mass_top a hb (2 * lam),
    logPoissonLaw_mass_top a hb lam,
    Measure.dirac_apply' _ (measurableSet_singleton _),
    Set.indicator_of_mem (Set.mem_singleton _)] at hmass
  simp only [Pi.one_apply, mul_one] at hmass
  -- pass to real numbers
  have e2ne : ((2 : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≠ ⊤ := by simp
  have t1ne : (2 : ℝ≥0∞)⁻¹
      * ENNReal.ofReal (Real.exp (-(((2 * lam : ℝ≥0)) : ℝ))) ≠ ⊤ :=
    ENNReal.mul_ne_top e2ne ENNReal.ofReal_ne_top
  have hreal := congrArg ENNReal.toReal hmass
  rw [ENNReal.toReal_add t1ne e2ne, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_nonneg _),
    ENNReal.toReal_ofReal (Real.exp_nonneg _),
    ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hreal
  -- hreal : ½·e^{−2λ} + ½ = e^{−λ}; contradict via (1 − e^{−λ})² > 0
  set t : ℝ := Real.exp (-(lam : ℝ)) with ht
  have hl : (0 : ℝ) < (lam : ℝ) := by exact_mod_cast hlam
  have ht1 : t < 1 := by
    rw [ht, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have ht2 : Real.exp (-(((2 * lam : ℝ≥0)) : ℝ)) = t ^ 2 := by
    rw [ht, sq, ← Real.exp_add]
    push_cast
    ring_nf
  rw [ht2] at hreal
  nlinarith [hreal, sq_nonneg (1 - t)]

/-! ## Corollary 15: exchangeable rigidity, conditional form -/

/-- **Corollary 15 (Exchangeable rigidity), conditional form.**  Taking
the de Finetti decomposition as hypothesis — a directing kernel
`κ : Ω → Measure ℝ` of probability measures with the conditional
moment identities the paper extracts from conditional independence at
`n = 1, 2` — the paper's argument runs in full: `Var(M_p) = 0` at every
lattice order, so a.e. directing measure has *exactly* the A1 lattice
moments simultaneously, and Phase-1 determinacy identifies it:

  **almost every directing measure is the log-Poisson law** —
  the exchangeable mixture is degenerate, `(W_n)` is i.i.d. log-Poisson.

De Finetti's theorem itself (exchangeable ⟹ such a kernel exists) is
the classical bridge and deliberately not formalized. -/
theorem corollary15_conditional {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Ω → Measure ℝ)
    (r γ C β : ℝ) {k : ℕ} (hk : k ≠ 0)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (lam : ℝ≥0) (hlam : (lam : ℝ) = -(C * Real.log r))
    (hprob : ∀ ω, IsProbabilityMeasure (κ ω))
    (hpos : ∀ ω, ∀ᵐ x ∂κ ω, 0 ≤ x)
    (hint : ∀ ω, ∀ m : ℕ, Integrable (fun x => x ^ (k * m)) (κ ω))
    (hMint : ∀ m : ℕ,
      Integrable (fun ω => ∫ x, x ^ (k * m) ∂κ ω) P)
    (hMsq : ∀ m : ℕ,
      Integrable (fun ω => (∫ x, x ^ (k * m) ∂κ ω) ^ 2) P)
    (h1 : ∀ m : ℕ, ∫ ω, (∫ x, x ^ (k * m) ∂κ ω) ∂P
      = r ^ (γ * k * m + C * (1 - β ^ m)))
    (h2 : ∀ m : ℕ, ∫ ω, (∫ x, x ^ (k * m) ∂κ ω) ^ 2 ∂P
      = (r ^ (γ * k * m + C * (1 - β ^ m))) ^ 2) :
    ∀ᵐ ω ∂P, κ ω
      = logPoissonLaw (γ * Real.log r) (Real.log β / k) lam := by
  -- Step 1: variance zero at each order ⟹ M_m = t_m a.s.
  have hae : ∀ m : ℕ, ∀ᵐ ω ∂P,
      (∫ x, x ^ (k * m) ∂κ ω)
        = r ^ (γ * k * m + C * (1 - β ^ m)) := by
    intro m
    set t : ℝ := r ^ (γ * k * m + C * (1 - β ^ m)) with htdef
    have hvar : ∫ ω, ((∫ x, x ^ (k * m) ∂κ ω) - t) ^ 2 ∂P = 0 := by
      have hexpand : ∀ ω : Ω, ((∫ x, x ^ (k * m) ∂κ ω) - t) ^ 2
          = (∫ x, x ^ (k * m) ∂κ ω) ^ 2
            - 2 * t * (∫ x, x ^ (k * m) ∂κ ω) + t ^ 2 := by
        intro ω; ring
      rw [show (fun ω => ((∫ x, x ^ (k * m) ∂κ ω) - t) ^ 2)
          = fun ω => (∫ x, x ^ (k * m) ∂κ ω) ^ 2
            - 2 * t * (∫ x, x ^ (k * m) ∂κ ω) + t ^ 2 from
        funext hexpand]
      have hI1 : Integrable (fun ω => (∫ x, x ^ (k * m) ∂κ ω) ^ 2
          - 2 * t * ∫ x, x ^ (k * m) ∂κ ω) P :=
        (hMsq m).sub ((hMint m).const_mul _)
      have hsplit1 : ∫ ω, ((∫ x, x ^ (k * m) ∂κ ω) ^ 2
            - 2 * t * ∫ x, x ^ (k * m) ∂κ ω + t ^ 2) ∂P
          = (∫ ω, ((∫ x, x ^ (k * m) ∂κ ω) ^ 2
            - 2 * t * ∫ x, x ^ (k * m) ∂κ ω) ∂P) + ∫ _ω, t ^ 2 ∂P :=
        integral_add hI1 (integrable_const _)
      have hsplit2 : ∫ ω, ((∫ x, x ^ (k * m) ∂κ ω) ^ 2
            - 2 * t * ∫ x, x ^ (k * m) ∂κ ω) ∂P
          = (∫ ω, (∫ x, x ^ (k * m) ∂κ ω) ^ 2 ∂P)
            - ∫ ω, 2 * t * ∫ x, x ^ (k * m) ∂κ ω ∂P :=
        integral_sub (hMsq m) ((hMint m).const_mul _)
      have hcm : ∫ ω, 2 * t * ∫ x, x ^ (k * m) ∂κ ω ∂P
          = 2 * t * ∫ ω, ∫ x, x ^ (k * m) ∂κ ω ∂P :=
        integral_const_mul _ _
      rw [hsplit1, hsplit2, hcm, h1 m, h2 m, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      ring
    have hsqint : Integrable
        (fun ω => ((∫ x, x ^ (k * m) ∂κ ω) - t) ^ 2) P := by
      have : Integrable (fun ω => (∫ x, x ^ (k * m) ∂κ ω) ^ 2
          - 2 * t * (∫ x, x ^ (k * m) ∂κ ω) + t ^ 2) P :=
        ((hMsq m).sub ((hMint m).const_mul _)).add (integrable_const _)
      exact this.congr (Filter.Eventually.of_forall fun ω => by ring)
    have := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg _) hsqint).mp hvar
    filter_upwards [this] with ω hω
    have := sq_eq_zero_iff.mp hω
    linarith [this]
  -- Step 2: all orders simultaneously (countably many), then determinacy
  have hall : ∀ᵐ ω ∂P, ∀ m : ℕ,
      (∫ x, x ^ (k * m) ∂κ ω)
        = r ^ (γ * k * m + C * (1 - β ^ m)) :=
    (ae_all_iff).mpr hae
  filter_upwards [hall] with ω hω
  haveI := hprob ω
  exact theorem3_law_uniqueness_W r γ C β hk hr hC hβ lam hlam (κ ω)
    (hpos ω) (hint ω) hω

/-! ## Theorem 16: finite-state impossibility (growth-contradiction core) -/

/-- Elementary superlinearity: `e^x ≥ x²/4` for `x ≥ 0`. -/
lemma sq_div_four_le_exp {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / 4 ≤ Real.exp x := by
  have h1 : x / 2 + 1 ≤ Real.exp (x / 2) := Real.add_one_le_exp (x / 2)
  have h2 : (x / 2 + 1) * (x / 2 + 1)
      ≤ Real.exp (x / 2) * Real.exp (x / 2) :=
    mul_le_mul h1 h1 (by linarith) (Real.exp_nonneg _)
  have h3 : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
    rw [← Real.exp_add]; ring_nf
  nlinarith [h2, h3, hx]

/-- **Theorem 16, growth-contradiction core**: no function can be the
log-Poisson cumulant `ap + λ(e^{bp} − 1)` (`b < 0`, `λ > 0`) on
`(−∞, 0]` while obeying a linear bound `≤ p·f_min` there — the cumulant
grows superlinearly as `p → −∞`.  This is the analytic heart of the
finite-state impossibility. -/
theorem theorem16_growth_contradiction {a b lam fmin : ℝ}
    (hb : b < 0) (hlam : 0 < lam)
    (h : ∀ p : ℝ, p ≤ 0
      → a * p + lam * (Real.exp (b * p) - 1) ≤ p * fmin) : False := by
  set K : ℝ := lam * b ^ 2 / 4 with hK
  have hKpos : 0 < K := by
    have hbne : b ≠ 0 := hb.ne
    rw [hK]; positivity
  set t : ℝ := max 1 ((|a - fmin| + lam + 1) / K) with htdef
  have ht1 : (1 : ℝ) ≤ t := le_max_left _ _
  have htK : |a - fmin| + lam + 1 ≤ K * t := by
    have := le_max_right (1 : ℝ) ((|a - fmin| + lam + 1) / K)
    calc |a - fmin| + lam + 1
        = (|a - fmin| + lam + 1) / K * K := by field_simp
      _ ≤ t * K := by
          apply mul_le_mul_of_nonneg_right _ hKpos.le
          rw [htdef]; exact le_max_right _ _
      _ = K * t := mul_comm _ _
  -- instantiate the linear bound at p = −t
  have hp := h (-t) (by linarith)
  -- superlinear lower bound for the exponential term
  have hbt : 0 ≤ b * -t := by nlinarith
  have hexp : (b * -t) ^ 2 / 4 ≤ Real.exp (b * -t) :=
    sq_div_four_le_exp hbt
  -- assemble: K·t² ≤ λ·exp(b·(−t)) ≤ λ + t(a − fmin) ≤ |a−fmin|·t + λ
  have hchain : K * t ^ 2 ≤ lam + t * (a - fmin) := by
    have hLHS : K * t ^ 2 = lam * ((b * -t) ^ 2 / 4) := by
      rw [hK]; ring
    have h1 : lam * ((b * -t) ^ 2 / 4) ≤ lam * Real.exp (b * -t) :=
      mul_le_mul_of_nonneg_left hexp hlam.le
    nlinarith [hp, h1, hLHS]
  have habs : t * (a - fmin) ≤ t * |a - fmin| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
  -- but K·t² ≥ (|a−fmin| + λ + 1)·t ≥ |a−fmin|·t + λ + 1
  have hfinal : (|a - fmin| + lam + 1) * t ≤ K * t ^ 2 := by
    have := mul_le_mul_of_nonneg_right htK (by linarith : (0:ℝ) ≤ t)
    nlinarith [this]
  nlinarith [hchain, habs, hfinal, ht1, abs_nonneg (a - fmin)]

/-- **Theorem 16 (Finite-state impossibility), scoped form**: if the
limiting cumulant `Λ` of a finite-state functional agrees with the
log-Poisson cumulant on all of `ℝ` — the conclusion the paper draws
from Perron–Frobenius simplicity and the identity theorem, stated here
as the (unformalized classical) hypothesis — while obeying the
finite-alphabet linear bound `Λ(p) ≤ p·f_min` for `p ≤ 0`, then `False`:
**no finite-state Markov functional satisfies real-`p` A1 with
nontrivial intermittency.** -/
theorem theorem16_scoped {Λ : ℝ → ℝ} {a b lam fmin : ℝ}
    (hb : b < 0) (hlam : 0 < lam)
    (hLP : ∀ p : ℝ, Λ p = a * p + lam * (Real.exp (b * p) - 1))
    (hlin : ∀ p : ℝ, p ≤ 0 → Λ p ≤ p * fmin) : False :=
  theorem16_growth_contradiction hb hlam
    (fun p hp => (hLP p) ▸ hlin p hp)

end Freeburg

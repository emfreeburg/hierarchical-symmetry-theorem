/-
Freeburg formalization — Propagation.lean
Theorem 11 (Unconditional Propagation) of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632.
-/
import Freeburg.PropagationLower

/-!
# Theorem 11: the unconditional propagation upper bound `W₁ ≤ K_∞√ε`

This file formalizes **Theorem 11 (Unconditional Propagation)** of the
paper, at `k = 1` (the same convention Theorem 12 fixes "for
cleanliness"; all jump factors are `u`, not `u^{1/k}`, and `L_1 = 1`):
under the Theorem-10 moment bounds on the tilted measure
`η = (1−u)·ν̃` — variance `∫(u−β)²dη ≤ (1+β)ε` and first moment
`∫|u−β|dη ≤ √((1+β)‖η‖ε)` — the compound-Poisson multiplier of *any*
intensity `ν̃` (finite or infinite activity, no minimum-jump
hypothesis) satisfies `W₁(law W, law W₀) ≤ K_∞ √ε` against the
log-Poisson target of rate `λ = ‖η‖/(1−β)`.

## The construction

The Poisson point process of the paper is realized as countably many
independent finite-activity **layers**: `band β 0 = [0,(1+β)/2]` is the
macroscopic band, `band β (j+1) = (1−h₀/2ʲ, 1−h₀/2^{j+1}]` chops the
small-jump region, and each `ν̃`-restriction has finite mass because
the tilt is bounded below band by band (`isFiniteMeasure_restrict_band`
— this is exactly why infinite activity needs no extra hypotheses).
One layer is `cpModel S ν̂ = Poisson(S) ⊗ ν̂^{⊗ℕ}` (`Measure.infinitePi`
twice); the multiplier is the infinite product across layers, realized
as the `liminf` of the *clamped* partial products, which are `[0,1]`-
valued and globally antitone — so the limit exists everywhere,
measurability is `Measurable.liminf`, and every limit identity is
dominated convergence.  Clamping (`clamp01`) makes every structural
lemma unconditional; the support hypothesis `ν̃(Icoᶜ) = 0` enters only
through trivial a.e. bridges.

## Faithfulness anchors

* `integral_pow_cpLawInf_levy` : `E[W^k] = exp(ak + ∫(u^k−1)dν̃)` — the
  layered law has the compound-Poisson cumulants of the printed triplet
  `(a, 0, ν)`.
* `cpLawInf_unique` : by Hausdorff determinacy (`MomentDeterminacy.lean`)
  those moments
  *pin* the law on `[0, e^a]`, so the construction is canonical.
* `twoAtomCPLaw_eq_cpLawInf` : for the Theorem-12 family the layered
  law *is* `CompoundPoisson.lean`'s two-Poisson pushforward.
* `wald_cpModel` : Wald's identity `E[Σ_{i<N} g(Uᵢ)] = S·E[g(U)]`, in
  the exact form the coupling consumes (deferred from
  `CompoundPoisson.lean`).

## The proof, by legs

`W₁ ≤ Leg A + Leg B + Leg C` (triangle on the common support
`[0, e^a]`):

* **Leg A** (`W1_cpLawInf_layer0_le`, Step 1): dropping all small-jump
  layers costs `e^a·Σ_{j≥1}∫(1−u)dν̃_j = e^a·‖η_small‖ ≤ 4e^aVε/(1−β)²`
  by Chebyshev (`eta_compl_band0_le`) — a near-`1` jump's cost is its
  multiplicative deviation, already `η`-weighted, not the count `1`.
* **Leg B** (`W1_cpLaw_logPoisson_le`, Steps 3–4): sharing the Poisson
  count and pairing every macroscopic factor against the constant `β`
  costs `e^a·∫_{mac}|u−β|dν̃ ≤ 2e^aSε/(1−β)` by the fixed de-tilting
  constant `2/(1−β)` (`setIntegral_band0_abs_le`).
* **Leg C** (`W1_logPoisson_rate_le'`, Step 2): thinning the two
  Poisson counts (superposition coupling) costs
  `e^a(1−β)|λ_mac − λ| ≤ e^a(2Sε/(1−β) + 4Vε/(1−β)²)`
  (`rate_diff_le`).

Total: `theorem11_W1_upper`, `W₁ ≤ e^a(4Sε/(1−β) + 8Vε/(1−β)²)`;
substituting the Theorem-10 bounds and absorbing the `O(ε)` term for
`ε ≤ ε₀ = ‖η‖/(4(1+β))` gives `theorem11_rate_upper`,
`W₁ ≤ K_∞√ε` with `K_∞ = 4e^a(1/(1−β) + 1/(1−β)²)√((1+β)‖η‖)`, and
`theorem11_from_theorem10` chains end-to-end from the cumulant-level
hypotheses (the printed LK triplet with A1 residuals `≤ ε`).

## The capstone

`theorem11_12_theta`: for the Theorem-12 two-atom family the two halves
bracket the same distance,
`c₁√ε(d) ≤ W₁(W_{(d)}, W₀) ≤ 8e^A√(A|ln r|)/(1−β)·√ε(d)` —
the paper's closing claim that **the exact rate is `Θ(√ε)`**, with both
constants explicit and kernel-checked.

## Adaptations and findings (documented deviations)

* **`k = 1` throughout**, matching Theorem 12 and the repo's
  parametrization; the general-`k` statement is the same proof with
  factors `u^{1/k}` and `L_k = (1/k)(β/2)^{(1−k)/k}`.
* **No drift slack**: at `k = 1` conservation is rigid
  (`a_ε = ‖η‖ = λ(1−β) = a₀`), so the paper's `e^{a₀+1}` is here
  `e^{a₀}` — admissible and sharper.
* **Sharpening**: `theorem11_W1_upper` and `theorem11_rate_upper` never
  consume `a = ‖η‖` (their `_ha` argument): the upper bound needs only
  the *shared* drift, not its conservation value — the same flavor as
  `PropagationLower.lean`'s finding that Theorem 12(ii) needs neither
  the matched rate
  nor `A > 0`.
* The paper's thinning coupling is realized as the triangle through
  `logPoisson(λ_mac)`; the bound obtained is the paper's displayed sum
  Step 1 + Step 2 + Step 3 with the paper's Step-2/Step-3 constants and
  a 2× sharper Step 1 (the paper's `2/k` factor and `8Vε/β²` term are
  vacuous at `k = 1`).

Everything in this file is sorry-free.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Nat

namespace Freeburg

/-! ## Clamping to `[0,1]`

The compound-Poisson multiplier is a product of jump factors that live
in `[0,1]` almost surely.  Working with the *clamped* factors makes
every structural lemma about the product model unconditional; the
support hypothesis enters only through the trivial bridge
`clamp01 u = u` a.e. -/

/-- Clamp a real number into the unit interval. -/
noncomputable def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clamp01_mem_Icc (x : ℝ) : clamp01 x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clamp01_eq_self {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    clamp01 x = x := by
  unfold clamp01
  rw [min_eq_right hx.2, max_eq_right hx.1]

theorem measurable_clamp01 : Measurable clamp01 :=
  (continuous_const.max (continuous_const.min continuous_id)).measurable

/-! ## The Poisson mean (Wald's ingredient)

Wald's identity for the coupling cost decomposes into per-coordinate
integrals plus the Poisson mean `E[N] = λ`; this is the form the
deferral from `CompoundPoisson.lean` anticipated. -/

theorem summable_nat_mul_poisson_weight (S : ℝ≥0) :
    Summable (fun n : ℕ => Real.exp (-(S : ℝ)) * (S : ℝ) ^ n / n ! * n) := by
  rw [← summable_nat_add_iff 1]
  refine (((Real.summable_pow_div_factorial (S : ℝ)).mul_left
    (Real.exp (-(S : ℝ)) * (S : ℝ))).congr fun n => ?_)
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hnf : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

theorem integrable_natCast_poissonMeasure (S : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure S) := by
  rw [integrable_poissonMeasure_iff]
  refine (summable_nat_mul_poisson_weight S).congr fun n => ?_
  rw [Real.norm_natCast]

/-- **The Poisson mean**: `E[N] = λ` for `N ~ Poisson(λ)`. -/
theorem integral_natCast_poissonMeasure (S : ℝ≥0) :
    ∫ n, (n : ℝ) ∂(poissonMeasure S) = S := by
  rw [integral_poissonMeasure]
  have hsum : Summable
      (fun n : ℕ => (Real.exp (-(S : ℝ)) * (S : ℝ) ^ n / n !) • (n : ℝ)) := by
    refine (summable_nat_mul_poisson_weight S).congr fun n => ?_
    rw [smul_eq_mul]
  rw [hsum.tsum_eq_zero_add]
  have hterm : ∀ n : ℕ,
      (Real.exp (-(S : ℝ)) * (S : ℝ) ^ (n + 1) / (n + 1)!) • ((n + 1 : ℕ) : ℝ)
        = (S : ℝ) * (Real.exp (-(S : ℝ)) * (S : ℝ) ^ n / n !) := by
    intro n
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hnf : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [smul_eq_mul, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
  rw [tsum_congr hterm, tsum_mul_left, Nat.cast_zero, smul_zero, zero_add,
    (hasSum_one_poissonMeasure S).tsum_eq, mul_one]

/-! ## The single-layer compound-Poisson model

`cpModel S ν̂ = Poisson(S) ⊗ (ν̂)^{⊗ℕ}` carries a Poisson number of
i.i.d. jump factors; `cpLaw a S ν̂` is the law of the multiplier
`W = e^a ∏_{i<N} U_i` (with clamped factors, so every lemma below is
unconditional in the jump law). -/

/-- The truncated product functional `(n, u) ↦ ∏_{i<n} clamp01 (uᵢ)`. -/
noncomputable def prodFnT : ℕ × (ℕ → ℝ) → ℝ :=
  fun p => ∏ i ∈ Finset.range p.1, clamp01 (p.2 i)

theorem measurable_prodFnT : Measurable prodFnT := by
  refine measurable_from_prod_countable_right fun n => ?_
  show Measurable fun y : ℕ → ℝ => ∏ i ∈ Finset.range n, clamp01 (y i)
  exact Finset.measurable_prod _
    fun i _ => measurable_clamp01.comp (measurable_pi_apply i)

theorem prodFnT_mem_Icc (p : ℕ × (ℕ → ℝ)) :
    prodFnT p ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun _ _ => (clamp01_mem_Icc _).1,
    Finset.prod_le_one (fun _ _ => (clamp01_mem_Icc _).1)
      fun _ _ => (clamp01_mem_Icc _).2⟩

/-- The compound-Poisson sample space: a Poisson count of rate `S`
paired with an i.i.d. sequence of jump factors of law `ν̂`. -/
noncomputable def cpModel (S : ℝ≥0) (μp : Measure ℝ) :
    Measure (ℕ × (ℕ → ℝ)) :=
  (poissonMeasure S).prod (Measure.infinitePi fun _ : ℕ => μp)

instance isProbabilityMeasure_cpModel (S : ℝ≥0) (μp : Measure ℝ)
    [IsProbabilityMeasure μp] : IsProbabilityMeasure (cpModel S μp) := by
  unfold cpModel
  infer_instance

/-- The **finite-activity compound-Poisson multiplier law**: the
distribution of `W = e^a ∏_{i<N} U_i` with `N ~ Poisson(S)` and
`U_i` i.i.d. of law `ν̂`. -/
noncomputable def cpLaw (a : ℝ) (S : ℝ≥0) (μp : Measure ℝ) : Measure ℝ :=
  (cpModel S μp).map fun p => Real.exp a * prodFnT p

instance isProbabilityMeasure_cpLaw (a : ℝ) (S : ℝ≥0) (μp : Measure ℝ)
    [IsProbabilityMeasure μp] : IsProbabilityMeasure (cpLaw a S μp) :=
  Measure.isProbabilityMeasure_map
    ((measurable_const.mul measurable_prodFnT).aemeasurable)

/-- The multiplier is bounded by its drift factor: `W ∈ [0, e^a]`
(Lemma 2(i) for the constructed law; unconditional thanks to the
clamped factors). -/
theorem cpLaw_ae_mem_Icc (a : ℝ) (S : ℝ≥0) (μp : Measure ℝ)
    [IsProbabilityMeasure μp] :
    ∀ᵐ w ∂(cpLaw a S μp), w ∈ Set.Icc (0 : ℝ) (Real.exp a) := by
  unfold cpLaw
  refine (MeasureTheory.ae_map_iff
    (measurable_const.mul measurable_prodFnT).aemeasurable
    measurableSet_Icc).mpr ?_
  refine Filter.Eventually.of_forall fun p => ⟨?_, ?_⟩
  · exact mul_nonneg (Real.exp_pos a).le (prodFnT_mem_Icc p).1
  · calc Real.exp a * prodFnT p ≤ Real.exp a * 1 :=
        mul_le_mul_of_nonneg_left (prodFnT_mem_Icc p).2 (Real.exp_pos a).le
    _ = Real.exp a := mul_one _

/-! ## The product-moment workhorse

For any `[0,1]`-valued factor functional `g`, the model integrates the
product `∏_{i<N} g(Uᵢ)` to the compound-Poisson exponential
`exp(S(∫g dν̂ − 1))` — the generating-function computation behind every
moment formula and every per-layer expectation below. -/

theorem integral_prod_cpModel (S : ℝ≥0) (μp : Measure ℝ)
    [IsProbabilityMeasure μp] (g : ℝ → ℝ) (hg : Measurable g)
    (hg01 : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ p, ∏ i ∈ Finset.range p.1, g (p.2 i) ∂(cpModel S μp)
      = Real.exp ((S : ℝ) * ((∫ u, g u ∂μp) - 1)) := by
  have hmeas : Measurable fun p : ℕ × (ℕ → ℝ) =>
      ∏ i ∈ Finset.range p.1, g (p.2 i) := by
    refine measurable_from_prod_countable_right fun n => ?_
    show Measurable fun y : ℕ → ℝ => ∏ i ∈ Finset.range n, g (y i)
    exact Finset.measurable_prod _ fun i _ => hg.comp (measurable_pi_apply i)
  have hint : Integrable
      (fun p : ℕ × (ℕ → ℝ) => ∏ i ∈ Finset.range p.1, g (p.2 i))
      (cpModel S μp) := by
    refine Integrable.mono' (integrable_const 1)
      hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg
      (Finset.prod_nonneg fun i _ => (hg01 _).1)]
    exact Finset.prod_le_one (fun i _ => (hg01 _).1) fun i _ => (hg01 _).2
  unfold cpModel at hint ⊢
  rw [MeasureTheory.integral_prod _ hint]
  -- the inner integral factorizes over the finitely many active coordinates
  have hinner : ∀ n : ℕ,
      ∫ u : ℕ → ℝ, ∏ i ∈ Finset.range n, g (u i)
          ∂(Measure.infinitePi fun _ : ℕ => μp)
        = (∫ x, g x ∂μp) ^ n := by
    intro n
    have hF : Measurable fun v : ((i : (Finset.range n : Finset ℕ)) → ℝ) =>
        ∏ i, g (v i) :=
      Finset.measurable_prod _ fun i _ => hg.comp (measurable_pi_apply i)
    have hcoe : (fun u : ℕ → ℝ => ∏ i ∈ Finset.range n, g (u i))
        = fun u : ℕ → ℝ =>
            ∏ i : (Finset.range n : Finset ℕ), g ((Finset.range n).restrict u i) :=
      funext fun u => (Finset.prod_coe_sort _ _).symm
    rw [hcoe]
    have hmap := integral_map (μ := Measure.infinitePi fun _ : ℕ => μp)
      ((Finset.range n).measurable_restrict (X := fun _ : ℕ => ℝ)).aemeasurable
      (f := fun v : ((i : (Finset.range n : Finset ℕ)) → ℝ) => ∏ i, g (v i))
      hF.aestronglyMeasurable
    rw [← hmap, Measure.infinitePi_map_restrict,
      integral_fintype_prod_eq_pow g, Fintype.card_coe, Finset.card_range]
  calc ∫ n : ℕ, ∫ u : ℕ → ℝ, ∏ i ∈ Finset.range (n, u).1, g ((n, u).2 i)
        ∂(Measure.infinitePi fun _ : ℕ => μp) ∂(poissonMeasure S)
      = ∫ n : ℕ, (∫ x, g x ∂μp) ^ n ∂(poissonMeasure S) := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun n => hinner n)
    _ = Real.exp ((S : ℝ) * ((∫ u, g u ∂μp) - 1)) :=
        integral_pow_poissonMeasure S _

/-- **The compound-Poisson moment formula** for the constructed law:
`E[W^m] = exp(am + S(E[U^m] − 1))` (clamped form; unconditional). -/
theorem integral_pow_cpLaw (a : ℝ) (S : ℝ≥0) (μp : Measure ℝ)
    [IsProbabilityMeasure μp] (m : ℕ) :
    ∫ w, w ^ m ∂(cpLaw a S μp)
      = Real.exp (a * m + (S : ℝ) * ((∫ u, clamp01 u ^ m ∂μp) - 1)) := by
  unfold cpLaw
  rw [integral_map (measurable_const.mul measurable_prodFnT).aemeasurable
    (continuous_pow m).aestronglyMeasurable]
  have hsplit : ∀ p : ℕ × (ℕ → ℝ),
      (Real.exp a * prodFnT p) ^ m
        = Real.exp (a * m)
            * ∏ i ∈ Finset.range p.1, clamp01 (p.2 i) ^ m := by
    intro p
    unfold prodFnT
    rw [mul_pow, ← Real.exp_nat_mul, mul_comm (m : ℝ) a, Finset.prod_pow]
  rw [show (fun p : ℕ × (ℕ → ℝ) => (Real.exp a * prodFnT p) ^ m)
      = fun p => Real.exp (a * m)
          * ∏ i ∈ Finset.range p.1, clamp01 (p.2 i) ^ m from funext hsplit,
    integral_const_mul,
    integral_prod_cpModel S μp _ (measurable_clamp01.pow_const m)
      (fun x => ⟨pow_nonneg (clamp01_mem_Icc x).1 m,
        pow_le_one₀ (clamp01_mem_Icc x).1 (clamp01_mem_Icc x).2⟩),
    ← Real.exp_add]

/-- The moment formula with the clamp removed: under the a.e. support
hypothesis the constructed law has exactly the paper's compound-Poisson
moments over the normalized jump law. -/
theorem integral_pow_cpLaw_of_ae (a : ℝ) (S : ℝ≥0) {μp : Measure ℝ}
    [IsProbabilityMeasure μp] (hsupp : ∀ᵐ u ∂μp, u ∈ Set.Icc (0 : ℝ) 1)
    (m : ℕ) :
    ∫ w, w ^ m ∂(cpLaw a S μp)
      = Real.exp (a * m + (S : ℝ) * ((∫ u, u ^ m ∂μp) - 1)) := by
  have h : ∫ u, clamp01 u ^ m ∂μp = ∫ u, u ^ m ∂μp := by
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with u hu
    rw [clamp01_eq_self hu]
  rw [integral_pow_cpLaw, h]

/-! ## Wald's identity on the model

The expected coupling cost `E[Σ_{i<N} g(Uᵢ)] = S·E[g(U)]` — per-coordinate
integrals against the i.i.d. sequence plus the Poisson mean.  This is the
form of Wald's identity that `CompoundPoisson.lean` deferred here: fixed by
the coupling construction that consumes it. -/

/-- Single-coordinate integration against the i.i.d. sequence. -/
theorem integral_eval_infinitePi (μp : Measure ℝ) [IsProbabilityMeasure μp]
    (g : ℝ → ℝ) (hg : Measurable g) (i : ℕ) :
    ∫ x : ℕ → ℝ, g (x i) ∂(Measure.infinitePi fun _ : ℕ => μp)
      = ∫ u, g u ∂μp := by
  have h := integral_map (μ := Measure.infinitePi fun _ : ℕ => μp)
    (measurable_pi_apply i).aemeasurable (f := g) hg.aestronglyMeasurable
  rw [Measure.infinitePi_map_eval] at h
  exact h.symm

/-- **Wald's identity** for the compound-Poisson model: integrability and
the value `S · ∫g dν̂` of the Poisson-counted i.i.d. sum. -/
theorem wald_cpModel (S : ℝ≥0) (μp : Measure ℝ) [IsProbabilityMeasure μp]
    (g : ℝ → ℝ) (hg : Measurable g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C) :
    Integrable (fun p : ℕ × (ℕ → ℝ) => ∑ i ∈ Finset.range p.1, g (p.2 i))
        (cpModel S μp)
      ∧ ∫ p, ∑ i ∈ Finset.range p.1, g (p.2 i) ∂(cpModel S μp)
          = (S : ℝ) * ∫ u, g u ∂μp := by
  have hmeas : Measurable fun p : ℕ × (ℕ → ℝ) =>
      ∑ i ∈ Finset.range p.1, g (p.2 i) := by
    refine measurable_from_prod_countable_right fun n => ?_
    show Measurable fun y : ℕ → ℝ => ∑ i ∈ Finset.range n, g (y i)
    exact Finset.measurable_sum _ fun i _ => hg.comp (measurable_pi_apply i)
  have hcoord : ∀ i : ℕ, Integrable (fun x : ℕ → ℝ => g (x i))
      (Measure.infinitePi fun _ : ℕ => μp) := by
    intro i
    refine Integrable.mono' (integrable_const C)
      ((hg.comp (measurable_pi_apply i)).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hgC _
  have hslice : ∀ n : ℕ, Integrable
      (fun u : ℕ → ℝ => ∑ i ∈ Finset.range n, g (u i))
      (Measure.infinitePi fun _ : ℕ => μp) :=
    fun n => integrable_finset_sum _ fun i _ => hcoord i
  have hsliceval : ∀ n : ℕ,
      ∫ u : ℕ → ℝ, ∑ i ∈ Finset.range n, g (u i)
          ∂(Measure.infinitePi fun _ : ℕ => μp)
        = (n : ℝ) * ∫ u, g u ∂μp := by
    intro n
    rw [integral_finset_sum _ fun i _ => hcoord i]
    have : ∀ i ∈ Finset.range n,
        ∫ u : ℕ → ℝ, g (u i) ∂(Measure.infinitePi fun _ : ℕ => μp)
          = ∫ u, g u ∂μp :=
      fun i _ => integral_eval_infinitePi μp g hg i
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hgC 0)
  -- integrability over the product model
  have hint : Integrable
      (fun p : ℕ × (ℕ → ℝ) => ∑ i ∈ Finset.range p.1, g (p.2 i))
      (cpModel S μp) := by
    unfold cpModel
    have hasm : AEStronglyMeasurable
        (fun p : ℕ × (ℕ → ℝ) => ∑ i ∈ Finset.range p.1, g (p.2 i))
        ((poissonMeasure S).prod (Measure.infinitePi fun _ : ℕ => μp)) :=
      hmeas.aestronglyMeasurable
    refine (integrable_prod_iff hasm).mpr ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun n => hslice n
    · refine Integrable.mono'
        ((integrable_natCast_poissonMeasure S).const_mul C) ?_ ?_
      · refine StronglyMeasurable.aestronglyMeasurable ?_
        refine (Measurable.stronglyMeasurable ?_)
        exact Measurable.of_discrete
      · refine Filter.Eventually.of_forall fun n => ?_
        have hptw : ∀ u : ℕ → ℝ,
            ‖∑ i ∈ Finset.range n, g (u i)‖ ≤ (n : ℝ) * C := by
          intro u
          calc ‖∑ i ∈ Finset.range n, g (u i)‖
              ≤ ∑ i ∈ Finset.range n, ‖g (u i)‖ := norm_sum_le _ _
            _ ≤ ∑ _i ∈ Finset.range n, C := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [Real.norm_eq_abs]; exact hgC _
            _ = (n : ℝ) * C := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        calc ‖∫ u : ℕ → ℝ, ‖∑ i ∈ Finset.range n, g (u i)‖
              ∂(Measure.infinitePi fun _ : ℕ => μp)‖
            ≤ ((n : ℝ) * C) * (Measure.infinitePi fun _ : ℕ => μp).real
                Set.univ :=
              norm_integral_le_of_norm_le_const
                (Filter.Eventually.of_forall fun u => by
                  rw [norm_norm]; exact hptw u)
          _ = C * (n : ℝ) := by rw [probReal_univ]; ring
  refine ⟨hint, ?_⟩
  unfold cpModel at hint ⊢
  rw [MeasureTheory.integral_prod _ hint]
  calc ∫ n : ℕ, ∫ u : ℕ → ℝ, ∑ i ∈ Finset.range (n, u).1, g ((n, u).2 i)
        ∂(Measure.infinitePi fun _ : ℕ => μp) ∂(poissonMeasure S)
      = ∫ n : ℕ, (n : ℝ) * ∫ u, g u ∂μp ∂(poissonMeasure S) :=
        integral_congr_ae (Filter.Eventually.of_forall fun n => hsliceval n)
    _ = ∫ n : ℕ, (∫ u, g u ∂μp) * (n : ℝ) ∂(poissonMeasure S) :=
        integral_congr_ae (Filter.Eventually.of_forall fun n => mul_comm _ _)
    _ = (∫ u, g u ∂μp) * ∫ n : ℕ, (n : ℝ) ∂(poissonMeasure S) :=
        integral_const_mul _ _
    _ = (S : ℝ) * ∫ u, g u ∂μp := by
        rw [integral_natCast_poissonMeasure, mul_comm]

/-! ## The log-Poisson target in product form -/

/-- For `β > 0` the log-Poisson law is the pushforward of the Poisson
count under `n ↦ e^a βⁿ` — the form the couplings use. -/
theorem logPoissonLaw_eq_pow_map {β : ℝ} (hβ0 : 0 < β) (a : ℝ) (lam : ℝ≥0) :
    logPoissonLaw a (Real.log β) lam
      = (poissonMeasure lam).map fun n : ℕ => Real.exp a * β ^ n := by
  unfold logPoissonLaw
  congr 1
  funext n
  rw [Real.exp_add, mul_comm (Real.log β) (n : ℝ), Real.exp_nat_mul,
    Real.exp_log hβ0]

/-- The ae-bound `|w| ≤ e^a` for the log-Poisson law with `β ∈ (0,1]`. -/
theorem logPoissonLaw_abs_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (a : ℝ) (lam : ℝ≥0) :
    ∀ᵐ w ∂(logPoissonLaw a (Real.log β) lam), |w| ≤ Real.exp a := by
  filter_upwards [logPoissonLaw_ae_mem_Icc a (Real.log β) lam
    (Real.log_nonpos hβ0.le hβ1)] with w hw
  exact abs_le.mpr ⟨by linarith [hw.1, Real.exp_pos a], hw.2⟩

/-- The ae-bound `|w| ≤ e^a` for the constructed compound-Poisson law. -/
theorem cpLaw_abs_le (a : ℝ) (S : ℝ≥0) (μp : Measure ℝ)
    [IsProbabilityMeasure μp] :
    ∀ᵐ w ∂(cpLaw a S μp), |w| ≤ Real.exp a := by
  filter_upwards [cpLaw_ae_mem_Icc a S μp] with w hw
  exact abs_le.mpr ⟨by linarith [hw.1, Real.exp_pos a], hw.2⟩

/-! ## Leg B: the same-count pairing coupling

Sharing the Poisson count and pairing every jump factor against the
constant `β` bounds `W₁(cpLaw, logPoisson)` by the expected jump cost
`S·E|U − β|` — Theorem 11, Steps 3–4, at matched rate. -/

theorem W1_cpLaw_logPoisson_le (a : ℝ) (S : ℝ≥0) (μp : Measure ℝ)
    [IsProbabilityMeasure μp] {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    W1 (cpLaw a S μp) (logPoissonLaw a (Real.log β) S)
      ≤ Real.exp a * ((S : ℝ) * ∫ u, |clamp01 u - β| ∂μp) := by
  have hβm : β ∈ Set.Icc (0 : ℝ) 1 := ⟨hβ0.le, hβ1⟩
  have hFmeas : Measurable fun p : ℕ × (ℕ → ℝ) =>
      Real.exp a * prodFnT p := measurable_const.mul measurable_prodFnT
  have hGmeas : Measurable fun p : ℕ × (ℕ → ℝ) =>
      Real.exp a * β ^ p.1 :=
    measurable_const.mul (measurable_const.pow measurable_fst)
  have hpair : Measurable fun p : ℕ × (ℕ → ℝ) =>
      (Real.exp a * prodFnT p, Real.exp a * β ^ p.1) := hFmeas.prodMk hGmeas
  -- the coupling and its marginals
  have h1 : ((cpModel S μp).map fun p =>
      (Real.exp a * prodFnT p, Real.exp a * β ^ p.1)).map Prod.fst
        = cpLaw a S μp := by
    rw [Measure.map_map measurable_fst hpair]
    rfl
  have h2 : ((cpModel S μp).map fun p =>
      (Real.exp a * prodFnT p, Real.exp a * β ^ p.1)).map Prod.snd
        = logPoissonLaw a (Real.log β) S := by
    rw [Measure.map_map measurable_snd hpair, logPoissonLaw_eq_pow_map hβ0]
    have hcomp : (Prod.snd ∘ fun p : ℕ × (ℕ → ℝ) =>
        (Real.exp a * prodFnT p, Real.exp a * β ^ p.1))
          = (fun n : ℕ => Real.exp a * β ^ n) ∘ Prod.fst := rfl
    rw [hcomp, ← Measure.map_map Measurable.of_discrete measurable_fst]
    unfold cpModel
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  haveI : IsProbabilityMeasure ((cpModel S μp).map fun p =>
      (Real.exp a * prodFnT p, Real.exp a * β ^ p.1)) :=
    Measure.isProbabilityMeasure_map hpair.aemeasurable
  refine (W1_le_of_coupling (cpLaw_abs_le a S μp)
    (logPoissonLaw_abs_le hβ0 hβ1 a S) _ h1 h2).trans ?_
  -- transfer the cost integral to the model space
  rw [integral_map hpair.aemeasurable
    (continuous_fst.sub continuous_snd).abs.aestronglyMeasurable]
  -- the telescoped pointwise cost
  have hpt : ∀ p : ℕ × (ℕ → ℝ),
      |Real.exp a * prodFnT p - Real.exp a * β ^ p.1|
        ≤ Real.exp a * ∑ i ∈ Finset.range p.1, |clamp01 (p.2 i) - β| := by
    intro p
    have htel := abs_prod_sub_prod_le (Finset.range p.1)
      (fun i => clamp01 (p.2 i)) (fun _ => β)
      (fun i _ => clamp01_mem_Icc _) (fun _ _ => hβm)
    rw [Finset.prod_const, Finset.card_range] at htel
    calc |Real.exp a * prodFnT p - Real.exp a * β ^ p.1|
        = Real.exp a * |prodFnT p - β ^ p.1| := by
          rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos a)]
      _ ≤ Real.exp a * ∑ i ∈ Finset.range p.1, |clamp01 (p.2 i) - β| :=
          mul_le_mul_of_nonneg_left htel (Real.exp_pos a).le
  -- Wald for the cost functional
  have habs1 : ∀ x : ℝ, |(|clamp01 x - β|)| ≤ 1 := by
    intro x
    rw [abs_abs]
    have h1 := clamp01_mem_Icc x
    exact abs_le.mpr ⟨by linarith [h1.1, h1.2, hβm.1, hβm.2],
      by linarith [h1.1, h1.2, hβm.1, hβm.2]⟩
  have hwald := wald_cpModel S μp (fun x => |clamp01 x - β|)
    ((measurable_clamp01.sub measurable_const).abs) habs1
  -- integrate the pointwise bound
  have hint1 : Integrable (fun p : ℕ × (ℕ → ℝ) =>
      |Real.exp a * prodFnT p - Real.exp a * β ^ p.1|) (cpModel S μp) := by
    refine Integrable.mono' (integrable_const (2 * Real.exp a))
      ((hFmeas.sub hGmeas).abs).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_abs]
    have hF1 : Real.exp a * prodFnT p ∈ Set.Icc 0 (Real.exp a) :=
      ⟨mul_nonneg (Real.exp_pos a).le (prodFnT_mem_Icc p).1,
        mul_le_of_le_one_right (Real.exp_pos a).le (prodFnT_mem_Icc p).2⟩
    have hG1 : Real.exp a * β ^ p.1 ∈ Set.Icc 0 (Real.exp a) :=
      ⟨mul_nonneg (Real.exp_pos a).le (pow_nonneg hβ0.le _),
        mul_le_of_le_one_right (Real.exp_pos a).le (pow_le_one₀ hβ0.le hβ1)⟩
    exact abs_le.mpr ⟨by linarith [hF1.1, hF1.2, hG1.1, hG1.2],
      by linarith [hF1.1, hF1.2, hG1.1, hG1.2]⟩
  have hint2 : Integrable (fun p : ℕ × (ℕ → ℝ) =>
      Real.exp a * ∑ i ∈ Finset.range p.1, |clamp01 (p.2 i) - β|)
      (cpModel S μp) := hwald.1.const_mul _
  have hwald2 : ∫ p, ∑ i ∈ Finset.range p.1, |clamp01 (p.2 i) - β|
      ∂(cpModel S μp) = (S : ℝ) * ∫ u, |clamp01 u - β| ∂μp := hwald.2
  calc ∫ p, |Real.exp a * prodFnT p - Real.exp a * β ^ p.1| ∂(cpModel S μp)
      ≤ ∫ p, Real.exp a * ∑ i ∈ Finset.range p.1, |clamp01 (p.2 i) - β|
          ∂(cpModel S μp) := integral_mono hint1 hint2 hpt
    _ = Real.exp a * ((S : ℝ) * ∫ u, |clamp01 u - β| ∂μp) := by
        rw [integral_const_mul, hwald2]

/-! ## Leg C: the rate coupling (thinning)

The thinning coupling of two log-Poisson laws shares the smaller count
and pays at most `e^a (1−β)` per excess jump — Theorem 11, Step 2's
rate-comparison cost, via Poisson superposition and the Poisson mean. -/

theorem one_sub_pow_le {β : ℝ} (hβ : β ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    1 - β ^ n ≤ n * (1 - β) := by
  have h := abs_prod_sub_one_le (Finset.range n) (fun _ => β) fun _ _ => hβ
  rw [Finset.prod_const, Finset.card_range] at h
  calc 1 - β ^ n ≤ |β ^ n - 1| := by rw [abs_sub_comm]; exact le_abs_self _
    _ ≤ ∑ _i ∈ Finset.range n, (1 - β) := h
    _ = n * (1 - β) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem W1_logPoisson_rate_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (a : ℝ)
    {l1 l2 : ℝ≥0} (hle : l2 ≤ l1) :
    W1 (logPoissonLaw a (Real.log β) l1) (logPoissonLaw a (Real.log β) l2)
      ≤ Real.exp a * (1 - β) * ((l1 : ℝ) - (l2 : ℝ)) := by
  have hβm : β ∈ Set.Icc (0 : ℝ) 1 := ⟨hβ0.le, hβ1⟩
  have hFmeas : Measurable fun q : ℕ × ℕ => Real.exp a * β ^ (q.1 + q.2) :=
    Measurable.of_discrete
  have hGmeas : Measurable fun q : ℕ × ℕ => Real.exp a * β ^ q.1 :=
    Measurable.of_discrete
  have hpair : Measurable fun q : ℕ × ℕ =>
      (Real.exp a * β ^ (q.1 + q.2), Real.exp a * β ^ q.1) :=
    hFmeas.prodMk hGmeas
  have h1 : (((poissonMeasure l2).prod (poissonMeasure (l1 - l2))).map
      fun q : ℕ × ℕ =>
        (Real.exp a * β ^ (q.1 + q.2), Real.exp a * β ^ q.1)).map Prod.fst
        = logPoissonLaw a (Real.log β) l1 := by
    rw [Measure.map_map measurable_fst hpair]
    have hcomp : (Prod.fst ∘ fun q : ℕ × ℕ =>
        (Real.exp a * β ^ (q.1 + q.2), Real.exp a * β ^ q.1))
          = (fun n : ℕ => Real.exp a * β ^ n)
              ∘ (fun q : ℕ × ℕ => q.1 + q.2) := rfl
    rw [hcomp, ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
      poissonMeasure_prod_map_add, add_tsub_cancel_of_le hle,
      logPoissonLaw_eq_pow_map hβ0]
  have h2 : (((poissonMeasure l2).prod (poissonMeasure (l1 - l2))).map
      fun q : ℕ × ℕ =>
        (Real.exp a * β ^ (q.1 + q.2), Real.exp a * β ^ q.1)).map Prod.snd
        = logPoissonLaw a (Real.log β) l2 := by
    rw [Measure.map_map measurable_snd hpair, logPoissonLaw_eq_pow_map hβ0]
    have hcomp : (Prod.snd ∘ fun q : ℕ × ℕ =>
        (Real.exp a * β ^ (q.1 + q.2), Real.exp a * β ^ q.1))
          = (fun n : ℕ => Real.exp a * β ^ n) ∘ Prod.fst := rfl
    rw [hcomp, ← Measure.map_map Measurable.of_discrete measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul]
  haveI : IsProbabilityMeasure
      (((poissonMeasure l2).prod (poissonMeasure (l1 - l2))).map
        fun q : ℕ × ℕ =>
          (Real.exp a * β ^ (q.1 + q.2), Real.exp a * β ^ q.1)) :=
    Measure.isProbabilityMeasure_map hpair.aemeasurable
  refine (W1_le_of_coupling (logPoissonLaw_abs_le hβ0 hβ1 a l1)
    (logPoissonLaw_abs_le hβ0 hβ1 a l2) _ h1 h2).trans ?_
  rw [integral_map hpair.aemeasurable
    (continuous_fst.sub continuous_snd).abs.aestronglyMeasurable]
  -- pointwise: the excess jumps cost at most (1−β) each
  have hpt : ∀ q : ℕ × ℕ,
      |Real.exp a * β ^ (q.1 + q.2) - Real.exp a * β ^ q.1|
        ≤ Real.exp a * (1 - β) * (q.2 : ℝ) := by
    intro q
    have hb1 : β ^ q.1 ≤ 1 := pow_le_one₀ hβ0.le hβ1
    have hb2 : β ^ q.2 ≤ 1 := pow_le_one₀ hβ0.le hβ1
    have hsplit : Real.exp a * β ^ (q.1 + q.2) - Real.exp a * β ^ q.1
        = -(Real.exp a * β ^ q.1 * (1 - β ^ q.2)) := by
      rw [pow_add]; ring
    rw [hsplit, abs_neg, abs_of_nonneg (mul_nonneg
      (mul_nonneg (Real.exp_pos a).le (pow_nonneg hβ0.le _))
      (by linarith))]
    have h5 : Real.exp a * β ^ q.1 * (1 - β ^ q.2)
        ≤ Real.exp a * (1 - β ^ q.2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (Real.exp_pos a).le hb1) (by linarith)
    have h6 : Real.exp a * (1 - β ^ q.2)
        ≤ Real.exp a * ((q.2 : ℝ) * (1 - β)) :=
      mul_le_mul_of_nonneg_left (one_sub_pow_le hβm q.2) (Real.exp_pos a).le
    exact (h5.trans h6).trans (le_of_eq (by ring))
  -- the excess count integrates to the rate difference
  have hsnd : Integrable (fun q : ℕ × ℕ => ((q.2 : ℕ) : ℝ))
      ((poissonMeasure l2).prod (poissonMeasure (l1 - l2))) := by
    have hmapint : Integrable (fun n : ℕ => (n : ℝ))
        (((poissonMeasure l2).prod (poissonMeasure (l1 - l2))).map
          Prod.snd) := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
      exact integrable_natCast_poissonMeasure _
    exact (integrable_map_measure
      (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).aestronglyMeasurable
      measurable_snd.aemeasurable).mp hmapint
  have hsndval : ∫ q : ℕ × ℕ, ((q.2 : ℕ) : ℝ)
      ∂((poissonMeasure l2).prod (poissonMeasure (l1 - l2)))
        = (l1 : ℝ) - (l2 : ℝ) := by
    have h := integral_map (μ := (poissonMeasure l2).prod
        (poissonMeasure (l1 - l2)))
      measurable_snd.aemeasurable
      (f := fun n : ℕ => (n : ℝ))
      (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).aestronglyMeasurable
    rw [Measure.map_snd_prod, measure_univ, one_smul,
      integral_natCast_poissonMeasure] at h
    rw [← h, NNReal.coe_sub hle]
  have hint1 : Integrable (fun q : ℕ × ℕ =>
      |Real.exp a * β ^ (q.1 + q.2) - Real.exp a * β ^ q.1|)
      ((poissonMeasure l2).prod (poissonMeasure (l1 - l2))) := by
    refine Integrable.mono' (integrable_const (2 * Real.exp a))
      ((hFmeas.sub hGmeas).abs).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun q => ?_
    rw [Real.norm_eq_abs, abs_abs]
    have h1 : (0 : ℝ) ≤ Real.exp a * β ^ (q.1 + q.2) := by positivity
    have h2 : Real.exp a * β ^ (q.1 + q.2) ≤ Real.exp a :=
      mul_le_of_le_one_right (Real.exp_pos a).le (pow_le_one₀ hβ0.le hβ1)
    have h3 : (0 : ℝ) ≤ Real.exp a * β ^ q.1 := by positivity
    have h4 : Real.exp a * β ^ q.1 ≤ Real.exp a :=
      mul_le_of_le_one_right (Real.exp_pos a).le (pow_le_one₀ hβ0.le hβ1)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc ∫ q : ℕ × ℕ, |Real.exp a * β ^ (q.1 + q.2) - Real.exp a * β ^ q.1|
        ∂((poissonMeasure l2).prod (poissonMeasure (l1 - l2)))
      ≤ ∫ q : ℕ × ℕ, Real.exp a * (1 - β) * (q.2 : ℝ)
          ∂((poissonMeasure l2).prod (poissonMeasure (l1 - l2))) :=
        integral_mono hint1 (hsnd.const_mul _) hpt
    _ = Real.exp a * (1 - β) * ((l1 : ℝ) - (l2 : ℝ)) := by
        rw [integral_const_mul, hsndval]

/-- Leg C in symmetric form: the rate cost is `e^a (1−β) |λ₁ − λ₂|`. -/
theorem W1_logPoisson_rate_le' {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (a : ℝ)
    (l1 l2 : ℝ≥0) :
    W1 (logPoissonLaw a (Real.log β) l1) (logPoissonLaw a (Real.log β) l2)
      ≤ Real.exp a * (1 - β) * |(l1 : ℝ) - (l2 : ℝ)| := by
  rcases le_total l2 l1 with h | h
  · refine (W1_logPoisson_rate_le hβ0 hβ1 a h).trans (le_of_eq ?_)
    rw [abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))]
  · rw [W1_comm]
    refine (W1_logPoisson_rate_le hβ0 hβ1 a h).trans (le_of_eq ?_)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))]

/-! ## Layers: normalizing a finite intensity measure

A layer is a finite intensity measure `m`; its compound-Poisson model is
`cpModel (layerRate m) (layerProb m)`.  Layers of zero mass get the
harmless jump law `δ₁` (a factor `1` changes nothing), keeping every
layer a probability space. -/

open Classical in
/-- The normalized jump law of a finite intensity measure (`δ₁` if the
mass vanishes). -/
noncomputable def layerProb (m : Measure ℝ) : Measure ℝ :=
  if m Set.univ = 0 then Measure.dirac 1 else (m Set.univ)⁻¹ • m

/-- The total mass of the intensity measure, as the layer's Poisson rate. -/
noncomputable def layerRate (m : Measure ℝ) : ℝ≥0 :=
  (m Set.univ).toNNReal

instance isProbabilityMeasure_layerProb (m : Measure ℝ)
    [IsFiniteMeasure m] : IsProbabilityMeasure (layerProb m) := by
  unfold layerProb
  split_ifs with h
  · infer_instance
  · haveI : NeZero m := ⟨by
      intro h0
      exact h (by rw [h0]; rfl)⟩
    infer_instance

theorem layerProb_ae_mem {m : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (h1 : (1 : ℝ) ∈ s) (hsupp : ∀ᵐ u ∂m, u ∈ s) :
    ∀ᵐ u ∂(layerProb m), u ∈ s := by
  unfold layerProb
  split_ifs with h
  · exact (ae_dirac_iff hs).mpr h1
  · exact Measure.ae_smul_measure hsupp _

/-- The defining bridge: rates and normalized integrals recombine to
integrals against the intensity measure. -/
theorem layerRate_mul_integral (m : Measure ℝ) [IsFiniteMeasure m]
    (g : ℝ → ℝ) :
    (layerRate m : ℝ) * ∫ u, g u ∂(layerProb m) = ∫ u, g u ∂m := by
  unfold layerRate layerProb
  split_ifs with h
  · have hm : m = 0 := Measure.measure_univ_eq_zero.mp h
    rw [hm]
    simp
  · have hne_top : m Set.univ ≠ ⊤ := measure_ne_top m _
    have hcoe : ((m Set.univ).toNNReal : ℝ) = (m Set.univ).toReal := rfl
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv, hcoe,
      ← mul_assoc, mul_inv_cancel₀
        (ENNReal.toReal_ne_zero.mpr ⟨h, hne_top⟩), one_mul]

/-- The combined form consumed by the moment formulas:
`S·(∫g dν̂ − 1) = ∫g dm − ‖m‖`. -/
theorem layerRate_mul_integral_sub_one (m : Measure ℝ) [IsFiniteMeasure m]
    (g : ℝ → ℝ) :
    (layerRate m : ℝ) * ((∫ u, g u ∂(layerProb m)) - 1)
      = (∫ u, g u ∂m) - m.real Set.univ := by
  rw [mul_sub, layerRate_mul_integral m g, mul_one]
  rfl

/-- Bounded measurable functions are integrable against a finite measure
— the form used for the per-layer integrands. -/
theorem integrable_of_bounded_finite {m : Measure ℝ} [IsFiniteMeasure m]
    {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C) :
    Integrable g m := by
  refine Integrable.mono' (integrable_const C) hg.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hgC x

/-! ## The layered (infinite-activity) model

The Poisson point process of an infinite-mass Lévy measure is realized
as countably many independent finite-activity layers; the multiplier is
the a.s.-monotone infinite product across layers.  No point-process
theory is needed: `Measure.infinitePi` over the layer models carries the
construction, and the clamped partial products are globally antitone in
the layer count, so the infinite product is their `liminf`. -/

/-- One layer's compound-Poisson sample space. -/
noncomputable def layerModel (m : Measure ℝ) : Measure (ℕ × (ℕ → ℝ)) :=
  cpModel (layerRate m) (layerProb m)

instance isProbabilityMeasure_layerModel (m : Measure ℝ)
    [IsFiniteMeasure m] : IsProbabilityMeasure (layerModel m) := by
  unfold layerModel
  infer_instance

/-- The layered sample space: independent copies of the layer models. -/
noncomputable def cpModelInf (ms : ℕ → Measure ℝ) :
    Measure (Π _ : ℕ, ℕ × (ℕ → ℝ)) :=
  Measure.infinitePi fun j => layerModel (ms j)

instance isProbabilityMeasure_cpModelInf (ms : ℕ → Measure ℝ)
    [∀ j, IsFiniteMeasure (ms j)] :
    IsProbabilityMeasure (cpModelInf ms) := by
  unfold cpModelInf
  infer_instance

/-- The product of the first `J+1` layer factors. -/
noncomputable def partialProd (ω : Π _ : ℕ, ℕ × (ℕ → ℝ)) (J : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (J + 1), prodFnT (ω j)

/-- The infinite multiplicative cascade across all layers, as the
`liminf` of the partial products (which is their genuine limit:
they are `[0,1]`-valued and antitone). -/
noncomputable def prodInf (ω : Π _ : ℕ, ℕ × (ℕ → ℝ)) : ℝ :=
  Filter.liminf (fun J => partialProd ω J) Filter.atTop

theorem partialProd_mem_Icc (ω : Π _ : ℕ, ℕ × (ℕ → ℝ)) (J : ℕ) :
    partialProd ω J ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun j _ => (prodFnT_mem_Icc (ω j)).1,
    Finset.prod_le_one (fun j _ => (prodFnT_mem_Icc (ω j)).1)
      fun j _ => (prodFnT_mem_Icc (ω j)).2⟩

theorem antitone_partialProd (ω : Π _ : ℕ, ℕ × (ℕ → ℝ)) :
    Antitone (partialProd ω) := by
  refine antitone_nat_of_succ_le fun J => ?_
  unfold partialProd
  rw [Finset.prod_range_succ]
  exact mul_le_of_le_one_right
    (Finset.prod_nonneg fun j _ => (prodFnT_mem_Icc (ω j)).1)
    (prodFnT_mem_Icc (ω (J + 1))).2

theorem tendsto_partialProd (ω : Π _ : ℕ, ℕ × (ℕ → ℝ)) :
    Filter.Tendsto (partialProd ω) Filter.atTop (nhds (prodInf ω)) := by
  have hbdd : BddBelow (Set.range (partialProd ω)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨J, rfl⟩
    exact (partialProd_mem_Icc ω J).1
  have h := tendsto_atTop_ciInf (antitone_partialProd ω) hbdd
  have hval : prodInf ω = ⨅ J, partialProd ω J := h.liminf_eq
  rwa [hval]

theorem prodInf_mem_Icc (ω : Π _ : ℕ, ℕ × (ℕ → ℝ)) :
    prodInf ω ∈ Set.Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (tendsto_partialProd ω)
    (Filter.Eventually.of_forall fun J => partialProd_mem_Icc ω J)

theorem prodInf_le_partialProd (ω : Π _ : ℕ, ℕ × (ℕ → ℝ)) (J : ℕ) :
    prodInf ω ≤ partialProd ω J :=
  le_of_tendsto (tendsto_partialProd ω)
    (Filter.eventually_atTop.mpr
      ⟨J, fun _ hK => antitone_partialProd ω hK⟩)

theorem measurable_partialProd (J : ℕ) :
    Measurable fun ω : Π _ : ℕ, ℕ × (ℕ → ℝ) => partialProd ω J :=
  Finset.measurable_prod _
    fun j _ => measurable_prodFnT.comp (measurable_pi_apply j)

theorem measurable_prodInf : Measurable prodInf :=
  Measurable.liminf fun J => measurable_partialProd J

/-- The **infinite-activity compound-Poisson multiplier law**: the
distribution of `W = e^a ∏_j P_j` over independent finite-activity
layers of intensities `ms j`. -/
noncomputable def cpLawInf (a : ℝ) (ms : ℕ → Measure ℝ) : Measure ℝ :=
  (cpModelInf ms).map fun ω => Real.exp a * prodInf ω

instance isProbabilityMeasure_cpLawInf (a : ℝ) (ms : ℕ → Measure ℝ)
    [∀ j, IsFiniteMeasure (ms j)] :
    IsProbabilityMeasure (cpLawInf a ms) :=
  Measure.isProbabilityMeasure_map
    (measurable_const.mul measurable_prodInf).aemeasurable

theorem cpLawInf_ae_mem_Icc (a : ℝ) (ms : ℕ → Measure ℝ)
    [∀ j, IsFiniteMeasure (ms j)] :
    ∀ᵐ w ∂(cpLawInf a ms), w ∈ Set.Icc (0 : ℝ) (Real.exp a) := by
  unfold cpLawInf
  refine (MeasureTheory.ae_map_iff
    (measurable_const.mul measurable_prodInf).aemeasurable
    measurableSet_Icc).mpr ?_
  refine Filter.Eventually.of_forall fun ω => ⟨?_, ?_⟩
  · exact mul_nonneg (Real.exp_pos a).le (prodInf_mem_Icc ω).1
  · exact mul_le_of_le_one_right (Real.exp_pos a).le (prodInf_mem_Icc ω).2

theorem cpLawInf_abs_le (a : ℝ) (ms : ℕ → Measure ℝ)
    [∀ j, IsFiniteMeasure (ms j)] :
    ∀ᵐ w ∂(cpLawInf a ms), |w| ≤ Real.exp a := by
  filter_upwards [cpLawInf_ae_mem_Icc a ms] with w hw
  exact abs_le.mpr ⟨by linarith [hw.1, Real.exp_pos a], hw.2⟩

/-! ## Finite-layer factorization and the cumulant certificate -/

/-- Integrals of finite products of per-layer functionals factorize over
the layered model (independence of the layers). -/
theorem integral_finprod_cpModelInf (ms : ℕ → Measure ℝ)
    [∀ j, IsFiniteMeasure (ms j)] (K : ℕ)
    (h : ℕ → (ℕ × (ℕ → ℝ)) → ℝ) (hmeas : ∀ j, Measurable (h j)) :
    ∫ ω, ∏ j ∈ Finset.range K, h j (ω j) ∂(cpModelInf ms)
      = ∏ j ∈ Finset.range K, ∫ p, h j p ∂(layerModel (ms j)) := by
  unfold cpModelInf
  have hF : Measurable fun v : ((j : (Finset.range K : Finset ℕ)) →
      ℕ × (ℕ → ℝ)) =>
        ∏ j : (Finset.range K : Finset ℕ), h (↑j) (v j) :=
    Finset.measurable_prod _
      fun j _ => (hmeas (↑j)).comp (measurable_pi_apply j)
  have hcoe : (fun ω : Π _ : ℕ, ℕ × (ℕ → ℝ) =>
      ∏ j ∈ Finset.range K, h j (ω j))
      = fun ω => ∏ j : (Finset.range K : Finset ℕ),
          h (↑j) ((Finset.range K).restrict ω j) :=
    funext fun ω => (Finset.prod_coe_sort _ _).symm
  rw [hcoe]
  have hmap := integral_map
    (μ := Measure.infinitePi fun j => layerModel (ms j))
    ((Finset.range K).measurable_restrict
      (X := fun _ : ℕ => ℕ × (ℕ → ℝ))).aemeasurable
    (f := fun v : ((j : (Finset.range K : Finset ℕ)) → ℕ × (ℕ → ℝ)) =>
      ∏ j : (Finset.range K : Finset ℕ), h (↑j) (v j))
    hF.aestronglyMeasurable
  have hpi : ∫ v : ((j : (Finset.range K : Finset ℕ)) → ℕ × (ℕ → ℝ)),
      ∏ j : (Finset.range K : Finset ℕ), h (↑j) (v j)
        ∂(Measure.pi fun j : (Finset.range K : Finset ℕ) =>
          layerModel (ms (↑j)))
      = ∏ j : (Finset.range K : Finset ℕ),
          ∫ p, h (↑j) p ∂(layerModel (ms (↑j))) :=
    integral_fintype_prod_eq_prod
      (fun j : (Finset.range K : Finset ℕ) => h (↑j))
  rw [← hmap, Measure.infinitePi_map_restrict, hpi]
  exact Finset.prod_coe_sort (Finset.range K)
    fun n => ∫ p, h n p ∂(layerModel (ms n))

/-- The per-layer moment factor: `E[P_j^k] = exp(S_j(E[U^k] − 1))`. -/
theorem integral_pow_layerModel (m : Measure ℝ) [IsFiniteMeasure m]
    (k : ℕ) :
    ∫ p, prodFnT p ^ k ∂(layerModel m)
      = Real.exp ((layerRate m : ℝ)
          * ((∫ u, clamp01 u ^ k ∂(layerProb m)) - 1)) := by
  have hsplit : (fun p : ℕ × (ℕ → ℝ) => prodFnT p ^ k)
      = fun p => ∏ i ∈ Finset.range p.1, clamp01 (p.2 i) ^ k := by
    funext p
    unfold prodFnT
    rw [Finset.prod_pow]
  unfold layerModel
  rw [hsplit]
  exact integral_prod_cpModel _ _ _ (measurable_clamp01.pow_const k)
    fun x => ⟨pow_nonneg (clamp01_mem_Icc x).1 _,
      pow_le_one₀ (clamp01_mem_Icc x).1 (clamp01_mem_Icc x).2⟩

/-- The per-layer moment factor against the intensity measure:
`E[P_j^k] = exp(∫(u^k − 1) dm_j)` (clamped form). -/
theorem integral_pow_layerModel' (m : Measure ℝ) [IsFiniteMeasure m]
    (k : ℕ) :
    ∫ p, prodFnT p ^ k ∂(layerModel m)
      = Real.exp (∫ u, (clamp01 u ^ k - 1) ∂m) := by
  rw [integral_pow_layerModel]
  congr 1
  have hint : Integrable (fun u => clamp01 u ^ k) m := by
    refine integrable_of_bounded_finite (measurable_clamp01.pow_const k)
      (C := 1) fun x => ?_
    rw [abs_of_nonneg (pow_nonneg (clamp01_mem_Icc x).1 _)]
    exact pow_le_one₀ (clamp01_mem_Icc x).1 (clamp01_mem_Icc x).2
  rw [layerRate_mul_integral_sub_one m _,
    integral_sub hint (integrable_const 1), integral_const,
    measureReal_def, smul_eq_mul, mul_one]

/-- The single-layer expected factor never exceeds `1` and dominates
`1 − ∫(1−u) dm` (the `1−e^{−x} ≤ x` estimate). -/
theorem integral_prodFnT_layerModel_bounds (m : Measure ℝ)
    [IsFiniteMeasure m] :
    1 - ∫ u, (1 - clamp01 u) ∂m
        ≤ ∫ p, prodFnT p ∂(layerModel m)
      ∧ ∫ p, prodFnT p ∂(layerModel m) ≤ 1 := by
  have h := integral_pow_layerModel' m 1
  simp only [pow_one] at h
  have hkey : ∫ u, (clamp01 u - 1) ∂m = -(∫ u, (1 - clamp01 u) ∂m) := by
    rw [← integral_neg]
    congr 1
    funext u
    ring
  have hnn : 0 ≤ ∫ u, (1 - clamp01 u) ∂m := by
    refine integral_nonneg fun u => ?_
    show (0 : ℝ) ≤ 1 - clamp01 u
    linarith [(clamp01_mem_Icc u).2]
  constructor
  · rw [h, hkey]
    have := Real.add_one_le_exp (-(∫ u, (1 - clamp01 u) ∂m))
    linarith
  · rw [h, hkey]
    refine Real.exp_le_one_iff.mpr ?_
    linarith

/-! ## The cumulant certificate for the layered law

`E[W^k] = exp(ak + Σ_j ∫(u^k − 1) dm_j)` — the compound-Poisson
cumulant form over the total intensity `Σ_j m_j`, certifying that the
layered construction realizes the paper's infinite-activity multiplier
(by Hausdorff determinacy this pins the law; see
`cpLawInf_unique`). -/

theorem summable_layer_cumulants {ms : ℕ → Measure ℝ}
    [∀ j, IsFiniteMeasure (ms j)]
    (hsum : Summable fun j => ∫ u, (1 - clamp01 u) ∂(ms j)) (k : ℕ) :
    Summable fun j => ∫ u, (clamp01 u ^ k - 1) ∂(ms j) := by
  rw [← summable_neg_iff]
  have hneg : ∀ j, -∫ u, (clamp01 u ^ k - 1) ∂(ms j)
      = ∫ u, (1 - clamp01 u ^ k) ∂(ms j) := by
    intro j
    rw [← integral_neg]
    congr 1
    funext u
    ring
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    (hsum.mul_left (k : ℝ))
  · rw [hneg j]
    refine integral_nonneg fun u => ?_
    show (0 : ℝ) ≤ 1 - clamp01 u ^ k
    linarith [pow_le_one₀ (clamp01_mem_Icc u).1 (clamp01_mem_Icc u).2
      (n := k)]
  · rw [hneg j]
    have hint1 : Integrable (fun u => 1 - clamp01 u ^ k) (ms j) := by
      refine integrable_of_bounded_finite
        ((measurable_const.sub (measurable_clamp01.pow_const k))) (C := 1)
        fun x => ?_
      have h1 := (clamp01_mem_Icc x).1
      have h2 := (clamp01_mem_Icc x).2
      have h3 := pow_le_one₀ h1 h2 (n := k)
      have h4 := pow_nonneg h1 k
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hint2 : Integrable (fun u => (k : ℝ) * (1 - clamp01 u)) (ms j) := by
      refine Integrable.const_mul ?_ _
      refine integrable_of_bounded_finite
        (measurable_const.sub measurable_clamp01) (C := 1) fun x => ?_
      have h1 := (clamp01_mem_Icc x).1
      have h2 := (clamp01_mem_Icc x).2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    refine (integral_mono hint1 hint2 fun u => ?_).trans (le_of_eq ?_)
    · have h1 := (clamp01_mem_Icc u).1
      have h2 := (clamp01_mem_Icc u).2
      have := one_sub_pow_le ⟨h1, h2⟩ k
      linarith
    · rw [integral_const_mul]

/-- **The cumulant certificate**: the layered law has the printed
compound-Poisson moments `E[W^k] = exp(ak + Σ_j ∫(u^k−1) dm_j)`. -/
theorem integral_pow_cpLawInf (a : ℝ) (ms : ℕ → Measure ℝ)
    [∀ j, IsFiniteMeasure (ms j)]
    (hsum : Summable fun j => ∫ u, (1 - clamp01 u) ∂(ms j)) (k : ℕ) :
    ∫ w, w ^ k ∂(cpLawInf a ms)
      = Real.exp (a * k + ∑' j, ∫ u, (clamp01 u ^ k - 1) ∂(ms j)) := by
  unfold cpLawInf
  rw [integral_map (measurable_const.mul measurable_prodInf).aemeasurable
    (continuous_pow k).aestronglyMeasurable]
  have hsplit : (fun ω : Π _ : ℕ, ℕ × (ℕ → ℝ) =>
      (Real.exp a * prodInf ω) ^ k)
      = fun ω => Real.exp (a * k) * prodInf ω ^ k := by
    funext ω
    rw [mul_pow, ← Real.exp_nat_mul, mul_comm (k : ℝ) a]
  rw [hsplit, integral_const_mul]
  -- DCT: the partial products converge boundedly to the infinite product
  have hDCT : Filter.Tendsto
      (fun J => ∫ ω, partialProd ω J ^ k ∂(cpModelInf ms)) Filter.atTop
      (nhds (∫ ω, prodInf ω ^ k ∂(cpModelInf ms))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ => (1 : ℝ))
      (fun J => ((measurable_partialProd J).pow_const k).aestronglyMeasurable)
      (integrable_const 1) (fun J => ?_) ?_
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg
        (pow_nonneg (partialProd_mem_Icc ω J).1 _)]
      exact pow_le_one₀ (partialProd_mem_Icc ω J).1
        (partialProd_mem_Icc ω J).2
    · exact Filter.Eventually.of_forall fun ω =>
        (tendsto_partialProd ω).pow k
  -- the partial-product integrals in closed form
  have hval : ∀ J : ℕ, ∫ ω, partialProd ω J ^ k ∂(cpModelInf ms)
      = Real.exp (∑ j ∈ Finset.range (J + 1),
          ∫ u, (clamp01 u ^ k - 1) ∂(ms j)) := by
    intro J
    have hsplit2 : (fun ω : Π _ : ℕ, ℕ × (ℕ → ℝ) => partialProd ω J ^ k)
        = fun ω => ∏ j ∈ Finset.range (J + 1),
            (fun p => prodFnT p ^ k) (ω j) := by
      funext ω
      unfold partialProd
      rw [Finset.prod_pow]
    rw [hsplit2, integral_finprod_cpModelInf ms (J + 1) _
      (fun j => measurable_prodFnT.pow_const k)]
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => integral_pow_layerModel' (ms j) k
  -- pass to the limit through the cumulant series
  have hsum_k := summable_layer_cumulants hsum k
  have hlim : Filter.Tendsto
      (fun J => Real.exp (∑ j ∈ Finset.range (J + 1),
        ∫ u, (clamp01 u ^ k - 1) ∂(ms j))) Filter.atTop
      (nhds (Real.exp (∑' j, ∫ u, (clamp01 u ^ k - 1) ∂(ms j)))) := by
    refine (Real.continuous_exp.continuousAt.tendsto.comp ?_)
    exact (hsum_k.hasSum.tendsto_sum_nat).comp
      (Filter.tendsto_add_atTop_nat 1)
  have huniq : ∫ ω, prodInf ω ^ k ∂(cpModelInf ms)
      = Real.exp (∑' j, ∫ u, (clamp01 u ^ k - 1) ∂(ms j)) := by
    refine tendsto_nhds_unique hDCT ?_
    have : (fun J => ∫ ω, partialProd ω J ^ k ∂(cpModelInf ms))
        = fun J => Real.exp (∑ j ∈ Finset.range (J + 1),
            ∫ u, (clamp01 u ^ k - 1) ∂(ms j)) := funext hval
    rw [this]
    exact hlim
  rw [huniq, ← Real.exp_add]

/-! ## Leg A: removing the small-jump layers

Dropping every layer beyond the zeroth couples the layered law with the
single-layer (macroscopic) law at total cost
`e^a Σ_{j≥1} ∫(1−u) dm_j = e^a‖η_small‖` — Theorem 11, Step 1: a
near-`1` jump's cost is its multiplicative deviation, already
`η`-weighted, not the count. -/

theorem W1_cpLawInf_layer0_le (a : ℝ) (ms : ℕ → Measure ℝ)
    [∀ j, IsFiniteMeasure (ms j)]
    (hsum : Summable fun j => ∫ u, (1 - clamp01 u) ∂(ms j)) :
    W1 (cpLawInf a ms) (cpLaw a (layerRate (ms 0)) (layerProb (ms 0)))
      ≤ Real.exp a * ∑' j, ∫ u, (1 - clamp01 u) ∂(ms (j + 1)) := by
  have hF : Measurable fun ω : Π _ : ℕ, ℕ × (ℕ → ℝ) =>
      Real.exp a * prodInf ω := measurable_const.mul measurable_prodInf
  have hG : Measurable fun ω : Π _ : ℕ, ℕ × (ℕ → ℝ) =>
      Real.exp a * prodFnT (ω 0) :=
    measurable_const.mul (measurable_prodFnT.comp (measurable_pi_apply 0))
  have hpair : Measurable fun ω : Π _ : ℕ, ℕ × (ℕ → ℝ) =>
      (Real.exp a * prodInf ω, Real.exp a * prodFnT (ω 0)) := hF.prodMk hG
  have h1 : ((cpModelInf ms).map fun ω =>
      (Real.exp a * prodInf ω, Real.exp a * prodFnT (ω 0))).map Prod.fst
        = cpLawInf a ms := by
    rw [Measure.map_map measurable_fst hpair]
    rfl
  have h2 : ((cpModelInf ms).map fun ω =>
      (Real.exp a * prodInf ω, Real.exp a * prodFnT (ω 0))).map Prod.snd
        = cpLaw a (layerRate (ms 0)) (layerProb (ms 0)) := by
    rw [Measure.map_map measurable_snd hpair]
    have hcomp : (Prod.snd ∘ fun ω : Π _ : ℕ, ℕ × (ℕ → ℝ) =>
        (Real.exp a * prodInf ω, Real.exp a * prodFnT (ω 0)))
          = (fun p : ℕ × (ℕ → ℝ) => Real.exp a * prodFnT p)
              ∘ (fun ω => ω 0) := rfl
    rw [hcomp, ← Measure.map_map (measurable_const.mul measurable_prodFnT)
      (measurable_pi_apply 0)]
    unfold cpModelInf
    rw [Measure.infinitePi_map_eval]
    rfl
  haveI : IsProbabilityMeasure ((cpModelInf ms).map fun ω =>
      (Real.exp a * prodInf ω, Real.exp a * prodFnT (ω 0))) :=
    Measure.isProbabilityMeasure_map hpair.aemeasurable
  refine (W1_le_of_coupling (cpLawInf_abs_le a ms)
    (cpLaw_abs_le a _ _) _ h1 h2).trans ?_
  rw [integral_map hpair.aemeasurable
    (continuous_fst.sub continuous_snd).abs.aestronglyMeasurable]
  -- the cost integrand in closed monotone form
  have hpt : ∀ ω : Π _ : ℕ, ℕ × (ℕ → ℝ),
      |Real.exp a * prodInf ω - Real.exp a * prodFnT (ω 0)|
        = Real.exp a * (prodFnT (ω 0) - prodInf ω) := by
    intro ω
    have hle : prodInf ω ≤ prodFnT (ω 0) := by
      have h := prodInf_le_partialProd ω 0
      unfold partialProd at h
      rwa [Finset.prod_range_one] at h
    rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos a),
      abs_of_nonpos (by linarith), neg_sub]
  have hint0 : Integrable
      (fun ω : Π _ : ℕ, ℕ × (ℕ → ℝ) => prodFnT (ω 0)) (cpModelInf ms) := by
    refine Integrable.mono' (integrable_const 1)
      (measurable_prodFnT.comp (measurable_pi_apply 0)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (prodFnT_mem_Icc (ω 0)).1]
    exact (prodFnT_mem_Icc (ω 0)).2
  have hintInf : Integrable
      (fun ω : Π _ : ℕ, ℕ × (ℕ → ℝ) => prodInf ω) (cpModelInf ms) := by
    refine Integrable.mono' (integrable_const 1)
      measurable_prodInf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (prodInf_mem_Icc ω).1]
    exact (prodInf_mem_Icc ω).2
  have hcost : ∫ ω, |Real.exp a * prodInf ω - Real.exp a * prodFnT (ω 0)|
      ∂(cpModelInf ms)
      = Real.exp a * ((∫ ω, prodFnT (ω 0) ∂(cpModelInf ms))
          - ∫ ω, prodInf ω ∂(cpModelInf ms)) := by
    rw [show (fun ω : Π _ : ℕ, ℕ × (ℕ → ℝ) =>
        |Real.exp a * prodInf ω - Real.exp a * prodFnT (ω 0)|)
        = fun ω => Real.exp a * (prodFnT (ω 0) - prodInf ω)
        from funext hpt, integral_const_mul, integral_sub hint0 hintInf]
  rw [hcost]
  -- evaluate both integrals through the layer factorization
  have hval0 : ∫ ω, prodFnT (ω 0) ∂(cpModelInf ms)
      = Real.exp (∫ u, (clamp01 u - 1) ∂(ms 0)) := by
    have h := integral_map (μ := cpModelInf ms)
      (measurable_pi_apply 0).aemeasurable
      (f := fun p : ℕ × (ℕ → ℝ) => prodFnT p)
      measurable_prodFnT.aestronglyMeasurable
    unfold cpModelInf at h ⊢
    rw [Measure.infinitePi_map_eval] at h
    rw [← h]
    have h1 := integral_pow_layerModel' (ms 0) 1
    simp only [pow_one] at h1
    exact h1
  have hvalInf : ∫ ω, prodInf ω ∂(cpModelInf ms)
      = Real.exp (∑' j, ∫ u, (clamp01 u - 1) ∂(ms j)) := by
    have h := integral_pow_cpLawInf 0 ms hsum 1
    unfold cpLawInf at h
    rw [integral_map (measurable_const.mul measurable_prodInf).aemeasurable
      (continuous_pow 1).aestronglyMeasurable] at h
    simp only [Real.exp_zero, one_mul, pow_one, Nat.cast_one, zero_mul,
      zero_add] at h
    exact h
  -- the cumulant series splits off its zeroth term
  have hsumc : Summable fun j => ∫ u, (clamp01 u - 1) ∂(ms j) := by
    refine (summable_layer_cumulants hsum 1).congr fun j => ?_
    congr 1
    funext u
    rw [pow_one]
  have hsplit_t : ∑' j, ∫ u, (clamp01 u - 1) ∂(ms j)
      = (∫ u, (clamp01 u - 1) ∂(ms 0))
          + ∑' j, ∫ u, (clamp01 u - 1) ∂(ms (j + 1)) :=
    hsumc.tsum_eq_zero_add
  have hneg : ∑' j, ∫ u, (1 - clamp01 u) ∂(ms (j + 1))
      = -∑' j, ∫ u, (clamp01 u - 1) ∂(ms (j + 1)) := by
    rw [← tsum_neg]
    congr 1
    funext j
    rw [← integral_neg]
    congr 1
    funext u
    ring
  have hc0 : ∫ u, (clamp01 u - 1) ∂(ms 0) ≤ 0 :=
    integral_nonpos fun u =>
      show clamp01 u - 1 ≤ (0 : ℝ) by linarith [(clamp01_mem_Icc u).2]
  have ht : ∑' j, ∫ u, (clamp01 u - 1) ∂(ms (j + 1)) ≤ 0 :=
    tsum_nonpos fun j =>
      integral_nonpos fun u =>
        show clamp01 u - 1 ≤ (0 : ℝ) by linarith [(clamp01_mem_Icc u).2]
  rw [hval0, hvalInf, hsplit_t]
  calc Real.exp a * (Real.exp (∫ u, (clamp01 u - 1) ∂(ms 0))
        - Real.exp ((∫ u, (clamp01 u - 1) ∂(ms 0))
            + ∑' j, ∫ u, (clamp01 u - 1) ∂(ms (j + 1))))
      = Real.exp a * (Real.exp (∫ u, (clamp01 u - 1) ∂(ms 0))
          * (1 - Real.exp (∑' j, ∫ u, (clamp01 u - 1) ∂(ms (j + 1))))) := by
        rw [Real.exp_add]; ring
    _ ≤ Real.exp a
        * (1 * (1 - Real.exp (∑' j, ∫ u, (clamp01 u - 1) ∂(ms (j + 1))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos a).le
        refine mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr hc0) ?_
        linarith [Real.exp_le_one_iff.mpr ht]
    _ ≤ Real.exp a * (-∑' j, ∫ u, (clamp01 u - 1) ∂(ms (j + 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos a).le
        linarith [Real.add_one_le_exp
          (∑' j, ∫ u, (clamp01 u - 1) ∂(ms (j + 1)))]
    _ = Real.exp a * ∑' j, ∫ u, (1 - clamp01 u) ∂(ms (j + 1)) := by
        rw [hneg]

/-! ## The geometric bands

Theorem 11's `ε`-independent split: `band β 0 = [0, (1+β)/2]` is the
macroscopic band, and `band β (j+1) = (1 − h₀/2ʲ, 1 − h₀/2^{j+1}]`
(`h₀ = (1−β)/2`) chops the small-jump region into pieces of finite
intensity — the layered stand-in for the Poisson point process. -/

/-- The layer bands. -/
def band (β : ℝ) : ℕ → Set ℝ
  | 0 => Set.Icc 0 ((1 + β) / 2)
  | j + 1 => Set.Ioc (1 - (1 - β) / 2 / 2 ^ j) (1 - (1 - β) / 2 / 2 ^ (j + 1))

theorem measurableSet_band (β : ℝ) (j : ℕ) : MeasurableSet (band β j) := by
  cases j with
  | zero => exact measurableSet_Icc
  | succ j => exact measurableSet_Ioc

/-- Every band sits below its right tilt level. -/
theorem band_subset_Iic (β : ℝ) (j : ℕ) :
    band β j ⊆ Set.Iic (1 - (1 - β) / 2 / 2 ^ j) := by
  cases j with
  | zero =>
    intro u hu
    have h2 : u ≤ (1 + β) / 2 := hu.2
    have heq : (1 : ℝ) - (1 - β) / 2 / 2 ^ 0 = (1 + β) / 2 := by
      norm_num
      ring
    rw [Set.mem_Iic, heq]
    exact h2
  | succ j => exact fun _ hu => Set.mem_Iic.mpr hu.2

theorem band_succ_subset_Ioi (β : ℝ) (j : ℕ) :
    band β (j + 1) ⊆ Set.Ioi (1 - (1 - β) / 2 / 2 ^ j) :=
  fun _ hu => Set.mem_Ioi.mpr hu.1

/-- The tilt `1 − u` is bounded below by `h₀/2ʲ` on `band β j`. -/
theorem one_sub_ge_on_band (β : ℝ) (j : ℕ) {u : ℝ} (hu : u ∈ band β j) :
    (1 - β) / 2 / 2 ^ j ≤ 1 - u := by
  have h := band_subset_Iic β j hu
  rw [Set.mem_Iic] at h
  linarith

/-- The bands are pairwise disjoint. -/
theorem pairwise_disjoint_band {β : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    Pairwise (Function.onFun Disjoint (band β)) := by
  have key : ∀ i j : ℕ, i < j → Disjoint (band β i) (band β j) := by
    intro i j hij
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 :=
      ⟨j - 1, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
    have hii : i ≤ j' := Nat.lt_succ_iff.mp hij
    have hh0 : (0 : ℝ) < (1 - β) / 2 := by
      have := hβ.2; linarith
    have h2 : (2 : ℝ) ^ i ≤ 2 ^ j' := pow_le_pow_right₀ one_le_two hii
    have hdiv : (1 - β) / 2 / 2 ^ j' ≤ (1 - β) / 2 / 2 ^ i :=
      div_le_div_of_nonneg_left hh0.le (pow_pos two_pos i) h2
    refine Set.disjoint_of_subset (band_subset_Iic β i)
      (band_succ_subset_Ioi β j') ?_
    exact Set.Iic_disjoint_Ioi (by linarith)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- The bands cover `[0,1)` — the a.e. support of the intensity. -/
theorem Ico_subset_iUnion_band {β : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    Set.Ico (0 : ℝ) 1 ⊆ ⋃ j, band β j := by
  intro u hu
  by_cases h0 : u ≤ (1 + β) / 2
  · exact Set.mem_iUnion.mpr ⟨0, ⟨hu.1, h0⟩⟩
  · push Not at h0
    have hh0 : (0 : ℝ) < (1 - β) / 2 := by have := hβ.2; linarith
    have h1u : (0 : ℝ) < 1 - u := by linarith [hu.2]
    have hex : ∃ n : ℕ, u ≤ 1 - (1 - β) / 2 / 2 ^ n := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
        (div_pos h1u hh0) (by norm_num : (1 : ℝ) / 2 < 1)
      refine ⟨n, ?_⟩
      have hpow : ((1 : ℝ) / 2) ^ n = 1 / 2 ^ n := by
        rw [div_pow, one_pow]
      rw [hpow, div_lt_div_iff₀ (pow_pos two_pos n) hh0] at hn
      have hkey : (1 - β) / 2 / 2 ^ n < 1 - u := by
        rw [div_lt_iff₀ (pow_pos two_pos n)]
        linarith
      linarith
    set N := Nat.find hex with hNdef
    have hNspec : u ≤ 1 - (1 - β) / 2 / 2 ^ N := Nat.find_spec hex
    have hNpos : N ≠ 0 := by
      intro hN0
      rw [hN0] at hNspec
      simp only [pow_zero, div_one] at hNspec
      have heq : (1 : ℝ) - (1 - β) / 2 = (1 + β) / 2 := by ring
      rw [heq] at hNspec
      linarith
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 :=
      ⟨N - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hNpos)).symm⟩
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    rw [hM]
    refine ⟨?_, ?_⟩
    · have hMlt : M < N := by rw [hM]; exact Nat.lt_succ_self M
      have hmin := Nat.find_min hex hMlt
      push Not at hmin
      exact hmin
    · rw [← hM]
      exact hNspec

/-! ## Bridges between the intensity `νt` and the tilted measure `η`

`η = (1−u)·νt`: set masses of `η` are tilted set-integrals against `νt`,
and `η`-integrals de-tilt to `(1−u)`-weighted `νt`-integrals.  These two
bridges plus Chebyshev on the variance hypothesis are the whole of
Theorem 11's Steps 1–3 analysis. -/

/-- `η`-mass as a tilted set integral (clamped form). -/
theorem eta_real_eq (νt : Measure ℝ)
    (hsupp : ∀ᵐ u ∂νt, u ∈ Set.Ico 0 1) {B : Set ℝ} (hB : MeasurableSet B) :
    (νt.withDensity fun u => ENNReal.ofReal (1 - u)).real B
      = ∫ u in B, (1 - clamp01 u) ∂νt := by
  have hmeas : Measurable fun u : ℝ => 1 - clamp01 u :=
    measurable_const.sub measurable_clamp01
  have hnn : 0 ≤ᵐ[νt.restrict B] fun u => 1 - clamp01 u :=
    Filter.Eventually.of_forall fun u =>
      show (0 : ℝ) ≤ 1 - clamp01 u by linarith [(clamp01_mem_Icc u).2]
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable,
    measureReal_def, withDensity_apply _ hB]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hsupp] with u hu
  rw [clamp01_eq_self ⟨hu.1, hu.2.le⟩]

/-- The tilt is integrable against the intensity whenever `η` is finite
— even for infinite-activity `νt`. -/
theorem integrable_one_sub_clamp (νt : Measure ℝ)
    (hsupp : ∀ᵐ u ∂νt, u ∈ Set.Ico 0 1)
    [IsFiniteMeasure (νt.withDensity fun u => ENNReal.ofReal (1 - u))] :
    Integrable (fun u => 1 - clamp01 u) νt := by
  have hmeas : Measurable fun u : ℝ => 1 - clamp01 u :=
    measurable_const.sub measurable_clamp01
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hcongr : ∀ᵐ u ∂νt, ‖1 - clamp01 u‖ₑ = ENNReal.ofReal (1 - u) := by
    filter_upwards [hsupp] with u hu
    rw [clamp01_eq_self ⟨hu.1, hu.2.le⟩,
      Real.enorm_eq_ofReal (by linarith [hu.2])]
  rw [lintegral_congr_ae hcongr, ← setLIntegral_univ,
    ← withDensity_apply _ MeasurableSet.univ]
  exact measure_lt_top _ _

/-- `η`-integrals de-tilt to `(1−u)`-weighted `νt`-integrals. -/
theorem integral_eta_eq (νt : Measure ℝ)
    (hsupp : ∀ᵐ u ∂νt, u ∈ Set.Ico 0 1) (h : ℝ → ℝ) :
    ∫ u, h u ∂(νt.withDensity fun u => ENNReal.ofReal (1 - u))
      = ∫ u, h u * (1 - clamp01 u) ∂νt := by
  have hd : (fun u : ℝ => ENNReal.ofReal (1 - u))
      = fun u : ℝ => (((1 - u).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  have hfm : Measurable fun u : ℝ => (1 - u).toNNReal :=
    (measurable_const.sub measurable_id).real_toNNReal
  rw [hd, integral_withDensity_eq_integral_smul hfm h]
  refine integral_congr_ae ?_
  filter_upwards [hsupp] with u hu
  rw [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (by linarith [hu.2]),
    clamp01_eq_self ⟨hu.1, hu.2.le⟩, mul_comm]

/-- Finite intensity on every band: the tilt is bounded below there, so
finiteness of `η` forces finiteness of `νt` band by band.  (This is why
infinite activity needs no extra hypotheses: it can only accumulate at
`u = 1`, where the multiplicative cost vanishes at exactly the rate `η`
measures.) -/
theorem isFiniteMeasure_restrict_band {β : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (νt : Measure ℝ)
    [IsFiniteMeasure (νt.withDensity fun u => ENNReal.ofReal (1 - u))]
    (j : ℕ) : IsFiniteMeasure (νt.restrict (band β j)) := by
  set ε₀ : ℝ≥0∞ := ENNReal.ofReal ((1 - β) / 2 / 2 ^ j) with hε₀
  have hh0 : (0 : ℝ) < (1 - β) / 2 / 2 ^ j :=
    div_pos (div_pos (by linarith [hβ.2]) two_pos) (pow_pos two_pos j)
  have hε₀0 : ε₀ ≠ 0 := by
    rw [hε₀, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hh0
  have hkey : ε₀ * νt (band β j)
      ≤ (νt.withDensity fun u => ENNReal.ofReal (1 - u)) (band β j) := by
    rw [withDensity_apply _ (measurableSet_band β j)]
    have hmono : ∀ᵐ u ∂(νt.restrict (band β j)),
        ε₀ ≤ ENNReal.ofReal (1 - u) := by
      filter_upwards [ae_restrict_mem (measurableSet_band β j)] with u hu
      exact ENNReal.ofReal_le_ofReal (one_sub_ge_on_band β j hu)
    calc ε₀ * νt (band β j) = ∫⁻ _ in band β j, ε₀ ∂νt := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ u in band β j, ENNReal.ofReal (1 - u) ∂νt :=
          lintegral_mono_ae hmono
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  rcases eq_top_or_lt_top (νt (band β j)) with htop | hlt
  · exfalso
    rw [htop, ENNReal.mul_top hε₀0] at hkey
    exact absurd (top_le_iff.mp hkey) (measure_lt_top _ _).ne
  · exact hlt

/-- **Chebyshev for the small-jump mass** (Theorem 11, Step 1): outside
the macroscopic band the deviation exceeds `h₀ = (1−β)/2`, so the
variance hypothesis controls the tilted mass there. -/
theorem eta_compl_band0_le {β : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (νt : Measure ℝ) (hsupp : ∀ᵐ u ∂νt, u ∈ Set.Ico 0 1)
    [IsFiniteMeasure (νt.withDensity fun u => ENNReal.ofReal (1 - u))]
    {Vε : ℝ}
    (hvar : ∫ u, (u - β) ^ 2
        ∂(νt.withDensity fun u => ENNReal.ofReal (1 - u)) ≤ Vε) :
    (νt.withDensity fun u => ENNReal.ofReal (1 - u)).real (band β 0)ᶜ
      ≤ 4 * Vε / (1 - β) ^ 2 := by
  set η := νt.withDensity fun u => ENNReal.ofReal (1 - u) with hηdef
  have hηsupp : ∀ᵐ u ∂η, u ∈ Set.Ico 0 1 :=
    Filter.Eventually.filter_mono
      (withDensity_absolutelyContinuous νt _).ae_le hsupp
  have hβ2 : (0 : ℝ) < 1 - β := by have := hβ.2; linarith
  have hint : Integrable (fun u => (u - β) ^ 2) η := by
    refine Integrable.mono' (integrable_const 1)
      (((measurable_id.sub measurable_const).pow_const
        2).aestronglyMeasurable) ?_
    filter_upwards [hηsupp] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : |u - β| ≤ 1 := abs_le.mpr
      ⟨by linarith [hu.1, hβ.2], by linarith [hu.2, hβ.1]⟩
    calc (u - β) ^ 2 = |u - β| ^ 2 := (sq_abs _).symm
      _ ≤ 1 := by nlinarith [abs_nonneg (u - β)]
  have hpoint : (fun _ : ℝ => ((1 - β) / 2) ^ 2)
      ≤ᵐ[η.restrict (band β 0)ᶜ] fun u => (u - β) ^ 2 := by
    filter_upwards [ae_restrict_of_ae hηsupp,
      ae_restrict_mem (measurableSet_band β 0).compl] with u hu hc
    have hgt : (1 + β) / 2 < u := by
      by_contra hle
      push Not at hle
      exact hc ⟨hu.1, hle⟩
    have h1 : (1 - β) / 2 ≤ u - β := by linarith
    nlinarith [sq_nonneg (u - β - (1 - β) / 2)]
  have hchain : ((1 - β) / 2) ^ 2 * η.real (band β 0)ᶜ ≤ Vε := by
    have hconst : ∫ _ in (band β 0)ᶜ, ((1 - β) / 2) ^ 2 ∂η
        = ((1 - β) / 2) ^ 2 * η.real (band β 0)ᶜ := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    calc ((1 - β) / 2) ^ 2 * η.real (band β 0)ᶜ
        = ∫ _ in (band β 0)ᶜ, ((1 - β) / 2) ^ 2 ∂η := hconst.symm
      _ ≤ ∫ u in (band β 0)ᶜ, (u - β) ^ 2 ∂η :=
          setIntegral_mono_ae_restrict
            (integrable_const _).integrableOn hint.integrableOn hpoint
      _ ≤ ∫ u, (u - β) ^ 2 ∂η :=
          setIntegral_le_integral hint
            (Filter.Eventually.of_forall fun u => sq_nonneg _)
      _ ≤ Vε := hvar
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 - β) ^ 2)]
  nlinarith [hchain]

/-- **De-tilting on the macroscopic band** (Theorem 11, Step 3): the
fixed constant `2/(1−β)` converts the band's jump cost against `νt` into
the first-moment hypothesis on `η`. -/
theorem setIntegral_band0_abs_le {β : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (νt : Measure ℝ) (hsupp : ∀ᵐ u ∂νt, u ∈ Set.Ico 0 1)
    [IsFiniteMeasure (νt.withDensity fun u => ENNReal.ofReal (1 - u))]
    {Sε : ℝ}
    (habs : ∫ u, |u - β|
        ∂(νt.withDensity fun u => ENNReal.ofReal (1 - u)) ≤ Sε) :
    ∫ u in band β 0, |clamp01 u - β| ∂νt ≤ 2 / (1 - β) * Sε := by
  haveI := isFiniteMeasure_restrict_band hβ νt 0
  set η := νt.withDensity fun u => ENNReal.ofReal (1 - u) with hηdef
  have hβ2 : (0 : ℝ) < 1 - β := by have := hβ.2; linarith
  have hmeasq : Measurable fun u : ℝ => |clamp01 u - β| :=
    (measurable_clamp01.sub measurable_const).abs
  have habsbd : ∀ x : ℝ, |(|clamp01 x - β|)| ≤ 2 := by
    intro x
    rw [abs_abs]
    have h1 := (clamp01_mem_Icc x).1
    have h2 := (clamp01_mem_Icc x).2
    exact abs_le.mpr ⟨by linarith [hβ.1, hβ.2], by linarith [hβ.1, hβ.2]⟩
  -- the weighted integrand against νt is dominated by the integrable tilt
  have hintw : Integrable
      (fun u => |clamp01 u - β| * (1 - clamp01 u)) νt := by
    refine Integrable.mono'
      ((integrable_one_sub_clamp νt hsupp).const_mul 2)
      (hmeasq.mul (measurable_const.sub measurable_clamp01)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 := (clamp01_mem_Icc u).1
    have h2 := (clamp01_mem_Icc u).2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith :
      (0 : ℝ) ≤ 1 - clamp01 u)]
    have := habsbd u
    nlinarith [abs_nonneg (clamp01 u - β)]
  -- pointwise de-tilt on the macroscopic band
  have hpoint : (fun u : ℝ => |clamp01 u - β|)
      ≤ᵐ[νt.restrict (band β 0)]
        fun u => 2 / (1 - β) * (|clamp01 u - β| * (1 - clamp01 u)) := by
    filter_upwards [ae_restrict_mem (measurableSet_band β 0)] with u hu
    have htilt : (1 - β) / 2 ≤ 1 - u := by
      have := one_sub_ge_on_band β 0 hu
      simpa using this
    have hu1 : u ≤ (1 + β) / 2 := hu.2
    have hu0 : 0 ≤ u := hu.1
    have hclamp : clamp01 u = u := clamp01_eq_self ⟨hu0, by linarith⟩
    rw [hclamp]
    have habs0 : 0 ≤ |u - β| := abs_nonneg _
    have hfac : 1 ≤ 2 / (1 - β) * (1 - u) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hβ2, one_mul]
      linarith
    calc |u - β| = |u - β| * 1 := (mul_one _).symm
      _ ≤ |u - β| * (2 / (1 - β) * (1 - u)) :=
          mul_le_mul_of_nonneg_left hfac habs0
      _ = 2 / (1 - β) * (|u - β| * (1 - u)) := by ring
  haveI : IsFiniteMeasure (νt.restrict (band β 0)) :=
    isFiniteMeasure_restrict_band hβ νt 0
  have hint1 : Integrable (fun u => |clamp01 u - β|)
      (νt.restrict (band β 0)) :=
    integrable_of_bounded_finite hmeasq habsbd
  calc ∫ u in band β 0, |clamp01 u - β| ∂νt
      ≤ ∫ u in band β 0,
          2 / (1 - β) * (|clamp01 u - β| * (1 - clamp01 u)) ∂νt :=
        setIntegral_mono_ae_restrict hint1
          (hintw.const_mul _).integrableOn hpoint
    _ = 2 / (1 - β) * ∫ u in band β 0,
          |clamp01 u - β| * (1 - clamp01 u) ∂νt := integral_const_mul _ _
    _ ≤ 2 / (1 - β) * ∫ u, |clamp01 u - β| * (1 - clamp01 u) ∂νt := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine setIntegral_le_integral hintw
          (Filter.Eventually.of_forall fun u => ?_)
        show (0 : ℝ) ≤ |clamp01 u - β| * (1 - clamp01 u)
        have h1 := (clamp01_mem_Icc u).1
        have h2 := (clamp01_mem_Icc u).2
        have := abs_nonneg (clamp01 u - β)
        nlinarith
    _ = 2 / (1 - β) * ∫ u, |u - β| ∂η := by
        rw [hηdef, integral_eta_eq νt hsupp (fun u => |u - β|)]
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [hsupp] with u hu
        rw [clamp01_eq_self ⟨hu.1, hu.2.le⟩]
    _ ≤ 2 / (1 - β) * Sε :=
        mul_le_mul_of_nonneg_left habs (by positivity)

/-- **The rate mismatch** (Theorem 11, Step 2): the macroscopic rate
differs from `‖η‖/(1−β)` by the de-tilted first moment plus the
small-jump mass. -/
theorem rate_diff_le {β : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (νt : Measure ℝ) (hsupp : ∀ᵐ u ∂νt, u ∈ Set.Ico 0 1)
    [IsFiniteMeasure (νt.withDensity fun u => ENNReal.ofReal (1 - u))] :
    |νt.real (band β 0) * (1 - β)
        - (νt.withDensity fun u => ENNReal.ofReal (1 - u)).real Set.univ|
      ≤ (∫ u in band β 0, |clamp01 u - β| ∂νt)
        + (νt.withDensity fun u => ENNReal.ofReal (1 - u)).real
            (band β 0)ᶜ := by
  haveI := isFiniteMeasure_restrict_band hβ νt (β := β) 0
  set η := νt.withDensity fun u => ENNReal.ofReal (1 - u) with hηdef
  -- total tilted mass splits across the band and its complement
  have hsplitmass : η.real Set.univ
      = (∫ u in band β 0, (1 - clamp01 u) ∂νt) + η.real (band β 0)ᶜ := by
    have h1 : η.real Set.univ
        = η.real (band β 0) + η.real (band β 0)ᶜ := by
      rw [← measureReal_add_measureReal_compl (μ := η)
        (measurableSet_band β 0)]
    rw [h1, eta_real_eq νt hsupp (measurableSet_band β 0)]
  -- the band part of the rate difference is the first-moment integral
  have hmoment : νt.real (band β 0) * (1 - β)
      - ∫ u in band β 0, (1 - clamp01 u) ∂νt
      = ∫ u in band β 0, (clamp01 u - β) ∂νt := by
    have hconst : ∫ _ in band β 0, (1 - β) ∂νt
        = νt.real (band β 0) * (1 - β) := by
      rw [setIntegral_const, smul_eq_mul]
    have hint1 : Integrable (fun _ : ℝ => (1 : ℝ) - β)
        (νt.restrict (band β 0)) := integrable_const _
    have hint2 : Integrable (fun u => 1 - clamp01 u)
        (νt.restrict (band β 0)) := by
      refine integrable_of_bounded_finite
        (measurable_const.sub measurable_clamp01) (C := 1) fun x => ?_
      have h1 := (clamp01_mem_Icc x).1
      have h2 := (clamp01_mem_Icc x).2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    rw [← hconst, ← integral_sub hint1 hint2]
    congr 1
    funext u
    ring
  rw [hsplitmass]
  have hre : νt.real (band β 0) * (1 - β)
      - ((∫ u in band β 0, (1 - clamp01 u) ∂νt) + η.real (band β 0)ᶜ)
      = (∫ u in band β 0, (clamp01 u - β) ∂νt) - η.real (band β 0)ᶜ := by
    rw [← hmoment]
    ring
  rw [hre]
  have habs1 : |∫ u in band β 0, (clamp01 u - β) ∂νt|
      ≤ ∫ u in band β 0, |clamp01 u - β| ∂νt :=
    abs_integral_le_integral_abs
  have habs2 : (0 : ℝ) ≤ η.real (band β 0)ᶜ := measureReal_nonneg
  calc |(∫ u in band β 0, (clamp01 u - β) ∂νt) - η.real (band β 0)ᶜ|
      ≤ |∫ u in band β 0, (clamp01 u - β) ∂νt| + |η.real (band β 0)ᶜ| :=
        abs_sub _ _
    _ ≤ (∫ u in band β 0, |clamp01 u - β| ∂νt) + η.real (band β 0)ᶜ := by
        rw [abs_of_nonneg habs2]
        exact add_le_add habs1 le_rfl

/-- The per-band tilted masses are summable, with the small-jump tail
summing below the complement mass — the layer interface of Step 1. -/
theorem tilt_bands_summable {β : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (νt : Measure ℝ) (hsupp : ∀ᵐ u ∂νt, u ∈ Set.Ico 0 1)
    [IsFiniteMeasure (νt.withDensity fun u => ENNReal.ofReal (1 - u))] :
    Summable (fun j => ∫ u, (1 - clamp01 u) ∂(νt.restrict (band β j)))
      ∧ ∑' j, ∫ u, (1 - clamp01 u) ∂(νt.restrict (band β (j + 1)))
          ≤ (νt.withDensity fun u => ENNReal.ofReal (1 - u)).real
              (band β 0)ᶜ := by
  set η := νt.withDensity fun u => ENNReal.ofReal (1 - u) with hηdef
  have hterm : ∀ j : ℕ, ∫ u, (1 - clamp01 u) ∂(νt.restrict (band β j))
      = η.real (band β j) :=
    fun j => (eta_real_eq νt hsupp (measurableSet_band β j)).symm
  have hnn : ∀ j : ℕ, 0 ≤ η.real (band β j) := fun j => measureReal_nonneg
  -- finite partial sums are masses of disjoint unions
  have hpartial : ∀ (f : ℕ → ℕ), Function.Injective f → ∀ n : ℕ,
      ∑ i ∈ Finset.range n, η.real (band β (f i)) ≤ η.real Set.univ := by
    intro f hf n
    have hdisj : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint
        fun i => band β (f i) := by
      intro i _ j _ hij
      exact pairwise_disjoint_band hβ (hf.ne hij)
    have hsum : ∑ i ∈ Finset.range n, η.real (band β (f i))
        = η.real (⋃ i ∈ Finset.range n, band β (f i)) := by
      rw [measureReal_biUnion_finset hdisj
        fun i _ => measurableSet_band β (f i)]
    rw [hsum]
    exact measureReal_mono (Set.subset_univ _)
  constructor
  · refine summable_of_sum_range_le (c := η.real Set.univ)
      (fun j => by rw [hterm j]; exact hnn j) fun n => ?_
    calc ∑ i ∈ Finset.range n,
          ∫ u, (1 - clamp01 u) ∂(νt.restrict (band β i))
        = ∑ i ∈ Finset.range n, η.real (band β i) :=
          Finset.sum_congr rfl fun i _ => hterm i
      _ ≤ η.real Set.univ := hpartial id (fun _ _ h => h) n
  · refine Real.tsum_le_of_sum_range_le
      (fun j => by rw [hterm (j + 1)]; exact hnn (j + 1)) fun n => ?_
    have hdisj : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint
        fun i => band β (i + 1) := by
      intro i _ j _ hij
      exact pairwise_disjoint_band hβ (by omega)
    calc ∑ i ∈ Finset.range n,
          ∫ u, (1 - clamp01 u) ∂(νt.restrict (band β (i + 1)))
        = ∑ i ∈ Finset.range n, η.real (band β (i + 1)) :=
          Finset.sum_congr rfl fun i _ => hterm (i + 1)
      _ = η.real (⋃ i ∈ Finset.range n, band β (i + 1)) :=
          (measureReal_biUnion_finset hdisj
            fun i _ => measurableSet_band β (i + 1)).symm
      _ ≤ η.real (band β 0)ᶜ := by
          refine measureReal_mono ?_
          refine Set.iUnion₂_subset fun i _ => ?_
          intro u hu
          have h1 := band_succ_subset_Ioi β i hu

          rw [Set.mem_Ioi] at h1
          have hh0 : (0 : ℝ) < (1 - β) / 2 / 2 ^ i :=
            div_pos (div_pos (by linarith [hβ.2]) two_pos)
              (pow_pos two_pos i)
          intro hu0
          have : u ≤ (1 + β) / 2 := hu0.2
          have heq : (1 : ℝ) - (1 - β) / 2 / 2 ^ i ≥ (1 + β) / 2 := by
            have h2 : (1 - β) / 2 / 2 ^ i ≤ (1 - β) / 2 := by
              rw [div_le_iff₀ (pow_pos two_pos i)]
              have h3 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ one_le_two
              nlinarith [hβ.2]
            linarith
          linarith

/-! ## Theorem 11, assembled: the unconditional propagation bound

The triangle decomposition `W₁(W, W₀) ≤ Leg A + Leg B + Leg C` with the
band estimates yields the explicit bound
`W₁ ≤ e^a (4Sε/(1−β) + 8Vε/(1−β)²)` for any intensity measure whose
tilt `η` satisfies the Theorem-10 moment bounds — finite or infinite
activity alike, with no minimum-jump hypothesis.  At `k = 1` the
conservation drift is rigid (`a = ‖η‖ = λ(1−β)`), so no drift slack is
spent (the paper's `e^{a₀+1}` can be read `e^{a₀}` here). -/

theorem theorem11_W1_upper {β : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (νt : Measure ℝ) (hsupp : ∀ᵐ u ∂νt, u ∈ Set.Ico 0 1)
    [IsFiniteMeasure (νt.withDensity fun u => ENNReal.ofReal (1 - u))]
    {Vε Sε : ℝ}
    (hvar : ∫ u, (u - β) ^ 2
        ∂(νt.withDensity fun u => ENNReal.ofReal (1 - u)) ≤ Vε)
    (habs : ∫ u, |u - β|
        ∂(νt.withDensity fun u => ENNReal.ofReal (1 - u)) ≤ Sε)
    (a : ℝ)
    (_ha : a = (νt.withDensity fun u =>
      ENNReal.ofReal (1 - u)).real Set.univ)
    (lam : ℝ≥0)
    (hlam : (lam : ℝ) * (1 - β)
      = (νt.withDensity fun u => ENNReal.ofReal (1 - u)).real Set.univ) :
    W1 (cpLawInf a fun j => νt.restrict (band β j))
        (logPoissonLaw a (Real.log β) lam)
      ≤ Real.exp a * (4 * Sε / (1 - β) + 8 * Vε / (1 - β) ^ 2) := by
  haveI : ∀ j, IsFiniteMeasure ((fun j => νt.restrict (band β j)) j) :=
    fun j => isFiniteMeasure_restrict_band hβ νt j
  have hβ1 : (0 : ℝ) < 1 - β := by linarith [hβ.2]
  obtain ⟨hsum, htail⟩ := tilt_bands_summable hβ νt hsupp
  -- the three coupling legs
  have hlegA : W1 (cpLawInf a fun j => νt.restrict (band β j))
      (cpLaw a (layerRate (νt.restrict (band β 0)))
        (layerProb (νt.restrict (band β 0))))
      ≤ Real.exp a * (4 * Vε / (1 - β) ^ 2) := by
    refine (W1_cpLawInf_layer0_le a (fun j => νt.restrict (band β j))
      hsum).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos a).le
    exact htail.trans (eta_compl_band0_le hβ νt hsupp hvar)
  have hlegB : W1 (cpLaw a (layerRate (νt.restrict (band β 0)))
      (layerProb (νt.restrict (band β 0))))
      (logPoissonLaw a (Real.log β) (layerRate (νt.restrict (band β 0))))
      ≤ Real.exp a * (2 / (1 - β) * Sε) := by
    refine (W1_cpLaw_logPoisson_le a _ _ hβ.1 hβ.2.le).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos a).le
    have hbridge : (layerRate (νt.restrict (band β 0)) : ℝ)
        * ∫ u, |clamp01 u - β| ∂(layerProb (νt.restrict (band β 0)))
        = ∫ u in band β 0, |clamp01 u - β| ∂νt :=
      layerRate_mul_integral (νt.restrict (band β 0)) _
    rw [hbridge]
    exact setIntegral_band0_abs_le hβ νt hsupp habs
  have hS₀real : (layerRate (νt.restrict (band β 0)) : ℝ)
      = νt.real (band β 0) := by
    unfold layerRate
    rw [Measure.restrict_apply_univ]
    rfl
  have hlegC : W1 (logPoissonLaw a (Real.log β)
      (layerRate (νt.restrict (band β 0))))
      (logPoissonLaw a (Real.log β) lam)
      ≤ Real.exp a * (2 / (1 - β) * Sε + 4 * Vε / (1 - β) ^ 2) := by
    refine (W1_logPoisson_rate_le' hβ.1 hβ.2.le a _ lam).trans ?_
    have h3 := setIntegral_band0_abs_le hβ νt hsupp habs
    have h4 := eta_compl_band0_le hβ νt hsupp hvar
    have h2 := rate_diff_le hβ νt hsupp
    have hkey : (1 - β) * |(layerRate (νt.restrict (band β 0)) : ℝ)
        - (lam : ℝ)| ≤ 2 / (1 - β) * Sε + 4 * Vε / (1 - β) ^ 2 := by
      have h1 : νt.real (band β 0) * (1 - β)
          - (νt.withDensity fun u =>
              ENNReal.ofReal (1 - u)).real Set.univ
          = ((layerRate (νt.restrict (band β 0)) : ℝ) - (lam : ℝ))
              * (1 - β) := by
        rw [hS₀real, ← hlam]
        ring
      have habseq : (1 - β) * |(layerRate (νt.restrict (band β 0)) : ℝ)
          - (lam : ℝ)|
          = |νt.real (band β 0) * (1 - β)
              - (νt.withDensity fun u =>
                  ENNReal.ofReal (1 - u)).real Set.univ| := by
        rw [h1, abs_mul, abs_of_pos hβ1]
        ring
      rw [habseq]
      exact h2.trans (add_le_add h3 h4)
    calc Real.exp a * (1 - β)
          * |(layerRate (νt.restrict (band β 0)) : ℝ) - (lam : ℝ)|
        = Real.exp a * ((1 - β)
            * |(layerRate (νt.restrict (band β 0)) : ℝ) - (lam : ℝ)|) := by
          ring
      _ ≤ Real.exp a * (2 / (1 - β) * Sε + 4 * Vε / (1 - β) ^ 2) :=
          mul_le_mul_of_nonneg_left hkey (Real.exp_pos a).le
  -- triangle assembly on the common support `[−e^a, e^a]`
  have hM1 := cpLawInf_abs_le a fun j => νt.restrict (band β j)
  have hM2 := cpLaw_abs_le a (layerRate (νt.restrict (band β 0)))
    (layerProb (νt.restrict (band β 0)))
  have hM3 := logPoissonLaw_abs_le hβ.1 hβ.2.le a
    (layerRate (νt.restrict (band β 0)))
  have hM4 := logPoissonLaw_abs_le hβ.1 hβ.2.le a lam
  have htri1 := W1_triangle hM1 hM2 hM4
  have htri2 := W1_triangle hM2 hM3 hM4
  calc W1 (cpLawInf a fun j => νt.restrict (band β j))
        (logPoissonLaw a (Real.log β) lam)
      ≤ Real.exp a * (4 * Vε / (1 - β) ^ 2)
        + (Real.exp a * (2 / (1 - β) * Sε)
            + Real.exp a * (2 / (1 - β) * Sε + 4 * Vε / (1 - β) ^ 2)) := by
        linarith [htri1, htri2, hlegA, hlegB, hlegC]
    _ = Real.exp a * (4 * Sε / (1 - β) + 8 * Vε / (1 - β) ^ 2) := by
        field_simp
        ring

/-! ## The cumulant certificate against the Lévy measure -/

/-- Band sums of tilt-dominated integrands recover the full
`νt`-integral. -/
theorem tsum_setIntegral_bands {β : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (νt : Measure ℝ) (hsupp : ∀ᵐ u ∂νt, u ∈ Set.Ico 0 1)
    [IsFiniteMeasure (νt.withDensity fun u => ENNReal.ofReal (1 - u))]
    (f : ℝ → ℝ) (hf : Measurable f) {Cf : ℝ}
    (hbd : ∀ x, |f x| ≤ Cf * (1 - clamp01 x)) :
    ∑' j, ∫ u in band β j, f u ∂νt = ∫ u, f u ∂νt := by
  have hint : Integrable f νt := by
    refine Integrable.mono'
      ((integrable_one_sub_clamp νt hsupp).const_mul Cf)
      hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hbd x
  have hself : νt.restrict (⋃ j, band β j) = νt :=
    Measure.restrict_eq_self_of_ae_mem
      (hsupp.mono fun u hu => Ico_subset_iUnion_band hβ hu)
  have hcup : ∫ u in ⋃ j, band β j, f u ∂νt = ∫ u, f u ∂νt := by
    rw [show (∫ u in ⋃ j, band β j, f u ∂νt)
      = ∫ u, f u ∂(νt.restrict (⋃ j, band β j)) from rfl, hself]
  rw [← hcup]
  exact (integral_iUnion (fun j => measurableSet_band β j)
    (pairwise_disjoint_band hβ) hint.integrableOn).symm

/-- **The cumulant certificate in Lévy form**: the layered construction
realizes the compound-Poisson moments
`E[W^k] = exp(ak + ∫(u^k − 1) dνt)` of the printed triplet `(a, 0, ν)`.
Together with `cpLawInf_unique` this pins the law of the paper's
infinite-activity multiplier. -/
theorem integral_pow_cpLawInf_levy {β : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (νt : Measure ℝ) (hsupp : ∀ᵐ u ∂νt, u ∈ Set.Ico 0 1)
    [IsFiniteMeasure (νt.withDensity fun u => ENNReal.ofReal (1 - u))]
    (a : ℝ) (k : ℕ) :
    ∫ w, w ^ k ∂(cpLawInf a fun j => νt.restrict (band β j))
      = Real.exp (a * k + ∫ u, (u ^ k - 1) ∂νt) := by
  haveI : ∀ j, IsFiniteMeasure ((fun j => νt.restrict (band β j)) j) :=
    fun j => isFiniteMeasure_restrict_band hβ νt j
  obtain ⟨hsum, _⟩ := tilt_bands_summable hβ νt hsupp
  rw [integral_pow_cpLawInf a _ hsum k]
  congr 1
  have hdom : ∀ x : ℝ, |clamp01 x ^ k - 1| ≤ (k : ℝ) * (1 - clamp01 x) := by
    intro x
    have h1 := (clamp01_mem_Icc x).1
    have h2 := (clamp01_mem_Icc x).2
    have h3 := pow_le_one₀ h1 h2 (n := k)
    have h4 := one_sub_pow_le ⟨h1, h2⟩ k
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hbands := tsum_setIntegral_bands hβ νt hsupp
    (fun u => clamp01 u ^ k - 1)
    ((measurable_clamp01.pow_const k).sub measurable_const) hdom
  have hcongr : ∫ u, (clamp01 u ^ k - 1) ∂νt
      = ∫ u, (u ^ k - 1) ∂νt := by
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with u hu
    rw [clamp01_eq_self ⟨hu.1, hu.2.le⟩]
  rw [← hcongr, ← hbands]

/-- **Uniqueness**: any probability law on `[0, e^a]` with the
compound-Poisson moments of the triplet equals the layered
construction (Hausdorff determinacy). -/
theorem cpLawInf_unique {β : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (νt : Measure ℝ) (hsupp : ∀ᵐ u ∂νt, u ∈ Set.Ico 0 1)
    [IsFiniteMeasure (νt.withDensity fun u => ENNReal.ofReal (1 - u))]
    (a : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμsupp : ∀ᵐ w ∂μ, w ∈ Set.Icc (0 : ℝ) (Real.exp a))
    (hμmom : ∀ k : ℕ, ∫ w, w ^ k ∂μ
      = Real.exp (a * k + ∫ u, (u ^ k - 1) ∂νt)) :
    μ = cpLawInf a fun j => νt.restrict (band β j) := by
  haveI : ∀ j, IsFiniteMeasure ((fun j => νt.restrict (band β j)) j) :=
    fun j => isFiniteMeasure_restrict_band hβ νt j
  refine ext_of_moments_eq hμsupp
    (cpLawInf_ae_mem_Icc a fun j => νt.restrict (band β j)) fun m => ?_
  rw [hμmom m, integral_pow_cpLawInf_levy hβ νt hsupp a m]

/-! ## The paper-constant form `W₁ ≤ K_∞ √ε` -/

/-- The explicit propagation constant at `k = 1`:
`K_∞ = 4e^a(1/(1−β) + 1/(1−β)²)·√((1+β)‖η‖)`.  The paper's `e^{a₀+1}`
carries an extra `e` of drift slack that the `k = 1` rigidity makes
unnecessary, so this constant is admissible and sharper. -/
noncomputable def Kinfty (a β normEta : ℝ) : ℝ :=
  4 * Real.exp a * (1 / (1 - β) + 1 / (1 - β) ^ 2)
    * Real.sqrt ((1 + β) * normEta)

/-- **Theorem 11 (Unconditional Propagation, paper form)**: under the
Theorem-10 moment bounds with residual size `ε ≤ ε₀ = ‖η‖/(4(1+β))`,
`W₁(law W, law W₀) ≤ K_∞ √ε`. -/
theorem theorem11_rate_upper {β ε : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (νt : Measure ℝ) (hsupp : ∀ᵐ u ∂νt, u ∈ Set.Ico 0 1)
    [IsFiniteMeasure (νt.withDensity fun u => ENNReal.ofReal (1 - u))]
    (hε : 0 ≤ ε)
    (hvar : ∫ u, (u - β) ^ 2
        ∂(νt.withDensity fun u => ENNReal.ofReal (1 - u))
      ≤ (1 + β) * ε)
    (habs : ∫ u, |u - β|
        ∂(νt.withDensity fun u => ENNReal.ofReal (1 - u))
      ≤ Real.sqrt ((1 + β) * ((νt.withDensity fun u =>
          ENNReal.ofReal (1 - u)).real Set.univ) * ε))
    (a : ℝ)
    (_ha : a = (νt.withDensity fun u =>
      ENNReal.ofReal (1 - u)).real Set.univ)
    (lam : ℝ≥0)
    (hlam : (lam : ℝ) * (1 - β)
      = (νt.withDensity fun u => ENNReal.ofReal (1 - u)).real Set.univ)
    (hε₀ : ε ≤ (νt.withDensity fun u =>
      ENNReal.ofReal (1 - u)).real Set.univ / (4 * (1 + β))) :
    W1 (cpLawInf a fun j => νt.restrict (band β j))
        (logPoissonLaw a (Real.log β) lam)
      ≤ Kinfty a β ((νt.withDensity fun u =>
          ENNReal.ofReal (1 - u)).real Set.univ) * Real.sqrt ε := by
  have hβ1 : (0 : ℝ) < 1 - β := by linarith [hβ.2]
  have hβ0 : (0 : ℝ) < 1 + β := by linarith [hβ.1]
  set M : ℝ := (νt.withDensity fun u =>
    ENNReal.ofReal (1 - u)).real Set.univ with hMdef
  have hM0 : 0 ≤ M := measureReal_nonneg
  refine (theorem11_W1_upper hβ νt hsupp hvar habs a _ha lam hlam).trans ?_
  -- split √((1+β)Mε) = √((1+β)M)·√ε and absorb the O(ε) term
  have hsqrt : Real.sqrt ((1 + β) * M * ε)
      = Real.sqrt ((1 + β) * M) * Real.sqrt ε := by
    rw [Real.sqrt_mul (by positivity)]
  have habsorb : 8 * ((1 + β) * ε) / (1 - β) ^ 2
      ≤ 4 * Real.sqrt ((1 + β) * M) * Real.sqrt ε / (1 - β) ^ 2 := by
    rw [div_le_div_iff_of_pos_right (by positivity)]
    -- 8(1+β)ε ≤ 4√((1+β)M)√ε
    have hε' : ε = Real.sqrt ε * Real.sqrt ε := (Real.mul_self_sqrt hε).symm
    have hkey : 2 * (1 + β) * Real.sqrt ε ≤ Real.sqrt ((1 + β) * M) := by
      rw [show (2 : ℝ) * (1 + β) * Real.sqrt ε
        = Real.sqrt ((2 * (1 + β)) ^ 2 * ε) from ?_]
      · refine Real.sqrt_le_sqrt ?_
        have h5 : 4 * (1 + β) * ε ≤ M := by
          rw [le_div_iff₀ (by positivity)] at hε₀
          linarith
        nlinarith [h5, hβ0, hε]
      · rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    calc 8 * ((1 + β) * ε)
        = 4 * (2 * (1 + β) * Real.sqrt ε) * Real.sqrt ε := by
          linear_combination (-(8 : ℝ) * (1 + β)) * Real.mul_self_sqrt hε
      _ ≤ 4 * Real.sqrt ((1 + β) * M) * Real.sqrt ε := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg ε)
          nlinarith [hkey]
  calc Real.exp a * (4 * Real.sqrt ((1 + β) * M * ε) / (1 - β)
        + 8 * ((1 + β) * ε) / (1 - β) ^ 2)
      ≤ Real.exp a * (4 * (Real.sqrt ((1 + β) * M) * Real.sqrt ε) / (1 - β)
        + 4 * Real.sqrt ((1 + β) * M) * Real.sqrt ε / (1 - β) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos a).le
        rw [hsqrt]
        exact add_le_add le_rfl habsorb
    _ = Kinfty a β M * Real.sqrt ε := by
        unfold Kinfty
        field_simp

/-! ## End-to-end: Theorem 11 from the Theorem-10 hypotheses

The cumulant-level hypotheses of Theorem 10 (the printed `(a, σ², ν)`
triplet with A1 residuals of size `ε`) propagate to the multiplier law:
`W₁(law W, law W₀) ≤ K_∞ √ε`, at `k = 1`. -/

theorem theorem11_from_theorem10 {ν : Measure ℝ} {a σ2 β ε : ℝ}
    (hσ2 : 0 ≤ σ2) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hgint : ∀ p : ℝ, 0 ≤ p → Integrable (gIntegrand 1 p) ν)
    (hres : ∀ m : ℕ, |lkPhi a σ2 ν 1 ((m + 1 : ℕ) * 1)
      - (1 - β) * lkC0 a ν 1 - β * lkPhi a σ2 ν 1 (m * 1)| ≤ ε)
    (hmass : 0 < (tiltedMeasure ν 1).real Set.univ)
    (hε₀ : ε ≤ (tiltedMeasure ν 1).real Set.univ / (4 * (1 + β)))
    (aW : ℝ) (haW : aW = (tiltedMeasure ν 1).real Set.univ)
    (lam : ℝ≥0)
    (hlam : (lam : ℝ) * (1 - β) = (tiltedMeasure ν 1).real Set.univ) :
    W1 (cpLawInf aW fun j =>
        ((ν.restrict (Set.Iio (0 : ℝ))).map fun x =>
          Real.exp (1 * x)).restrict (band β j))
      (logPoissonLaw aW (Real.log β) lam)
      ≤ Kinfty aW β ((tiltedMeasure ν 1).real Set.univ)
          * Real.sqrt ε := by
  have hk : (0 : ℝ) < 1 := one_pos
  obtain ⟨hσ0, hjump, hcomp, _hlim, _ht, _hdict⟩ :=
    theorem10_step0 hk hσ2 hβ hgint hres
  haveI hfin : IsFiniteMeasure (tiltedMeasure ν 1) :=
    isFiniteMeasure_tiltedMeasure hk
      (nu_Iio_lt_top hk (hgint 0 le_rfl)) hcomp
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hres 0)
  have htilt : tiltedMeasure ν 1
      = ((ν.restrict (Set.Iio (0 : ℝ))).map fun x =>
          Real.exp (1 * x)).withDensity
            (fun u => ENNReal.ofReal (1 - u)) := rfl
  have hsupp : ∀ᵐ u ∂((ν.restrict (Set.Iio (0 : ℝ))).map fun x =>
      Real.exp (1 * x)), u ∈ Set.Ico 0 1 := by
    filter_upwards [ae_map_mem_Ioo (ν := ν) hk] with u hu
    exact ⟨hu.1.le, hu.2⟩
  haveI : IsFiniteMeasure (((ν.restrict (Set.Iio (0 : ℝ))).map fun x =>
      Real.exp (1 * x)).withDensity fun u => ENNReal.ofReal (1 - u)) :=
    htilt ▸ hfin
  have hvar := theorem10_variance_known hk hσ2 hβ hgint hres
  have habs0 := theorem10_wasserstein_known hk hσ2 hβ hgint hres hmass
  -- de-normalize the Wasserstein-form bound
  have habs : ∫ u, |u - β| ∂(tiltedMeasure ν 1)
      ≤ Real.sqrt ((1 + β) * (tiltedMeasure ν 1).real Set.univ * ε) := by
    have hM := hmass
    rw [inv_mul_le_iff₀ hM] at habs0
    refine habs0.trans (le_of_eq ?_)
    have hXnn : (0 : ℝ) ≤ (1 + β) * (tiltedMeasure ν 1).real Set.univ * ε :=
      mul_nonneg (mul_nonneg (by linarith [hβ.1]) measureReal_nonneg) hε
    rw [show (1 + β) * ε / (tiltedMeasure ν 1).real Set.univ
      = ((1 + β) * (tiltedMeasure ν 1).real Set.univ * ε)
          / ((tiltedMeasure ν 1).real Set.univ) ^ 2 by
        field_simp, Real.sqrt_div hXnn, Real.sqrt_sq hM.le, mul_comm,
      div_mul_cancel₀ _ hM.ne']
  rw [htilt] at hvar habs hε₀ haW hlam ⊢
  exact theorem11_rate_upper hβ _ hsupp hε hvar habs aW haW lam hlam hε₀

/-! ## The capstone: the rate `Θ(√ε)` is exact

For the Theorem-12 two-atom family, the constructed layered law *is*
`twoAtomCPLaw` (Hausdorff determinacy through the cumulant
certificates), so Theorems 11 and 12 bracket the same `W₁` distance:
`c₁ √ε(d) ≤ W₁ ≤ c₃ √ε(d)` with both constants explicit.  This is the
paper's closing claim: "combined with Theorem 11, the exact rate is
`Θ(√ε)`." -/

/-- Integration of an arbitrary function against the two-atom tilted
measure `η_d`. -/
theorem integral_etaD_general {A : ℝ} (hA : 0 ≤ A) (β d : ℝ) (f : ℝ → ℝ) :
    ∫ u, f u ∂(etaD A β d) = A / 2 * (f (β - d) + f (β + d)) := by
  unfold etaD
  rw [integral_smul_measure, integral_add_measure
    (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top),
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul]

/-- The two-atom tilted measure has total mass `A` (drift rigidity). -/
theorem etaD_real_univ {A : ℝ} (hA : 0 ≤ A) (β d : ℝ) :
    (etaD A β d).real Set.univ = A := by
  have h := integral_etaD_general hA β d fun _ => (1 : ℝ)
  rw [integral_const, smul_eq_mul, mul_one] at h
  rw [h]
  ring

theorem isFiniteMeasure_etaD (A β d : ℝ) :
    IsFiniteMeasure (etaD A β d) := by
  unfold etaD
  refine ⟨?_⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- The two-atom Lévy measure lives where its atoms do. -/
theorem twoAtomLevy_ae_mem {s t : ℝ} (l1 l2 : ℝ≥0) {S : Set ℝ}
    (hS : MeasurableSet S) (hs : s ∈ S) (ht : t ∈ S) :
    ∀ᵐ u ∂(twoAtomLevy s t l1 l2), u ∈ S := by
  unfold twoAtomLevy
  rw [ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure ((ae_dirac_iff hS).mpr hs) _,
    Measure.ae_smul_measure ((ae_dirac_iff hS).mpr ht) _⟩

/-- Both atoms of the Theorem-12 family lie in the macroscopic band. -/
theorem atoms_mem_band0 {β d : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2)) :
    β - d ∈ band β 0 ∧ β + d ∈ band β 0 := by
  have h1 := hβ.1
  have h2 := hβ.2
  have h3 := hd.1
  have h4 := hd.2
  constructor
  · exact ⟨by nlinarith, by nlinarith⟩
  · exact ⟨by nlinarith, by nlinarith⟩

open Classical in
/-- The band restrictions of the two-atom Lévy measure: everything sits
in the macroscopic band. -/
theorem twoAtomLevy_restrict_band {β d : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2)) (l1 l2 : ℝ≥0) :
    (twoAtomLevy (β - d) (β + d) l1 l2).restrict (band β 0)
        = twoAtomLevy (β - d) (β + d) l1 l2
      ∧ ∀ j : ℕ, (twoAtomLevy (β - d) (β + d) l1 l2).restrict
          (band β (j + 1)) = 0 := by
  obtain ⟨hm1, hm2⟩ := atoms_mem_band0 hβ hd
  have h1 := hβ.1
  have h2 := hβ.2
  have h3 := hd.1
  have h4 := hd.2
  constructor
  · unfold twoAtomLevy
    rw [Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
      restrict_dirac, restrict_dirac, if_pos hm1, if_pos hm2]
  · intro j
    have hnot1 : β - d ∉ band β (j + 1) := by
      intro hmem
      have := band_succ_subset_Ioi β j hmem
      rw [Set.mem_Ioi] at this
      have h5 : (1 - β) / 2 / 2 ^ j ≤ (1 - β) / 2 := by
        rw [div_le_iff₀ (pow_pos two_pos j)]
        have h6 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
        nlinarith
      nlinarith
    have hnot2 : β + d ∉ band β (j + 1) := by
      intro hmem
      have := band_succ_subset_Ioi β j hmem
      rw [Set.mem_Ioi] at this
      have h5 : (1 - β) / 2 / 2 ^ j ≤ (1 - β) / 2 := by
        rw [div_le_iff₀ (pow_pos two_pos j)]
        have h6 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
        nlinarith
      nlinarith
    unfold twoAtomLevy
    rw [Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
      restrict_dirac, restrict_dirac, if_neg hnot1, if_neg hnot2]
    simp

/-- **The identification**: the layered construction over the two-atom
Lévy measure *is* `CompoundPoisson.lean`'s `twoAtomCPLaw` — moments match through the
cumulant certificates, and Hausdorff determinacy does the rest. -/
theorem twoAtomCPLaw_eq_cpLawInf {β A d : ℝ}
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hA : 0 < A)
    (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2)) (lam1 lam2 : ℝ≥0)
    (hl1 : (lam1 : ℝ) = A / 2 / (1 - (β - d)))
    (hl2 : (lam2 : ℝ) = A / 2 / (1 - (β + d))) :
    twoAtomCPLaw A (β - d) (β + d) lam1 lam2
      = cpLawInf A fun j =>
          (twoAtomLevy (β - d) (β + d) lam1 lam2).restrict (band β j) := by
  have h1 := hβ.1
  have h2 := hβ.2
  have h3 := hd.1
  have h4 := hd.2
  have hsupp : ∀ᵐ u ∂(twoAtomLevy (β - d) (β + d) lam1 lam2),
      u ∈ Set.Ico 0 1 := by
    refine twoAtomLevy_ae_mem lam1 lam2 measurableSet_Ico ?_ ?_
    · exact ⟨by nlinarith, by nlinarith⟩
    · exact ⟨by nlinarith, by nlinarith⟩
  haveI : IsFiniteMeasure
      ((twoAtomLevy (β - d) (β + d) lam1 lam2).withDensity fun u =>
        ENNReal.ofReal (1 - u)) :=
    (twoAtomLevy_tilt_eq_etaD hβ hA.le hd lam1 lam2 hl1 hl2) ▸
      isFiniteMeasure_etaD A β d
  refine cpLawInf_unique hβ _ hsupp A _
    (twoAtomCPLaw_ae_mem_Icc A lam1 lam2
      ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩)
    fun k => ?_
  exact integral_pow_twoAtomCPLaw_CGF A (β - d) (β + d) lam1 lam2 k

/-- **Theorems 11 + 12 (the exact rate)**: for the attaining family the
two propagation bounds bracket the same Wasserstein distance,
`c₁·√ε(d) ≤ W₁ ≤ c₃·√ε(d)` with `c₃ = 8e^A√(A|ln r|)/(1−β)` explicit —
"the exact rate is `Θ(√ε)`". -/
theorem theorem11_12_theta {β A r d : ℝ}
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hA : 0 < A) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioc 0 (β * (1 - β) / 2))
    (lam1 lam2 lam : ℝ≥0)
    (hl1 : (lam1 : ℝ) = A / 2 / (1 - (β - d)))
    (hl2 : (lam2 : ℝ) = A / 2 / (1 - (β + d)))
    (hlam : (lam : ℝ) = A / (1 - β)) :
    c1 A β r * Real.sqrt (epsResidual A β d r)
        ≤ W1 (twoAtomCPLaw A (β - d) (β + d) lam1 lam2)
            (logPoissonLaw A (Real.log β) lam)
      ∧ W1 (twoAtomCPLaw A (β - d) (β + d) lam1 lam2)
            (logPoissonLaw A (Real.log β) lam)
        ≤ 8 * Real.exp A * Real.sqrt (A * |Real.log r|) / (1 - β)
            * Real.sqrt (epsResidual A β d r) := by
  have hβ1 : (0 : ℝ) < 1 - β := by linarith [hβ.2]
  refine ⟨theorem12_rate_lower hβ hA hr hd lam1 lam2 lam hl1 hl2 hlam, ?_⟩
  rw [twoAtomCPLaw_eq_cpLawInf hβ hA hd lam1 lam2 hl1 hl2]
  have hsupp : ∀ᵐ u ∂(twoAtomLevy (β - d) (β + d) lam1 lam2),
      u ∈ Set.Ico 0 1 := by
    have h1 := hβ.1
    have h2 := hβ.2
    have h3 := hd.1
    have h4 := hd.2
    refine twoAtomLevy_ae_mem lam1 lam2 measurableSet_Ico ?_ ?_
    · exact ⟨by nlinarith, by nlinarith⟩
    · exact ⟨by nlinarith, by nlinarith⟩
  have htilt := twoAtomLevy_tilt_eq_etaD hβ hA.le hd lam1 lam2 hl1 hl2
  haveI : IsFiniteMeasure
      ((twoAtomLevy (β - d) (β + d) lam1 lam2).withDensity fun u =>
        ENNReal.ofReal (1 - u)) := htilt ▸ isFiniteMeasure_etaD A β d
  -- the moment inputs, exactly
  have hvar : ∫ u, (u - β) ^ 2
      ∂((twoAtomLevy (β - d) (β + d) lam1 lam2).withDensity fun u =>
        ENNReal.ofReal (1 - u)) ≤ A * d ^ 2 := by
    rw [htilt, integral_etaD_general hA.le β d fun u => (u - β) ^ 2]
    have : (β - d - β) ^ 2 = d ^ 2 := by ring
    rw [this, show (β + d - β) ^ 2 = d ^ 2 by ring]
    refine le_of_eq ?_
    ring
  have habs : ∫ u, |u - β|
      ∂((twoAtomLevy (β - d) (β + d) lam1 lam2).withDensity fun u =>
        ENNReal.ofReal (1 - u)) ≤ A * d := by
    rw [htilt, integral_etaD_general hA.le β d fun u => |u - β|]
    rw [show β - d - β = -d by ring, show β + d - β = d by ring,
      abs_neg, abs_of_pos hd.1]
    refine le_of_eq ?_
    ring
  have hmassA : ((twoAtomLevy (β - d) (β + d) lam1 lam2).withDensity
      fun u => ENNReal.ofReal (1 - u)).real Set.univ = A := by
    rw [htilt]
    exact etaD_real_univ hA.le β d
  have hlam' : (lam : ℝ) * (1 - β)
      = ((twoAtomLevy (β - d) (β + d) lam1 lam2).withDensity fun u =>
          ENNReal.ofReal (1 - u)).real Set.univ := by
    rw [hmassA, hlam, div_mul_cancel₀ _ hβ1.ne']
  refine (theorem11_W1_upper hβ _ hsupp hvar habs A
    (by rw [hmassA]) lam hlam').trans ?_
  -- d-algebra: absorb the d² term and convert d to √ε(d)
  have hlnr : 0 < |Real.log r| :=
    abs_pos.mpr (Real.log_neg hr.1 hr.2).ne
  have hεnn : 0 ≤ epsResidual A β d r :=
    le_trans (div_nonneg (mul_nonneg hA.le (sq_nonneg d)) (abs_nonneg _))
      (theorem12_residual_lower (r := r) hβ hA.le hd)
  have hd2 : d ^ 2 ≤ epsResidual A β d r * |Real.log r| / A := by
    have h := theorem12_residual_lower (r := r) hβ hA.le hd
    rw [div_le_iff₀ hlnr] at h
    rw [le_div_iff₀ hA]
    linarith
  have hdle : d ≤ Real.sqrt (epsResidual A β d r * |Real.log r| / A) := by
    have h := Real.sqrt_le_sqrt hd2
    rwa [Real.sqrt_sq hd.1.le] at h
  have hstep1 : Real.exp A * (4 * (A * d) / (1 - β)
      + 8 * (A * d ^ 2) / (1 - β) ^ 2)
      ≤ Real.exp A * (8 * A * d / (1 - β)) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos A).le
    rw [div_add_div _ _ hβ1.ne' (by positivity), div_le_div_iff₀
      (by positivity) hβ1]
    have hdh : 2 * d ≤ 1 - β := by nlinarith [hd.2, hβ.1, hβ.2]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg
      (by linarith : (0 : ℝ) ≤ 4 * A) hd.1.le) hβ1.le)
      (by linarith : (0 : ℝ) ≤ 1 - β - 2 * d), hd.1, hA, hβ1]
  refine hstep1.trans ?_
  -- 8Ae^A d/(1−β) ≤ 8e^A√(A|ln r|)/(1−β) · √ε
  have hAd : A * d ≤ Real.sqrt (A * |Real.log r|)
      * Real.sqrt (epsResidual A β d r) := by
    calc A * d ≤ A * Real.sqrt (epsResidual A β d r * |Real.log r| / A) :=
          mul_le_mul_of_nonneg_left hdle hA.le
      _ = Real.sqrt (A ^ 2 * (epsResidual A β d r * |Real.log r| / A)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hA.le]
      _ = Real.sqrt (A * |Real.log r| * epsResidual A β d r) := by
          congr 1
          field_simp
      _ = Real.sqrt (A * |Real.log r|)
            * Real.sqrt (epsResidual A β d r) := by
          rw [Real.sqrt_mul (by positivity)]
  calc Real.exp A * (8 * A * d / (1 - β))
      = 8 * Real.exp A / (1 - β) * (A * d) := by ring
    _ ≤ 8 * Real.exp A / (1 - β) * (Real.sqrt (A * |Real.log r|)
          * Real.sqrt (epsResidual A β d r)) :=
        mul_le_mul_of_nonneg_left hAd (by positivity)
    _ = 8 * Real.exp A * Real.sqrt (A * |Real.log r|) / (1 - β)
          * Real.sqrt (epsResidual A β d r) := by ring

end Freeburg

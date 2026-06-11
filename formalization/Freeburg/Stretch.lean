/-
Freeburg formalization — Stretch.lean
Lemma 2(i) (Boundedness) of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632.
-/
import Mathlib

/-!
# Boundedness: A1 moments force `essSup V = r^{γk}`

Lemma 2(i) of arXiv:2604.01632 states that for `V = W^k`, the A1
lattice moments `E[V^m] = r^{ζ_{km}}` with
`ζ_{km} = γkm + C(1−β^m)` force `V` to be essentially bounded with
`essSup V = r^{γk}` (hence `essSup W = r^γ`).

The paper proves this via `‖V‖_{L^m} ↑ ‖V‖_{L^∞}`.  Mathlib (as of
v4.30.0-rc2) does not provide the `p → ∞` limit of `L^p` norms, but the
paper's moment sequence has more structure than an abstract convergent
sequence of norms: it is *geometrically sandwiched*,

  `Klo · c^m ≤ E[V^m] ≤ Khi · c^m`,  `c = r^{γk}`,
  `Klo = r^C ≤ r^{C(1−β^m)} ≤ 1 = Khi`,

and for such moments the essential-supremum identification is elementary:

* upper bound: `μ{V ≥ c+δ} ≤ Khi (c/(c+δ))^m → 0` (Markov via a set
  integral; no `m`-th roots needed);
* lower bound: `V ≤ c′ < c` a.e. would give `Klo ≤ (c′/c)^m → 0`.

Consequently this file is **sorry-free**: the stretch goal is proved in
full, not axiomatized.

Main results:

* `Freeburg.ae_le_of_pow_integral_le` — geometric upper moments give
  `V ≤ c` a.e.
* `Freeburg.not_ae_le_of_le_pow_integral` — geometric lower moments
  forbid any essential bound `c′ < c`.
* `Freeburg.essSup_eq_of_geometric_moment_sandwich` — together:
  `essSup V = c`.
* `Freeburg.rpow_A1_moment_sandwich` — the A1 moments
  `r^{γkm + C(1−β^m)}` are geometrically sandwiched with
  `c = r^{γk}`, `Klo = r^C`, `Khi = 1`.
* `Freeburg.lemma2_boundedness` — **Lemma 2(i)**: A1 moments give
  `essSup V = r^{γk}`.
-/

open MeasureTheory Filter

namespace Freeburg

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Upper half of Lemma 2(i)** of arXiv:2604.01632 (abstract form):
if a nonnegative random variable has all moments bounded by `Khi · c^m`,
then `V ≤ c` almost everywhere.  (Markov's inequality at level `c + δ`
gives `μ{V ≥ c+δ} ≤ Khi (c/(c+δ))^m → 0`.) -/
theorem ae_le_of_pow_integral_le [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (hVm : Measurable V) (hV0 : 0 ≤ᵐ[μ] V)
    (c Khi : ℝ) (hc : 0 ≤ c)
    (hint : ∀ m : ℕ, Integrable (fun ω => V ω ^ m) μ)
    (hup : ∀ m : ℕ, ∫ ω, V ω ^ m ∂μ ≤ Khi * c ^ m) :
    ∀ᵐ ω ∂μ, V ω ≤ c := by
  -- Step 1: each super-level set {V ≥ c + δ} is null.
  have step : ∀ δ : ℝ, 0 < δ → μ {ω | c + δ ≤ V ω} = 0 := by
    intro δ hδ
    set S := {ω | c + δ ≤ V ω} with hSdef
    have hS : MeasurableSet S := measurableSet_le measurable_const hVm
    have hcd : (0 : ℝ) < c + δ := by linarith
    -- Markov: (c+δ)^m μ(S) ≤ ∫ V^m ≤ Khi c^m.
    have hbound : ∀ m : ℕ, (c + δ) ^ m * μ.real S ≤ Khi * c ^ m := by
      intro m
      have h1 : (c + δ) ^ m * μ.real S ≤ ∫ ω in S, V ω ^ m ∂μ := by
        refine setIntegral_ge_of_const_le_real hS (measure_ne_top μ S)
          (fun ω hω => ?_) ((hint m).integrableOn)
        exact pow_le_pow_left₀ hcd.le hω m
      have h2 : ∫ ω in S, V ω ^ m ∂μ ≤ ∫ ω, V ω ^ m ∂μ := by
        refine setIntegral_le_integral (hint m) ?_
        filter_upwards [hV0] with ω h using pow_nonneg h m
      linarith [hup m]
    -- Divide and let m → ∞.
    have hratio : ∀ m : ℕ, μ.real S ≤ Khi * (c / (c + δ)) ^ m := by
      intro m
      have h3 : μ.real S ≤ Khi * c ^ m / (c + δ) ^ m := by
        rw [le_div_iff₀ (pow_pos hcd m)]
        nlinarith [hbound m]
      calc μ.real S ≤ Khi * c ^ m / (c + δ) ^ m := h3
        _ = Khi * (c / (c + δ)) ^ m := by rw [div_pow, mul_div_assoc]
    have hlim : Tendsto (fun m : ℕ => Khi * (c / (c + δ)) ^ m)
        atTop (nhds 0) := by
      have h0 : Tendsto (fun m : ℕ => (c / (c + δ)) ^ m) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hc hcd.le)
          ((div_lt_one hcd).mpr (by linarith))
      simpa using h0.const_mul Khi
    have hle0 : μ.real S ≤ 0 := ge_of_tendsto' hlim hratio
    have hzero : μ.real S = 0 := le_antisymm hle0 measureReal_nonneg
    exact (measureReal_eq_zero_iff (measure_ne_top μ S)).mp hzero
  -- Step 2: union over δ = 1/(n+1).
  rw [ae_iff]
  have hsub : {ω | ¬ V ω ≤ c}
      ⊆ ⋃ n : ℕ, {ω | c + 1 / ((n : ℝ) + 1) ≤ V ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, not_le] at hω
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < V ω - c by linarith)
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    simp only [Set.mem_setOf_eq]
    linarith
  refine measure_mono_null hsub (measure_iUnion_null fun n => step _ ?_)
  positivity

/-- **Lower half of Lemma 2(i)** of arXiv:2604.01632 (abstract form):
if all moments are bounded below by `Klo · c^m` with `Klo > 0 < c`, then
no constant `c′ < c` is an essential upper bound for `V`.
(Otherwise `Klo ≤ (c′/c)^m → 0`.) -/
theorem not_ae_le_of_le_pow_integral [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (hV0 : 0 ≤ᵐ[μ] V)
    (c c' Klo : ℝ) (hKlo : 0 < Klo) (hc : 0 < c)
    (hint : ∀ m : ℕ, Integrable (fun ω => V ω ^ m) μ)
    (hlo : ∀ m : ℕ, Klo * c ^ m ≤ ∫ ω, V ω ^ m ∂μ)
    (hc' : c' < c) :
    ¬ ∀ᵐ ω ∂μ, V ω ≤ c' := by
  intro hae
  -- a.e. 0 ≤ V ≤ c′ forces 0 ≤ c′ (the space is nonempty in measure).
  have hc'0 : 0 ≤ c' := by
    obtain ⟨ω, h1, h2⟩ := (hae.and hV0).exists
    exact le_trans h2 h1
  have hup : ∀ m : ℕ, ∫ ω, V ω ^ m ∂μ ≤ c' ^ m := by
    intro m
    calc ∫ ω, V ω ^ m ∂μ ≤ ∫ _ω, c' ^ m ∂μ := by
          refine integral_mono_ae (hint m) (integrable_const _) ?_
          filter_upwards [hae, hV0] with ω h1 h2
          exact pow_le_pow_left₀ h2 h1 m
      _ = c' ^ m := by simp
  have hKlo_le : ∀ m : ℕ, Klo ≤ (c' / c) ^ m := by
    intro m
    rw [div_pow, le_div_iff₀ (pow_pos hc m)]
    linarith [hlo m, hup m]
  have hlim : Tendsto (fun m : ℕ => (c' / c) ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hc'0 hc.le)
      ((div_lt_one hc).mpr hc')
  have : Klo ≤ 0 := ge_of_tendsto' hlim hKlo_le
  linarith

/-- **Lemma 2(i)** of arXiv:2604.01632, abstract form: geometrically
sandwiched moments `Klo c^m ≤ E[V^m] ≤ Khi c^m` (with `Klo > 0 < c`)
identify the essential supremum: `essSup V = c`.
(The paper's `‖V‖_{L^m} → ‖V‖_{L^∞}` argument is replaced by this
elementary two-sided estimate, which its moment sequence satisfies.) -/
theorem essSup_eq_of_geometric_moment_sandwich [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (hVm : Measurable V) (hV0 : 0 ≤ᵐ[μ] V)
    (c Klo Khi : ℝ) (hc : 0 < c) (hKlo : 0 < Klo)
    (hint : ∀ m : ℕ, Integrable (fun ω => V ω ^ m) μ)
    (hlo : ∀ m : ℕ, Klo * c ^ m ≤ ∫ ω, V ω ^ m ∂μ)
    (hup : ∀ m : ℕ, ∫ ω, V ω ^ m ∂μ ≤ Khi * c ^ m) :
    essSup V μ = c := by
  have ha : ∀ᵐ ω ∂μ, V ω ≤ c :=
    ae_le_of_pow_integral_le V hVm hV0 c Khi hc.le hint hup
  have hb : ∀ c' : ℝ, c' < c → ¬ ∀ᵐ ω ∂μ, V ω ≤ c' := fun c' hc' =>
    not_ae_le_of_le_pow_integral V hV0 c c' Klo hKlo hc hint hlo hc'
  rw [essSup_eq_sInf]
  have hmem : c ∈ {a : ℝ | μ {x | a < V x} = 0} := by
    simp only [Set.mem_setOf_eq]
    have : {x | c < V x} = {x | ¬ V x ≤ c} := by
      ext x; simp [not_le]
    rw [this]
    exact ae_iff.mp ha
  have hlb : ∀ a ∈ {a : ℝ | μ {x | a < V x} = 0}, c ≤ a := by
    intro a hamem
    by_contra hcle
    have hlt : a < c := not_le.mp hcle
    refine hb a hlt ?_
    rw [ae_iff]
    have : {ω | ¬ V ω ≤ a} = {x | a < V x} := by
      ext x; simp [not_le]
    rw [this]
    exact hamem
  exact le_antisymm (csInf_le ⟨c, hlb⟩ hmem) (le_csInf ⟨c, hmem⟩ hlb)

/-- The A1 lattice moments `r^{γkm + C(1−β^m)}` of Lemma 2 of
arXiv:2604.01632 are geometrically sandwiched:
`r^C (r^{γk})^m ≤ r^{γkm + C(1−β^m)} ≤ 1·(r^{γk})^m`
(the exponent `C(1−β^m)` lies in `[0, C]` and `r < 1`). -/
theorem rpow_A1_moment_sandwich (r γk C β : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hC : 0 ≤ C) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    r ^ C * (r ^ γk) ^ m ≤ r ^ (γk * m + C * (1 - β ^ m)) ∧
      r ^ (γk * m + C * (1 - β ^ m)) ≤ 1 * (r ^ γk) ^ m := by
  have hr0 : (0 : ℝ) < r := hr.1
  have hrm : (r ^ γk) ^ m = r ^ (γk * (m : ℝ)) := by
    rw [← Real.rpow_natCast (r ^ γk) m, ← Real.rpow_mul hr0.le]
  have hsplit : r ^ (γk * (m : ℝ) + C * (1 - β ^ m))
      = r ^ (γk * (m : ℝ)) * r ^ (C * (1 - β ^ m)) := Real.rpow_add hr0 _ _
  have hβm1 : β ^ m ≤ 1 := pow_le_one₀ hβ.1.le hβ.2.le
  have hβm0 : 0 < β ^ m := pow_pos hβ.1 m
  have hexp0 : 0 ≤ C * (1 - β ^ m) := mul_nonneg hC (by linarith)
  have hexpC : C * (1 - β ^ m) ≤ C := by nlinarith
  constructor
  · rw [hsplit, hrm, mul_comm (r ^ C)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr0.le _)
    exact Real.rpow_le_rpow_of_exponent_ge hr0 hr.2.le hexpC
  · rw [hsplit, hrm, one_mul]
    nth_rewrite 2 [← mul_one (r ^ (γk * (m : ℝ)))]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr0.le _)
    exact Real.rpow_le_one hr0.le hr.2.le hexp0

/-- **Lemma 2(i) (Boundedness)** of arXiv:2604.01632: let `V = W^k ≥ 0`
on a probability space with the A1 lattice moments
`E[V^m] = r^{ζ_{km}}`, `ζ_{km} = γkm + C(1−β^m)` (here `γk` is a single
real parameter, the paper's `γ·k`).  Then `V` is essentially bounded
with `essSup V = r^{γk}`.  (Taking `k`-th roots, `essSup W = r^γ` — the
multiplier is capped at exactly the most-singular scaling factor.)

The hypothesis `0 ≤ C`, not stated in the paper, is redundant rather
than restrictive: on a probability space Cauchy–Schwarz
(`E[V]² ≤ E[V²]`) applied to the stated moments forces
`C(1−β)² ≥ 0`, so no probability measure realizes these moments with
`C < 0` — the excluded regime is empty.  (The paper's instantiations
have `C > 0`, or `C = 0` in the monofractal edge case.) -/
theorem lemma2_boundedness [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (hVm : Measurable V) (hV0 : 0 ≤ᵐ[μ] V)
    (r γk C β : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hint : ∀ m : ℕ, Integrable (fun ω => V ω ^ m) μ)
    (hmom : ∀ m : ℕ, ∫ ω, V ω ^ m ∂μ = r ^ (γk * m + C * (1 - β ^ m))) :
    essSup V μ = r ^ γk := by
  refine essSup_eq_of_geometric_moment_sandwich V hVm hV0 (r ^ γk)
    (r ^ C) 1 (Real.rpow_pos_of_pos hr.1 _) (Real.rpow_pos_of_pos hr.1 _)
    hint (fun m => ?_) (fun m => ?_)
  · rw [hmom m]
    exact (rpow_A1_moment_sandwich r γk C β hr hC hβ m).1
  · rw [hmom m]
    exact (rpow_A1_moment_sandwich r γk C β hr hC hβ m).2

end Freeburg

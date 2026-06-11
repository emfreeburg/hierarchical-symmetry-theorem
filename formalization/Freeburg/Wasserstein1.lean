/-
Freeburg formalization — Wasserstein1.lean
The dual-form Kantorovich–Rubinstein distance used by §5 of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632.
-/
import Mathlib

/-!
# The Wasserstein-1 distance in dual (Kantorovich–Rubinstein) form

Mathlib has no optimal-transport theory.  The paper, however, only ever
uses the two *easy* directions of Kantorovich duality:

* **lower bound by a test function** (Theorem 12): for any 1-Lipschitz
  `f`, `∫f dμ − ∫f dν ≤ W₁(μ,ν)`;
* **upper bound by a coupling** (Theorem 11): for any coupling `π` of
  `(μ,ν)`, `W₁(μ,ν) ≤ ∫|x−y| dπ`.

So we *define* `W₁` in dual form — the supremum of `∫f dμ − ∫f dν`
over 1-Lipschitz test functions anchored at `0` — on which the first
bound is definitional and the second is a one-line estimate.  The full
Kantorovich duality theorem is never needed by the paper and is not
proved here.  All quantitative lemmas carry a bounded-support
hypothesis (`∀ᵐ x, |x| ≤ M`), which every multiplier law in the paper
satisfies (Lemma 2(i): `ess sup W = r^γ`).

Main declarations:

* `Freeburg.lipTestVals`, `Freeburg.W1` — the dual-form distance.
* `Freeburg.le_W1` — the test-function lower bound (definitional).
* `Freeburg.le_W1_of_lipschitz` — the same without the anchoring, for
  probability measures.
* `Freeburg.W1_le_of_coupling` — the coupling upper bound.
* `Freeburg.W1_dirac` — `W₁(μ, δ_c) = ∫|x−c| dμ`, the form in which
  Theorem 10's display is a genuine Wasserstein statement.
* `Freeburg.W1_triangle`, `Freeburg.W1_comm`, `Freeburg.W1_nonneg`.

Everything in this file is sorry-free.
-/

open MeasureTheory

namespace Freeburg

/-! ## Definition -/

/-- The set of dual values `∫f dμ − ∫f dν` over 1-Lipschitz test
functions anchored at `0`.  Anchoring costs nothing (the dual value is
invariant under `f ↦ f − f 0` for probability measures) and makes every
admissible `f` integrable against any bounded-support finite measure. -/
def lipTestVals (μ ν : Measure ℝ) : Set ℝ :=
  {z | ∃ f : ℝ → ℝ, LipschitzWith 1 f ∧ f 0 = 0 ∧
    z = (∫ x, f x ∂μ) - ∫ x, f x ∂ν}

/-- The **Wasserstein-1 distance in dual (Kantorovich–Rubinstein)
form**: `W₁(μ,ν) = sup {∫f dμ − ∫f dν : f 1-Lipschitz, f 0 = 0}`. -/
noncomputable def W1 (μ ν : Measure ℝ) : ℝ :=
  sSup (lipTestVals μ ν)

/-! ## Elementary facts about anchored Lipschitz test functions -/

/-- An anchored 1-Lipschitz function is dominated by `|x|`. -/
theorem abs_le_abs_self_of_lipschitz {f : ℝ → ℝ}
    (hf : LipschitzWith 1 f) (hf0 : f 0 = 0) (x : ℝ) : |f x| ≤ |x| := by
  have h := hf.dist_le_mul x 0
  rw [Real.dist_eq, Real.dist_eq, hf0, sub_zero, sub_zero] at h
  simpa using h

/-- An anchored 1-Lipschitz function is integrable against any finite
measure of bounded support. -/
theorem integrable_of_lipschitz_anchored {μ : Measure ℝ} [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, |x| ≤ M)
    {f : ℝ → ℝ} (hf : LipschitzWith 1 f) (hf0 : f 0 = 0) :
    Integrable f μ := by
  refine Integrable.mono' (integrable_const M)
    hf.continuous.aestronglyMeasurable ?_
  filter_upwards [hμ] with x hx
  exact (abs_le_abs_self_of_lipschitz hf hf0 x).trans hx

theorem zero_mem_lipTestVals (μ ν : Measure ℝ) :
    (0 : ℝ) ∈ lipTestVals μ ν := by
  refine ⟨fun _ => 0, (LipschitzWith.const 0).weaken zero_le_one, rfl, ?_⟩
  simp

theorem bddAbove_lipTestVals {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M : ℝ}
    (hμ : ∀ᵐ x ∂μ, |x| ≤ M) (hν : ∀ᵐ x ∂ν, |x| ≤ M) :
    BddAbove (lipTestVals μ ν) := by
  refine ⟨M * μ.real Set.univ + M * ν.real Set.univ, ?_⟩
  rintro z ⟨f, hf, hf0, rfl⟩
  have hbμ : ‖∫ x, f x ∂μ‖ ≤ M * μ.real Set.univ := by
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [hμ] with x hx
    exact (abs_le_abs_self_of_lipschitz hf hf0 x).trans hx
  have hbν : ‖∫ x, f x ∂ν‖ ≤ M * ν.real Set.univ := by
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [hν] with x hx
    exact (abs_le_abs_self_of_lipschitz hf hf0 x).trans hx
  rw [Real.norm_eq_abs] at hbμ hbν
  have h1 := (le_abs_self (∫ x, f x ∂μ)).trans hbμ
  have h2 := neg_le_of_abs_le hbν
  linarith

/-! ## The two duality directions -/

/-- `W₁ ≥ 0` (witnessed by the zero test function). -/
theorem W1_nonneg {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, |x| ≤ M) (hν : ∀ᵐ x ∂ν, |x| ≤ M) :
    0 ≤ W1 μ ν :=
  le_csSup (bddAbove_lipTestVals hμ hν) (zero_mem_lipTestVals μ ν)

/-- **The test-function lower bound** (the easy direction of duality
used by Theorem 12): every anchored 1-Lipschitz `f` certifies
`∫f dμ − ∫f dν ≤ W₁(μ,ν)`.  Definitional. -/
theorem le_W1 {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, |x| ≤ M) (hν : ∀ᵐ x ∂ν, |x| ≤ M)
    {f : ℝ → ℝ} (hf : LipschitzWith 1 f) (hf0 : f 0 = 0) :
    (∫ x, f x ∂μ) - ∫ x, f x ∂ν ≤ W1 μ ν :=
  le_csSup (bddAbove_lipTestVals hμ hν) ⟨f, hf, hf0, rfl⟩

/-- The test-function lower bound without the anchoring: for
probability measures the dual value is invariant under `f ↦ f − f 0`. -/
theorem le_W1_of_lipschitz {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, |x| ≤ M) (hν : ∀ᵐ x ∂ν, |x| ≤ M)
    {f : ℝ → ℝ} (hf : LipschitzWith 1 f) :
    (∫ x, f x ∂μ) - ∫ x, f x ∂ν ≤ W1 μ ν := by
  have hglip : LipschitzWith 1 fun x => f x - f 0 := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    show dist (f x - f 0) (f y - f 0) ≤ 1 * dist x y
    rw [Real.dist_eq, sub_sub_sub_cancel_right, ← Real.dist_eq]
    exact hf.dist_le_mul x y
  have hg0 : (fun x => f x - f 0) 0 = 0 := by simp
  have hgintμ : Integrable (fun x => f x - f 0) μ :=
    integrable_of_lipschitz_anchored hμ hglip hg0
  have hgintν : Integrable (fun x => f x - f 0) ν :=
    integrable_of_lipschitz_anchored hν hglip hg0
  have heq : f = fun a => (f a - f 0) + f 0 := by funext a; ring
  have hfintμ : Integrable f μ := by
    rw [heq]; exact hgintμ.add (integrable_const (f 0))
  have hfintν : Integrable f ν := by
    rw [heq]; exact hgintν.add (integrable_const (f 0))
  have h := le_W1 hμ hν hglip hg0
  rw [integral_sub hfintμ (integrable_const _),
    integral_sub hfintν (integrable_const _)] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  linarith [h]

/-- **The coupling upper bound** (the easy direction of duality used by
Theorem 11): any measure `π` on `ℝ × ℝ` with marginals `μ` and `ν`
certifies `W₁(μ,ν) ≤ ∫ |x − y| dπ`. -/
theorem W1_le_of_coupling {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, |x| ≤ M) (hν : ∀ᵐ x ∂ν, |x| ≤ M)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (h1 : π.map Prod.fst = μ) (h2 : π.map Prod.snd = ν) :
    W1 μ ν ≤ ∫ p : ℝ × ℝ, |p.1 - p.2| ∂π := by
  refine csSup_le ⟨0, zero_mem_lipTestVals μ ν⟩ ?_
  rintro z ⟨f, hf, hf0, rfl⟩
  -- transfer the marginal integrals to the coupling space
  have hmeas1 : AEStronglyMeasurable f (π.map Prod.fst) := by
    rw [h1]; exact hf.continuous.aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable f (π.map Prod.snd) := by
    rw [h2]; exact hf.continuous.aestronglyMeasurable
  have hμint : Integrable f (π.map Prod.fst) := by
    rw [h1]; exact integrable_of_lipschitz_anchored hμ hf hf0
  have hνint : Integrable f (π.map Prod.snd) := by
    rw [h2]; exact integrable_of_lipschitz_anchored hν hf hf0
  have hint1 : Integrable (fun p : ℝ × ℝ => f p.1) π :=
    (integrable_map_measure hmeas1 measurable_fst.aemeasurable).mp hμint
  have hint2 : Integrable (fun p : ℝ × ℝ => f p.2) π :=
    (integrable_map_measure hmeas2 measurable_snd.aemeasurable).mp hνint
  have he1 : ∫ x, f x ∂μ = ∫ p : ℝ × ℝ, f p.1 ∂π := by
    rw [← h1, integral_map measurable_fst.aemeasurable hmeas1]
  have he2 : ∫ x, f x ∂ν = ∫ p : ℝ × ℝ, f p.2 ∂π := by
    rw [← h2, integral_map measurable_snd.aemeasurable hmeas2]
  rw [he1, he2, ← integral_sub hint1 hint2]
  -- the a.e. support bounds transfer to the coupling space
  have habs1 : ∀ᵐ p : ℝ × ℝ ∂π, |p.1| ≤ M := by
    have h : ∀ᵐ x ∂(π.map Prod.fst), |x| ≤ M := by rw [h1]; exact hμ
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_le measurable_id.abs measurable_const)).mp h
  have habs2 : ∀ᵐ p : ℝ × ℝ ∂π, |p.2| ≤ M := by
    have h : ∀ᵐ x ∂(π.map Prod.snd), |x| ≤ M := by rw [h2]; exact hν
    exact (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_le measurable_id.abs measurable_const)).mp h
  have hintabs : Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) π := by
    refine Integrable.mono' (integrable_const (M + M))
      (continuous_fst.sub continuous_snd).abs.aestronglyMeasurable ?_
    filter_upwards [habs1, habs2] with p hp1 hp2
    rw [Real.norm_eq_abs, abs_abs]
    calc |p.1 - p.2| = |p.1 + -p.2| := by rw [sub_eq_add_neg]
      _ ≤ |p.1| + |-p.2| := abs_add_le _ _
      _ = |p.1| + |p.2| := by rw [abs_neg]
      _ ≤ M + M := by linarith
  refine integral_mono (hint1.sub hint2) hintabs fun p => ?_
  have h := hf.dist_le_mul p.1 p.2
  rw [Real.dist_eq, Real.dist_eq] at h
  calc f p.1 - f p.2 ≤ |f p.1 - f p.2| := le_abs_self _
    _ ≤ |p.1 - p.2| := by simpa using h

/-! ## `W₁` against a Dirac mass -/

/-- The anchored 1-Lipschitz witness `x ↦ |x − c| − |c|`. -/
theorem lipschitzWith_absSub (c : ℝ) :
    LipschitzWith 1 fun x : ℝ => |x - c| - |c| := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  show dist (|x - c| - |c|) (|y - c| - |c|) ≤ 1 * dist x y
  rw [Real.dist_eq, Real.dist_eq, sub_sub_sub_cancel_right]
  have h := abs_abs_sub_abs_le_abs_sub (x - c) (y - c)
  rw [sub_sub_sub_cancel_right] at h
  simpa using h

/-- **`W₁` against a point mass is the first absolute moment**:
`W₁(μ, δ_c) = ∫|x − c| dμ`.  This is the statement that turns the
display of Theorem 10 into a genuine Wasserstein bound. -/
theorem W1_dirac {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, |x| ≤ M) (c : ℝ) :
    W1 μ (Measure.dirac c) = ∫ x, |x - c| ∂μ := by
  have hμ' : ∀ᵐ x ∂μ, |x| ≤ max M |c| :=
    hμ.mono fun x hx => hx.trans (le_max_left _ _)
  have hδ : ∀ᵐ x ∂(Measure.dirac c), |x| ≤ max M |c| := by
    rw [ae_dirac_iff (show MeasurableSet {x : ℝ | |x| ≤ max M |c|} from
      measurableSet_le continuous_abs.measurable measurable_const)]
    exact le_max_right _ _
  have hintabs : Integrable (fun x => |x - c|) μ := by
    refine Integrable.mono' (integrable_const (max M |c| + |c|))
      (continuous_id.sub continuous_const).abs.aestronglyMeasurable ?_
    filter_upwards [hμ'] with x hx
    rw [Real.norm_eq_abs, abs_abs]
    calc |x - c| = |x + -c| := by rw [sub_eq_add_neg]
      _ ≤ |x| + |-c| := abs_add_le _ _
      _ = |x| + |c| := by rw [abs_neg]
      _ ≤ max M |c| + |c| := by linarith
  refine le_antisymm ?_ ?_
  · -- every dual value is ≤ ∫|x−c|
    refine csSup_le ⟨0, zero_mem_lipTestVals _ _⟩ ?_
    rintro z ⟨f, hf, hf0, rfl⟩
    rw [integral_dirac]
    have hfint : Integrable f μ := integrable_of_lipschitz_anchored hμ' hf hf0
    have hsplit : (∫ x, f x ∂μ) - f c = ∫ x, f x - f c ∂μ := by
      rw [integral_sub hfint (integrable_const _), integral_const,
        probReal_univ, one_smul]
    rw [hsplit]
    refine integral_mono (hfint.sub (integrable_const _)) hintabs fun x => ?_
    have h := hf.dist_le_mul x c
    rw [Real.dist_eq, Real.dist_eq] at h
    calc f x - f c ≤ |f x - f c| := le_abs_self _
      _ ≤ |x - c| := by simpa using h
  · -- the explicit witness `|x − c| − |c|` attains it
    have hf0 : (fun x : ℝ => |x - c| - |c|) 0 = 0 := by simp
    have h := le_W1 hμ' hδ (lipschitzWith_absSub c) hf0
    rw [integral_dirac, integral_sub hintabs (integrable_const _),
      integral_const, probReal_univ, one_smul] at h
    have hc : |c - c| - |c| = -|c| := by simp
    rw [hc] at h
    linarith [h]

/-! ## Metric structure -/

/-- Triangle inequality for the dual-form `W₁` on a common bounded
support. -/
theorem W1_triangle {μ ν ρ : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, |x| ≤ M) (hν : ∀ᵐ x ∂ν, |x| ≤ M)
    (hρ : ∀ᵐ x ∂ρ, |x| ≤ M) :
    W1 μ ρ ≤ W1 μ ν + W1 ν ρ := by
  refine csSup_le ⟨0, zero_mem_lipTestVals _ _⟩ ?_
  rintro z ⟨f, hf, hf0, rfl⟩
  have h1 := le_W1 hμ hν hf hf0
  have h2 := le_W1 hν hρ hf hf0
  linarith

/-- The dual value set is symmetric in its arguments (replace `f` by
`−f`), so the dual-form `W₁` is too. -/
theorem lipTestVals_comm (μ ν : Measure ℝ) :
    lipTestVals ν μ = lipTestVals μ ν := by
  have key : ∀ ρ σ : Measure ℝ, lipTestVals σ ρ ⊆ lipTestVals ρ σ := by
    rintro ρ σ z ⟨f, hf, hf0, rfl⟩
    refine ⟨fun x => -f x, ?_, by simp [hf0], ?_⟩
    · refine LipschitzWith.of_dist_le_mul fun x y => ?_
      show dist (-f x) (-f y) ≤ 1 * dist x y
      rw [dist_neg_neg]
      exact hf.dist_le_mul x y
    · rw [integral_neg, integral_neg]
      ring
  exact le_antisymm (key μ ν) (key ν μ)

theorem W1_comm (μ ν : Measure ℝ) : W1 ν μ = W1 μ ν :=
  congrArg sSup (lipTestVals_comm μ ν)

end Freeburg

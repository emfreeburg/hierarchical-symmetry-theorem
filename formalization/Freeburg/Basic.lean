/-
Freeburg formalization — Basic.lean
Lemma 1 (Exponent Form) and Proposition 5 (Converse) of
"Hierarchical symmetry selects log-Poisson cascades: classification,
uniqueness, and stability", E. M. Freeburg, arXiv:2604.01632.
-/
import Mathlib

/-!
# The hierarchical symmetry axiom: exponent form and converse

This file formalizes the purely algebraic/analytic backbone of the paper:

* `Freeburg.SatisfiesA1` — Axiom A1 (eq. ($*$)) on the lattice `p = mk`,
  re-indexed by `m : ℕ` (so `δ m` stands for the paper's `δ_{mk}`).
* `Freeburg.delta_closed_form` — Lemma 1, step (2):
  `δ m − L = β^m (δ 0 − L)`.
* `Freeburg.tendsto_delta` — the remark following Axiom A1: the contraction
  forces `δ m → L` (so `L = δ_∞`).
* `Freeburg.zeta_closed_form` — Lemma 1, step (3): the partial sums
  `ζ m = ∑_{j<m} δ j` satisfy `ζ m = L m + (δ 0 − L)(1 − β^m)/(1 − β)`.
* `Freeburg.zeta_gamma_C` — Lemma 1, eq. ($**$), in the paper's
  `(γ, C)` parametrization: `ζ_{mk} = γ (mk) + C (1 − β^m)` with
  `γ = L/k`, `C = (δ 0 − L)/(1 − β)`.
* `Freeburg.exponent_form` — Lemma 1 packaged under the paper's
  hypothesis `β ∈ (0,1)`.
* `Freeburg.deltaLP_A1`, `Freeburg.logPoisson_satisfies_A1` —
  Proposition 5 (Converse): the log-Poisson exponent curve
  `ζ p = (a p + λ(e^{bp} − 1))/ln r` has step-`k` increments satisfying
  A1 with `β = e^{bk}` and `L = ak/ln r`.

Everything in this file is sorry-free.
-/

namespace Freeburg

/-- **Axiom A1 (Hierarchical Symmetry)**, eq. ($*$) of arXiv:2604.01632,
restricted to the lattice `p ∈ k ℕ` and re-indexed by `m : ℕ`:
`δ_{m+1} = (1−β) L + β δ_m`.  Here `δ m` plays the role of the paper's
incremental exponent `δ_{mk} = ζ_{(m+1)k} − ζ_{mk}`, and `L` is the free
constant of the axiom (the eventual limit `δ_∞`). -/
def SatisfiesA1 (δ : ℕ → ℝ) (β L : ℝ) : Prop :=
  ∀ m : ℕ, δ (m + 1) = (1 - β) * L + β * δ m

/-- **Lemma 1 (Exponent Form), step (2)** of arXiv:2604.01632:
the A1 recurrence is first-order linear with fixed point `L`, so iteration
gives `δ m − L = β^m (δ 0 − L)`.  Purely algebraic: no constraint on `β`
is needed for this step. -/
theorem delta_closed_form (δ : ℕ → ℝ) (β L : ℝ) (hrec : SatisfiesA1 δ β L) :
    ∀ m : ℕ, δ m - L = β ^ m * (δ 0 - L) := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
    have hstep : δ (n + 1) - L = β * (δ n - L) := by
      rw [hrec n]; ring
    rw [hstep, ih, pow_succ]
    ring

/-- The lattice-level biconditional (skeleton of Corollary 6 of
arXiv:2604.01632): a sequence satisfies the A1 recurrence iff it has
the geometric-deviation closed form `δ m = L + β^m (δ 0 − L)`.  (The
forward direction is Lemma 1; the converse is the computation behind
Proposition 5.) -/
theorem satisfiesA1_iff_closed_form (δ : ℕ → ℝ) (β L : ℝ) :
    SatisfiesA1 δ β L ↔ ∀ m : ℕ, δ m = L + β ^ m * (δ 0 - L) := by
  constructor
  · intro h m
    linarith [delta_closed_form δ β L h m]
  · intro h m
    rw [h (m + 1), h m, pow_succ]
    ring

/-- Remark after Axiom A1 in arXiv:2604.01632: since eq. ($*$) is a
contraction for `0 ≤ β < 1`, it forces `δ_{mk} → L` as `m → ∞`;
this identifies the free constant `L` of the axiom with `δ_∞`. -/
theorem tendsto_delta (δ : ℕ → ℝ) (β L : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hrec : SatisfiesA1 δ β L) :
    Filter.Tendsto δ Filter.atTop (nhds L) := by
  have h : ∀ m, L + β ^ m * (δ 0 - L) = δ m := fun m => by
    linarith [delta_closed_form δ β L hrec m]
  have hlim : Filter.Tendsto (fun m : ℕ => L + β ^ m * (δ 0 - L))
      Filter.atTop (nhds (L + 0 * (δ 0 - L))) :=
    tendsto_const_nhds.add
      (((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1)).mul_const _)
  simpa using hlim.congr h

/-- **Lemma 1 (Exponent Form), step (3)** of arXiv:2604.01632:
with `ζ 0 = 0`, summing the step-`k` increments by the geometric series
yields the closed form
`ζ m = ∑_{j<m} δ j = L·m + (δ 0 − L) · (1 − β^m)/(1 − β)`.
Purely algebraic; requires only `β ≠ 1`. -/
theorem zeta_closed_form (δ : ℕ → ℝ) (β L : ℝ) (hβ : β ≠ 1)
    (hrec : SatisfiesA1 δ β L) (m : ℕ) :
    ∑ j ∈ Finset.range m, δ j
      = L * m + (δ 0 - L) * ((1 - β ^ m) / (1 - β)) := by
  have h1β : (1 : ℝ) - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  have hβ1 : β - 1 ≠ 0 := sub_ne_zero.mpr hβ
  have hδ : ∀ j, δ j = L + β ^ j * (δ 0 - L) := fun j => by
    linarith [delta_closed_form δ β L hrec j]
  calc ∑ j ∈ Finset.range m, δ j
      = ∑ j ∈ Finset.range m, (L + β ^ j * (δ 0 - L)) :=
        Finset.sum_congr rfl fun j _ => hδ j
    _ = (Finset.range m).card • L
          + (∑ j ∈ Finset.range m, β ^ j) * (δ 0 - L) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul]
    _ = L * m + (δ 0 - L) * ((1 - β ^ m) / (1 - β)) := by
        rw [Finset.card_range, nsmul_eq_mul, geom_sum_eq hβ]
        field_simp
        ring

/-- **Lemma 1, eq. ($**$)** of arXiv:2604.01632 in the paper's
parametrization: identifying `γ = δ_∞/k = L/k` and
`C = (δ 0 − δ_∞)/(1 − β)`, the lattice scaling exponents are
`ζ_{mk} = γ·(mk) + C·(1 − β^m)`.  (`k` enters only through the
re-parametrization `γ = L/k`, hence may be any nonzero real here;
in the paper it is the integer hierarchy step.) -/
theorem zeta_gamma_C (δ : ℕ → ℝ) (β L k : ℝ) (hk : k ≠ 0) (hβ : β ≠ 1)
    (hrec : SatisfiesA1 δ β L) (m : ℕ) :
    ∑ j ∈ Finset.range m, δ j
      = (L / k) * (m * k) + ((δ 0 - L) / (1 - β)) * (1 - β ^ m) := by
  rw [zeta_closed_form δ β L hβ hrec m]
  field_simp

/-- **Lemma 1 (Exponent Form)** of arXiv:2604.01632, packaged under the
paper's standing hypothesis `β ∈ (0,1)`: the closed form for the
increments, the closed form for the partial sums, and the convergence
`δ_{mk} → L = δ_∞`. -/
theorem exponent_form (δ : ℕ → ℝ) (β L : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hrec : SatisfiesA1 δ β L) :
    (∀ m : ℕ, δ m - L = β ^ m * (δ 0 - L)) ∧
      (∀ m : ℕ, ∑ j ∈ Finset.range m, δ j
        = L * m + (δ 0 - L) * ((1 - β ^ m) / (1 - β))) ∧
      Filter.Tendsto δ Filter.atTop (nhds L) :=
  ⟨delta_closed_form δ β L hrec,
   zeta_closed_form δ β L (ne_of_lt hβ.2) hrec,
   tendsto_delta δ β L hβ.1.le hβ.2 hrec⟩

/-! ## The converse: log-Poisson exponents satisfy A1

Proposition 5 of arXiv:2604.01632.  If `log W = a + bN` with
`N ~ Poisson(λ)`, then `E[W^p] = exp(ap + λ(e^{bp} − 1))`, so the scaling
exponents are `ζ_p = (ap + λ(e^{bp} − 1))/ln r`.  We take this analytic
form of `ζ` as the definition and verify the A1 recurrence for its
step-`k` increments — a pure real computation. -/

/-- The log-Poisson scaling-exponent curve
`ζ p = (a p + λ (e^{b p} − 1)) / ln r` (proof of Proposition 5,
arXiv:2604.01632, from the Poisson moment generating function). -/
noncomputable def zetaLP (a b lam r : ℝ) (p : ℝ) : ℝ :=
  (a * p + lam * (Real.exp (b * p) - 1)) / Real.log r

/-- The step-`k` incremental exponents `δ_p = ζ_{p+k} − ζ_p` of the
log-Poisson curve. -/
noncomputable def deltaLP (a b lam r k : ℝ) (p : ℝ) : ℝ :=
  zetaLP a b lam r (p + k) - zetaLP a b lam r p

/-- Closed form of the log-Poisson increments:
`δ_p = ak/ln r + (λ(e^{bk} − 1)/ln r) · e^{bp}` (display in the proof of
Proposition 5, arXiv:2604.01632). -/
theorem deltaLP_eq (a b lam r k : ℝ) (hr : Real.log r ≠ 0) (p : ℝ) :
    deltaLP a b lam r k p
      = a * k / Real.log r
        + lam * (Real.exp (b * k) - 1) / Real.log r * Real.exp (b * p) := by
  unfold deltaLP zetaLP
  rw [show b * (p + k) = b * p + b * k by ring, Real.exp_add]
  field_simp
  ring

/-- **Proposition 5 (Converse), core computation** of arXiv:2604.01632:
the log-Poisson increments satisfy the A1 recurrence
`δ_{p+k} = (1 − β) L + β δ_p` with `β = e^{bk}` and `L = ak/ln r`,
for every real `p`.  Only `ln r ≠ 0` is needed for the algebra;
the hypotheses `b < 0 < k` of the paper serve solely to place
`β = e^{bk}` in `(0,1)` (see `logPoisson_satisfies_A1`). -/
theorem deltaLP_A1 (a b lam r k : ℝ) (hr : Real.log r ≠ 0) (p : ℝ) :
    deltaLP a b lam r k (p + k)
      = (1 - Real.exp (b * k)) * (a * k / Real.log r)
        + Real.exp (b * k) * deltaLP a b lam r k p := by
  rw [deltaLP_eq a b lam r k hr (p + k), deltaLP_eq a b lam r k hr p,
    show b * (p + k) = b * p + b * k by ring, Real.exp_add]
  field_simp
  ring

/-- **Proposition 5 (Converse)** of arXiv:2604.01632: if the cascade
multiplier is log-Poisson — `log W = a + bN`, `N ~ Poisson(λ)`, with
`b < 0`, scale ratio `r ∈ (0,1)` and hierarchy step `k > 0` — then the
incremental scaling exponents satisfy A1 with `β = e^{bk} ∈ (0,1)` and
`L = δ_∞ = ak/ln r`.  (The Poisson rate `λ` plays no role in the
recurrence itself — a fact the formalization makes explicit; `λ > 0`
matters only for nontrivial intermittency `C > 0`.) -/
theorem logPoisson_satisfies_A1 (a b lam r k : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hb : b < 0) (hk : 0 < k) :
    ∃ β ∈ Set.Ioo (0 : ℝ) 1, ∃ L : ℝ, ∀ p : ℝ,
      deltaLP a b lam r k (p + k)
        = (1 - β) * L + β * deltaLP a b lam r k p := by
  have hlog : Real.log r ≠ 0 := ne_of_lt (Real.log_neg hr.1 hr.2)
  refine ⟨Real.exp (b * k), ⟨Real.exp_pos _, ?_⟩,
    a * k / Real.log r, fun p => deltaLP_A1 a b lam r k hlog p⟩
  exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos hb hk)

/-- The lattice restriction of the converse: sampling the log-Poisson
increments at `p = mk` produces a sequence satisfying `SatisfiesA1`
(the form consumed by `exponent_form`).  This connects Proposition 5 to
Lemma 1 of arXiv:2604.01632. -/
theorem logPoisson_satisfies_A1_lattice (a b lam r k : ℝ)
    (hr : Real.log r ≠ 0) :
    SatisfiesA1 (fun m : ℕ => deltaLP a b lam r k (m * k))
      (Real.exp (b * k)) (a * k / Real.log r) := by
  intro m
  have h : ((m : ℝ) + 1) * k = m * k + k := by ring
  simpa [h] using deltaLP_A1 a b lam r k hr (m * k)

end Freeburg

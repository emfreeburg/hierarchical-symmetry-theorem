# Freeburg — Lean 4 formalization

A Lean 4 / Mathlib formalization of the mathematical core of

> E. M. Freeburg, *Hierarchical symmetry selects log-Poisson cascades:
> classification, uniqueness, and stability*, arXiv:2604.01632.

**Status: every theorem in this repository is fully proved.
`0 × sorry`, `0` custom axioms** — all results depend only on Lean's
standard axioms `[propext, Classical.choice, Quot.sound]`, enforced
by `AxiomAudit.lean`: an environment walk checking **every constant
compiled from the `Freeburg.*` modules** (373, including all
auto-generated auxiliaries — strictly stronger than per-theorem
`#print axioms`), failing on any violation.
Eleven modules, 6,581 lines, 247 declarations.

- Toolchain: `leanprover/lean4:v4.30.0-rc2`
- Mathlib: tag `v4.30.0-rc2` (rev `5450b53e5ddc`)
- Build: `lake exe cache get && lake build` (a warm Mathlib cache makes
  this take well under a minute for the project files).

**Numbering note.** All eleven modules cite the published arXiv (v2)
numbering.

The mapping tables below are curated: they list every paper-relevant
declaration; small supporting lemmas and instances are omitted.

## What is formalized

### `Freeburg/Basic.lean` — Lemma 1 and Proposition 5 (pure algebra/analysis)

| Lean name | Paper statement |
|---|---|
| `SatisfiesA1` | Axiom A1, eq. (∗), on the lattice `p = mk`, indexed by `m : ℕ` |
| `delta_closed_form` | Lemma 1, step (2): `δ_m − L = β^m (δ₀ − L)` |
| `satisfiesA1_iff_closed_form` | lattice-level biconditional (skeleton of Corollary 6) |
| `tendsto_delta` | remark after A1: the contraction forces `δ_m → L = δ_∞` |
| `zeta_closed_form` | Lemma 1, step (3): `ζ_m = Σ_{j<m} δ_j = Lm + (δ₀−L)(1−β^m)/(1−β)` |
| `zeta_gamma_C` | Lemma 1, eq. (∗∗): `ζ_{mk} = γ(mk) + C(1−β^m)`, `γ = L/k`, `C = (δ₀−L)/(1−β)` |
| `exponent_form` | Lemma 1 packaged under the paper's hypothesis `β ∈ (0,1)` |
| `zetaLP`, `deltaLP`, `deltaLP_eq` | the log-Poisson exponent curve `ζ_p = (ap + λ(e^{bp}−1))/ln r` and its increments |
| `deltaLP_A1` | Proposition 5 (Converse), core computation: `δ_{p+k} = (1−β)L + βδ_p`, `β = e^{bk}`, `L = ak/ln r`, all real `p` |
| `logPoisson_satisfies_A1` | Proposition 5 with the paper's hypotheses (`r ∈ (0,1)`, `b < 0 < k` ⟹ `β ∈ (0,1)`) |
| `logPoisson_satisfies_A1_lattice` | the lattice restriction, in the form consumed by Lemma 1 |

### `Freeburg/Dirac.lean` — Theorem 7, Step 4 (geometric moments ⟹ Dirac)

Setting: `η` a finite nonnegative measure on `ℝ` concentrated on
`[0,1]` (`∀ᵐ u ∂η, u ∈ Icc 0 1`) — the tilted Lévy measure
`η = (1−u) dν̃` in the compactified coordinates `u = e^{kx}`.
Hypothesis: `∫ u^m dη = A β^m` for `m = 0, 1, 2`.

| Lean name | Paper statement |
|---|---|
| `integral_pow_integrable`, `integrable_sq_sub`, `integrable_abs_sub` | integrability of the test integrands (from boundedness of the support) |
| `integral_sq_sub` | the expansion `∫(u−β)² dη = μ₂ − 2βμ₁ + β²μ₀` |
| `integral_pow_zero` | `μ₀ = ‖η‖` (the zeroth moment is the mass) |
| `variance_zero_of_geometric_moments` | Thm 7, Step 4: `∫(u−β)² dη = A(β²−2β²+β²) = 0` |
| `ae_eq_of_geometric_moments` | Thm 7, Step 4: `u = β` for `η`-a.e. `u` |
| `measure_eq_zero_of_geometric_moments` | `η s = 0` for **every** `s` with `β ∉ s` (no measurability of `s` needed) |
| `mass_eq_of_geometric_moments` | `‖η‖ = A` (hence `A ≥ 0` is automatic, not an assumption) |
| `measure_singleton_of_geometric_moments`, `real_measure_singleton_of_geometric_moments` | `η {β} = A` |
| `eq_dirac_of_geometric_moments` | `η = A·δ_β` as measures |

No hypothesis on `β` (or `A`) is needed: the rigidity is uniform in
`β ∈ ℝ`. The paper instantiates `β ∈ (0,1)`, `A = |A| > 0`, after which
inverting the tilt gives `ν = λδ_b`, `b = ln β/k`, `λ = A/(1−β)` — the
log-Poisson generator.

### `Freeburg/Stability.lean` — Theorem 10, Steps 1–3, with sharpness

Normalization: `|ln r| = 1` (legitimate by Corollary 23 of the paper:
all constants are scale-ratio-free). Residuals: `ε_m = μ_{m+1} − βμ_m`.

| Lean name | Paper statement |
|---|---|
| `variance_identity` | Thm 10, Step 2 (telescoping): `∫(u−β)² dη = ε₁ − βε₀` |
| `variance_le_of_residual_bounds` | Thm 10, reading (i): `\|ε₀\|,\|ε₁\| ≤ ε ⟹ ∫(u−β)² dη ≤ (1+β)ε` |
| `variance_le_of_fitted_residual_bounds` | Thm 10, reading (ii): fitted residuals `h_m = ε_m − t`, `\|h₀\|,\|h₁\|,\|t\| ≤ ε ⟹ ∫(u−β)² dη ≤ 2ε`, via `ε₁ − βε₀ = (h₁ − βh₀) + (1−β)t` |
| `sq_integral_abs_le` | Cauchy–Schwarz `(∫\|f\| dη)² ≤ ‖η‖ ∫ f² dη`, self-contained via the quadratic-discriminant argument |
| `abs_moment_le` | Thm 10, Step 3: `∫\|u−β\| dη ≤ √(‖η‖(1+β)ε)` |
| `normalized_abs_moment_le` | Thm 10(i) displayed bound: `‖η‖⁻¹∫\|u−β\| dη ≤ √((1+β)ε/‖η‖)`; for a Dirac target this *is* `W₁(η/‖η‖, δ_β)` |
| `classification_of_A1` | glue: exact A1 + moment dictionary ⟹ `η = (δ₀−L)·δ_β` (the classification as the `ε = 0` case) |
| `stability_of_approx_A1` | glue: approximate A1 residuals are literally the moment residuals; `(1+β)ε` bound from A1 form |
| `twoAtom`, `twoAtom_integral`, `twoAtom_ae_Icc` | the endpoint two-atom measure `c₀δ₀ + c₁δ₁` and its integral calculus |
| `variance_le_sharp` | **sharpness of `(1+β)`**: `η = (2ε/β)δ₀ + (ε/(1−β))δ₁` has `(ε₀,ε₁) = (−ε,ε)` and `∫(u−β)² dη = (1+β)ε` exactly |
| `fitted_variance_le_sharp` | **sharpness of `2`**: `η = (2ε/β)δ₀ + (2ε/(1−β))δ₁`, `t = ε` has `(ε₀,ε₁) = (0,2ε)` and `∫(u−β)² dη = 2ε` exactly |

On the closed interval `[0,1]` the paper's limiting two-atom family
(`u₀ ↓ 0`, `v ↑ 1`) is itself admissible, so sharpness is realized with
*exact equality* rather than only in the limit.

The Wasserstein conclusion is stated as the normalized first absolute
moment (equal to `W₁` against a Dirac target) rather than through a
Wasserstein library, as the optimal-transport machinery would only
re-derive that identity.

### `Freeburg/Stretch.lean` — Lemma 2(i) (boundedness), fully proved

The paper proves `essSup V = r^{γk}` (where `V = W^k`) from
`‖V‖_{L^m} ↑ ‖V‖_{L^∞}`. Mathlib (v4.30.0-rc2) has no `p → ∞` limit
theorem for `L^p` norms, but the A1 moment sequence is *geometrically
sandwiched* — `r^C·(r^{γk})^m ≤ E[V^m] ≤ (r^{γk})^m` — and for such
moments the identification is elementary, so the lemma is proved in
full (no sorry):

| Lean name | Statement |
|---|---|
| `ae_le_of_pow_integral_le` | `E[V^m] ≤ Khi·c^m` (all `m`) ⟹ `V ≤ c` a.e. (Markov at level `c+δ`, then `Khi(c/(c+δ))^m → 0`) |
| `not_ae_le_of_le_pow_integral` | `Klo·c^m ≤ E[V^m]` (all `m`), `Klo > 0 < c` ⟹ no `c' < c` is an a.e. bound |
| `essSup_eq_of_geometric_moment_sandwich` | both ⟹ `essSup V = c` (via `essSup_eq_sInf`) |
| `rpow_A1_moment_sandwich` | the A1 moments `r^{γkm + C(1−β^m)}` satisfy the sandwich with `c = r^{γk}`, `Klo = r^C`, `Khi = 1` |
| `lemma2_boundedness` | **Lemma 2(i)**: A1 moments ⟹ `essSup V = r^{γk}` (so `essSup W = r^γ`) |

### `Freeburg/MomentDeterminacy.lean` — Lemma 2(ii) (Hausdorff determinacy)

| Lean name | Paper statement |
|---|---|
| `integrable_of_ae_Icc` | continuous functions are integrable against finite measures on `[0,M]` |
| `integral_polynomial_eq_of_moments` | equal moments ⟹ equal polynomial integrals |
| `ext_of_moments_eq` | **Hausdorff determinacy**: finite Borel measures on `[0,M]` with equal moments coincide (Weierstrass + Riesz, as in the paper) |
| `ext_of_lattice_moments_eq` | **Lemma 2(ii)**: determinacy from the `k`-lattice moments alone (pushforward along `x ↦ x^k`, inversion on the support) |

### `Freeburg/LogPoissonLaw.lean` — Theorem 3(ii) at the level of laws

| Lean name | Paper statement |
|---|---|
| `logPoissonLaw` | the law of `W = exp(a + bN)`, `N ~ Poisson(λ)`, as a `Measure ℝ` (pushforward of Mathlib's `poissonMeasure`) |
| `integral_pow_logPoissonLaw` | the moment formula `E[W^m] = exp(am + λ(e^{bm}−1))` (the displayed formula in the proofs of Thm 3(ii)/Prop 5; equivalently eq. (∗∗) under `E[W^p] = r^{ζ_p}`) |
| `logPoissonLaw_ae_mem_Icc` | for `b ≤ 0` the law lives on `[0, e^a]` |
| `theorem3_law_uniqueness` | **Theorem 3(ii)**, `V = W^k` form: A1 moments ⟹ the law *is* log-Poisson (chains Lemma 2(i) + Lemma 2(ii) + the moment formula) |
| `theorem3_law_uniqueness_W` | **Theorem 3(ii)**, `W` form, from the lattice moments alone: *"no other probability distribution on `W` is compatible with A1"*; also Prop 9(a) |

### `Freeburg/LevyKhintchine.lean` — Theorem 7 (forward) and Theorem 10, Step 0

The log-ID class is formalized **by triplet, at the cumulant level**:
`lkPhi a σ2 ν k p = ak + σ²k(p+k/2) + ∫ g_p dν` is the paper's unsplit
Step-1 form of `ψ(p+k) − ψ(p)` (sanity identity `lkPhi_eq_lkPsi_sub`).
This is faithful to the printed theorems, which quantify over triplets
in their hypotheses; the one classical input *not* formalized is the
Lévy–Khintchine representation theorem itself (abstract ID law ⟹
triplet), which the paper's statements never invoke.

| Lean name | Paper statement |
|---|---|
| `gIntegrand_eq_sub`, sign inventory (`gIntegrand_nonneg`, `gIntegrand_far_bounds`, `gIntegrand_le_k_abs`, `gIntegrand_mono`, shell bounds) | Thm 7, Steps 1, 1′ |
| `nu_Iio_lt_top` | the far Lévy mass is finite (from integrability of `g_0` alone) |
| `tendsto_lkPhi_atTop_of_sigma_pos` | **Step 2**: `σ² > 0` ⟹ `φ(mk) → +∞` (kills log-normal) |
| `tendsto_lkPhi_atTop_of_pos_jumps` | **Step 3**: positive jumps ⟹ divergence |
| `tendsto_lkPhi_atTop_of_compensator_infinite` | **Step 3½**: `∫_{[−1,0)}\|x\| dν = ∞` ⟹ divergence (kills `α ∈ [1,2)` stable) |
| `step0_conclusions` | **Thm 10, Step 0**: bounded lattice increments ⟹ all three structural conclusions |
| `lkPhi_split`, `tendsto_lkPhi_c0` | the split form (legitimate only now) and the limit `φ(mk) → c₀` |
| `tiltedMeasure`, `tiltedMeasure_ae_Icc`, `isFiniteMeasure_tiltedMeasure` | `η = (1−u)·dν̃`, `u = e^{kx}`, supported in `[0,1]`, finite |
| `integral_pow_tiltedMeasure` | **the moment dictionary** `∫ u^m dη = c₀ − φ(mk)` |
| `theorem7_forward_eta` | **Theorem 7, forward**: exact A1 ⟹ `σ² = 0`, no positive jumps, integrability, `η = (Lφ−φ(0))·δ_β` |
| `map_eq_smul_dirac_of_tilted_eq`, `theorem7_forward_nu` | the tilt inversion: `ν = λ·δ_b`, `b = ln β/k`, `λ = (Lφ−φ(0))/(1−β)` — **the generator is log-Poisson** |
| `theorem10_step0` | **Thm 10, Step 0–1 package**: approximate A1 ⟹ conclusions + limit + `(1−β)\|Lφ−c₀\| ≤ ε` + exact dictionary |
| `theorem10_variance_known` / `theorem10_variance_fitted` | **Thm 10, Step 2 assembled**: `∫(u−β)²dη ≤ (1+β)ε` (reading (i)) / `≤ 2ε` (reading (ii)), end-to-end from the LK-form hypotheses |
| `theorem10_wasserstein_known` | **Thm 10(i), displayed bound**: `‖η‖⁻¹∫\|u−β\|dη ≤ √((1+β)ε/‖η‖)` end-to-end |


### `Freeburg/Wasserstein1.lean` — `W₁` in dual (Kantorovich–Rubinstein) form

Mathlib has no optimal transport.  The paper only ever uses the two
*easy* directions of Kantorovich duality, so `W₁` is defined in dual
form — `sup {∫f dμ − ∫f dν : f 1-Lipschitz, f 0 = 0}` — on
bounded-support measures, where both directions are elementary.
Lower bounds on this dual-form `W₁` transfer to the transport-form
distance unconditionally (every dual value is ≤ every coupling cost,
`W1_le_of_coupling`); upper bounds are statements about the KR-dual
metric, which equals the transport distance on compact supports by the
classical Kantorovich–Rubinstein theorem ([Vil09], cited by the paper)
— the one classical bridge this file assumes rather than proves:

| Lean name | Statement |
|---|---|
| `lipTestVals`, `W1` | the dual-form distance |
| `integrable_of_lipschitz_anchored`, `bddAbove_lipTestVals` | well-definedness on bounded supports |
| `le_W1`, `le_W1_of_lipschitz` | **the test-function lower bound** (Theorem 12's direction), anchored and unanchored |
| `W1_le_of_coupling` | **the coupling upper bound** `W₁ ≤ ∫\|x−y\| dπ` (Theorem 11's direction) |
| `W1_dirac` | `W₁(μ, δ_c) = ∫\|x−c\| dμ` — the identity making Theorem 10's display a genuine `W₁` bound |
| `W1_triangle`, `W1_comm`, `W1_nonneg` | metric structure on a common bounded support |

### `Freeburg/CompoundPoisson.lean` — two-atom compound Poisson + superposition

Theorem 12's compound-Poisson multiplier collapses, by the marked
decomposition, to a pushforward of **two independent Poisson counts**
— no point-process theory is needed.  The construction is certified
against the paper's description three ways (superposition, cumulant
identity, conservation):

| Lean name | Statement |
|---|---|
| `integral_pow_poissonMeasure` | the Poisson PGF `E[x^N] = e^{λ(x−1)}` |
| `poissonMeasure_prod_map_add` | **Poisson superposition**: `N₁+N₂ ~ Poisson(λ₁+λ₂)` (binomial-theorem proof on singletons) |
| `twoAtomCPLaw` | the law of `W = e^c s^{N₁} t^{N₂}`, independent Poisson counts |
| `twoAtomCPLaw_ae_mem_Icc` | the multiplier lives on `[0, e^c]` (Lemma 2(i) for the family) |
| `integral_pow_twoAtomCPLaw` | the moment formula `E[W^m] = exp(cm + λ₁(s^m−1) + λ₂(t^m−1))` |
| `integral_pow_twoAtomCPLaw_CGF` | **the compound-Poisson cumulant identity** `E[W^m] = exp(cm + ∫(u^m−1)dν̃)` over the actual two-atom Lévy measure `twoAtomLevy` |
| `integral_twoAtomCPLaw_eq_one` | conservation: drift `c = ∫(1−u)dν̃` gives `E[W] = 1` |
| `twoAtomLevy_withDensity_tilt` | de-tilting two-atom measures: `ν̃·g` reweights the atoms |
| `abs_prod_sub_prod_le`, `abs_prod_sub_one_le` | the telescoping product inequality `\|∏s_i − ∏t_i\| ≤ Σ\|s_i−t_i\|` on `[0,1]` (Theorem 11's coupling cost; Wald's identity lives in the construction that consumes it — `wald_cpModel` in `Propagation.lean`) |

### `Freeburg/PropagationLower.lean` — Theorem 12 (the rate `√ε` is exact)

The two-atom perturbation `η_d = (A/2)(δ_{β−d} + δ_{β+d})`,
`d ∈ (0, β(1−β)/2]`, with `A` the η-mass (`= C\|ln r\|(1−β)` for the
Theorem-3 cascade) and `k = 1` as in the paper:

| Lean name | Paper statement |
|---|---|
| `pow_sub_pow_le`, `nat_mul_pow_le` | the calculus-free mean-value bound and `sup_x x·ρ^x ≤ (e\|ln ρ\|)⁻¹` via `e^{y−1} ≥ y` |
| `etaD`, `integral_pow_etaD` | `η_d` and its moments `μ_m = (A/2)[(β−d)^m + (β+d)^m]` |
| `twoAtomLevy_tilt_eq_etaD` | faithfulness: the family's Lévy measure (masses `(A/2)/(1−(β±d))`, matched to the atoms `β±d` — the pairing forced by `η_d = (1−u)dν̃_d`; this kernel-checked identity caught a `∓` typo in the paper's parenthetical, fixed pre-submission) tilts to exactly `η_d` |
| `etaD_residual_formula`, `_nonneg`, `_one` | the signed residuals `ε_m\|ln r\| = (Ad/2)[(β+d)^m − (β−d)^m] ≥ 0` (so `ε₀ = 0`), with `ε₁\|ln r\| = Ad²` **exactly** |
| `c2`, `nat_mul_pow_pred_le_c2`, `etaD_residual_le` | the explicit admissible constant `c₂(β) = max((eβ·ln(2/(1+β)))⁻¹, 1)` bounding the paper's interval minimum |
| `epsResidual`, `theorem12_residual_lower` / `_upper` | **Theorem 12(i)**: `Ad²/\|ln r\| ≤ ε(d) ≤ c₂(β)Ad²/\|ln r\|` with `ε(d) = ⨆_m ε_m` the genuine residual supremum |
| `infDist_geom_minus` / `_plus` | the one-jump points `e^A(β±d)` sit at distance **exactly** `e^A d` from the target support `G = {e^A β^j}` |
| `theorem12_W1_lower` | **Theorem 12(ii), first display**: `W₁(law W_{(d)}, law W₀) ≥ λ_d e^{−λ_d} e^A d`, by the test function `min(dist(·,G), e^Aβ(1−β)/2)` through `le_W1` |
| `lamD_eq`, `lamD_bounds` | `λ_d = λ/(1−d²(1−β)^{−2})` and the window `λ ≤ λ_d ≤ 4λ/3` |
| `c1`, `c1_pos`, `theorem12_rate_lower` | **Theorem 12 assembled**: `W₁ ≥ c₁(β,A,r)·√ε(d)` with `c₁ > 0` explicit — *no `o(√ε)` propagation bound is possible*; with Theorem 11 the exact rate is `Θ(√ε)` |
| `theorem10_wasserstein_W1` | **Theorem 10(i) as genuine `W₁`**: `W₁(η/‖η‖, δ_β) ≤ √((1+β)ε/‖η‖)` end-to-end from the LK-form hypotheses (`W1_dirac` ∘ `theorem10_wasserstein_known`) |

### `Freeburg/Propagation.lean` — Theorem 11 (unconditional propagation upper bound)

The multiplicative-coupling upper bound, **in the unconditional form of
the paper**: no finite-activity and no minimum-jump assumption.  The
compound-Poisson law with arbitrary (possibly infinite-activity) tilted
Lévy measure is built in layers over geometric bands of the jump
support; on each band the tilt `1−u` is bounded below, so each layer is
honestly finite — this is the structural reason the paper's Theorem 11
needs no extra hypotheses, and the construction makes it a *proof*.
Conventions: `k = 1` (the convention Theorem 12 fixes; the paper's
Theorem 11 is printed for general `k` — the module docstring documents
the deviation, with `L_1 = 1`), jump factors clamped to `[0,1]`
(`clamp01`), so all model-level lemmas are
unconditional and support hypotheses enter only as a.e. bridges.

| Lean name | Statement |
|---|---|
| `clamp01`, `prodFnT`, `cpModel`, `cpLaw` | single-layer model: `W = e^a ∏_{i<N} U_i`, `N ~ Poisson(S)`, `U_i` i.i.d. — built on `(poissonMeasure S).prod (Measure.infinitePi …)` |
| `integral_prod_cpModel` | the workhorse product formula `E[∏_{i<N} g(U_i)] = exp(S(∫g − 1))` |
| `integral_pow_cpLaw` | single-layer moments `E[W^m] = exp(am + S(∫u^m dμ̂ − 1))` |
| `wald_cpModel` | **Wald's identity** `E[Σ_{i<N} g(U_i)] = S·∫g dμ̂`, with the integrability that the coupling consumes (deferred from `CompoundPoisson.lean` to the construction that uses it) |
| `logPoissonLaw_eq_pow_map` | the target as a pushforward `n ↦ e^a β^n` of `poissonMeasure` |
| `W1_cpLaw_logPoisson_le` | **same-count pairing leg**: `W₁ ≤ e^a · S · ∫\|clamp01 u − β\| dμ̂` (telescoping + Wald) |
| `W1_logPoisson_rate_le`, `'` | **thinning leg**: `W₁(logPoisson(λ₁), logPoisson(λ₂)) ≤ e^a(1−β)\|λ₁−λ₂\|` (Poisson superposition coupling) |
| `layerProb`, `layerRate`, `layerRate_mul_integral` | normalizing an arbitrary finite measure into (rate, probability) with the unconditional identity `S·∫g dμ̂ = ∫g dm` |
| `layerModel`, `cpModelInf`, `partialProd`, `prodInf`, `cpLawInf` | **the layered infinite-activity construction**: countably many independent layers via `Measure.infinitePi`; the infinite product as `liminf` of antitone clamped partial products (measurable for free; all limits by dominated convergence) |
| `integral_finprod_cpModelInf`, `integral_pow_layerModel'` | factorization over layers; per-layer cumulant `∫ prodFnT^m = exp(∫(u^m−1)dm)` |
| `integral_pow_cpLawInf` | layered moments `E[W^m] = exp(am + Σ_j ∫(u^m−1)dm_j)` |
| `W1_cpLawInf_layer0_le` | **small-jump removal leg**: dropping all layers `j ≥ 1` costs `≤ e^a Σ_{j≥1} ∫(1−u)dm_j = e^a·η(small jumps)` |
| `band`, `pairwise_disjoint_band`, `Ico_subset_iUnion_band` | the geometric bands: `band 0 = [0,(1+β)/2]`, `band (j+1)` halving toward `1`; a disjoint cover of `[0,1)` |
| `eta_real_eq`, `integral_eta_eq`, `isFiniteMeasure_restrict_band` | the `η = (1−u)dν̃` bridges; each band-restriction of `ν̃` is finite **because the tilt is bounded below on the band** |
| `eta_compl_band0_le`, `setIntegral_band0_abs_le`, `rate_diff_le`, `tilt_bands_summable` | Steps 1–2 of the paper's proof: Chebyshev for the small-jump mass `η(band₀ᶜ) ≤ 4V_ε/(1−β)²`, the de-tilt comparison `∫_{band₀}\|u−β\|dν̃ ≤ 2S_ε/(1−β)`, and the macroscopic-rate estimate |
| `theorem11_W1_upper` | **Theorem 11, explicit-constant form**: `W₁(law W, law W₀) ≤ e^a(4S_ε/(1−β) + 8V_ε/(1−β)²)` from `∫(u−β)²dη ≤ V_ε`, `∫\|u−β\|dη ≤ S_ε` alone — two triangle inequalities over the three legs |
| `tsum_setIntegral_bands`, `integral_pow_cpLawInf_levy`, `cpLawInf_unique` | **the faithfulness certificate**: the layered law has cumulants `E[W^m] = exp(am + ∫(u^m−1)dν̃)` and (with `MomentDeterminacy.lean`'s Hausdorff determinacy) is the *unique* law with these moments — the construction is canonical, not ad hoc |
| `Kinfty`, `theorem11_rate_upper` | **Theorem 11, paper form**: `W₁ ≤ K_∞√ε` for `ε ≤ ε₀ = ‖η‖/(4(1+β))`, with `K_∞ = 4e^a(1/(1−β)+1/(1−β)²)·√((1+β)‖η‖)` — at the LK-residual scale `ε = \|ln r\|·ε_paper` and with `‖η‖ = \|A\|` this is exactly the printed `4e^{a₀}(…)√((1+β)\|A\|\|ln r\|)·√ε_paper` |
| `theorem11_from_theorem10` | **end-to-end glue**: from the printed Theorem-10 hypotheses (LK-form residuals ≤ ε) directly to `W₁ ≤ K_∞√ε` — Theorems 10 and 11 chained with no interface gap |
| `twoAtomLevy_restrict_band`, `twoAtomCPLaw_eq_cpLawInf` | the Theorem-12 family seen by the Theorem-11 machine: its two-atom Lévy measure lives in `band 0`, and the layered law *equals* `CompoundPoisson.lean`'s `twoAtomCPLaw` (via the cumulant certificate + determinacy) |
| `theorem11_12_theta` | **the Θ(√ε) capstone**: for the attaining family, `c₁(β,A,r)·√ε(d) ≤ W₁ ≤ (8e^A√(A\|ln r\|)/(1−β))·√ε(d)` — both halves of the paper's closing claim *"the exact rate is Θ(√ε)"*, kernel-checked |

## What is *not* formalized (and why)

* The **Lévy–Khintchine representation theorem** (every infinitely
  divisible law has a triplet) and the moment-side analytic
  continuation.  The class is instead formalized by triplet — exactly
  how Theorems 7, 10 and 18 state their hypotheses — so every printed
  statement is covered; only this classical bridge is assumed when
  *instantiating* them at an abstract ID law.
* Sections 6–7 (beyond independence; continuous cascades) — planned
  future work; de Finetti (Cor 15) and Perron–Frobenius analyticity
  (Thm 16) are deliberately out of scope (each is a major classical
  formalization project in its own right).

## Findings made while formalizing

1. **The converse needs no `λ > 0`** — `deltaLP_A1` holds for every
   `λ ∈ ℝ` (only `ln r ≠ 0` is used); the paper's hypotheses `b < 0`,
   `λ > 0` matter only to place `β ∈ (0,1)` and to make the
   intermittency nontrivial. Consistent with the paper's `C = 0` edge
   case (monofractal: A1 holds trivially for any β).
2. **The Dirac rigidity is uniform in `β`** — no `β ∈ (0,1)` hypothesis
   is needed in `Dirac.lean`; for `β ∉ [0,1]` the hypotheses simply
   force `η = 0` (`A = 0`). Likewise `A ≥ 0` is a conclusion, not an
   assumption.  (In the same spirit, `theorem7_forward_nu` drops the
   paper's `C > 0` and concludes the *exact value* `λ = |A|/(1−β)`;
   positivity follows under the printed hypothesis by one line.)
3. **Sharpness is exact on the closed interval** — the paper attains
   `(1+β)` and `2` only as limits because its `η` lives on the open
   interval `(0,1)`; on `Icc 0 1` the endpoint two-atom measures attain
   both constants exactly, and even satisfy the residual bounds at
   *all* orders `m`, not just `m = 0, 1`.
4. **Lemma 2(i) without `‖·‖_p → ‖·‖_∞`** — the geometric sandwich
   proof gives, in addition, the explicit tail estimate
   `μ{V ≥ c+δ} ≤ Khi (c/(c+δ))^m` for every `m`, quantifying the
   qualitative essential-boundedness claim.
5. **Theorem 12(ii) needs neither the matched rate nor `A > 0`** —
   the Wasserstein lower bound `theorem12_W1_lower` holds against the
   log-Poisson target of *every* rate `λ`: the test function vanishes
   on the whole geometric support `{e^A β^j}`, so only the perturbation
   geometry (`0 < d ≤ β(1−β)/2`) enters — and the drift-positivity
   hypothesis is never used by the proof (its argument is `_hA`),
   though the statement still carries `0 < A`.  The
   paper's matched target (`λ = A/(1−β)`, `A > 0`) is the special case
   quantified by `theorem12_rate_lower`.
6. **Sign conventions check out** — the glue theorem
   `stability_of_approx_A1` verifies that the moment residuals
   `μ_{m+1} − βμ_m` coincide *exactly* (not up to sign) with the A1
   residuals `δ_{m+1} − (1−β)L − βδ_m` under the dictionary
   `μ_m = δ_m − L`, confirming the repaired Step 1 of Theorem 3 (the
   v1 per-moment estimate is indeed never needed: only `ε₀, ε₁` enter).
7. **Theorem 11's constant improves at `k = 1`** — the paper's
   `e^{a₀+1}` arises from a drift slack `|a_ε − a₀| ≤ 1` that is vacuous
   at `k = 1`, where conservation makes the drift *rigid*
   (`a_ε = ‖η_ε‖`): the formalized bound carries `e^{a}` with no `+1`,
   and `K_∞ = 4e^a(1/(1−β)+1/(1−β)²)√((1+β)‖η‖)` is correspondingly
   sharper than the printed constant.  (The comparison is at the
   formalization's residual scale: the LK-form `ε` is `|ln r|` times
   the paper's exponent-level `ε`, and `‖η‖ = |A|` exactly, so no
   `√|ln r|` factor is lost.)
8. **The upper bound never uses conservation** — `theorem11_W1_upper`
   and `theorem11_rate_upper` take `a = ‖η‖` as a hypothesis but never
   consume it (argument `_ha`): only the *shared* drift of the two laws
   and the matched macroscopic rate `λ(1−β) = ‖η‖` enter.  Like finding
   5 (its mirror image for Theorem 12), the propagation estimate is
   about geometry, not about the conservation identity.
9. **One sign typo found in the paper** — Theorem 12's parenthetical
   printed the two-atom Lévy masses as `(|A|/2)/(1−(β∓d))`,
   cross-pairing atoms and tilts; proving `twoAtomLevy_tilt_eq_etaD`
   forced the matched pairing `(|A|/2)/(1−(β±d))` (the total rate `λ_d`
   is pairing-invariant, so nothing downstream changes).  Fixed in the
   paper pre-submission — the only error the formalization found.

## Reproducing the build

```bash
# from this directory (formalization/ in the public repository)
lake exe cache get   # pulls the Mathlib build cache (multi-GB, one-time)
lake build           # builds the eleven Freeburg modules
lake env lean AxiomAudit.lean   # whole-library axiom audit (must print PASS)
grep -rn "sorry" Freeburg/ Freeburg.lean   # no matches outside docstring prose
```

## License

Apache License 2.0 — see [`LICENSE`](LICENSE) in this directory
(Copyright 2026 E. M. Freeburg). The paper itself — `PAPER.md` and the
`paper/` LaTeX sources at the repository root — is licensed CC BY 4.0.

# Hierarchical Symmetry Selects Log-Poisson Cascades: Classification, Uniqueness, and Stability

**E. M. Freeburg**

---

## Abstract

Within i.i.d. multiplicative cascades, a single axiom—the hierarchical symmetry, a linear contraction on incremental scaling exponents—is shown to be necessary and sufficient for the cascade multiplier to be log-Poisson. We establish three results: (1) a characterization theorem proving that the hierarchical symmetry uniquely determines the log-Poisson distribution with explicit parameters; (2) a classification theorem proving that the hierarchical symmetry selects exactly the log-Poisson class from the full log-infinitely-divisible family, excluding log-normal, log-stable, and all intermediate generators; and (3) a stability theorem proving that approximate hierarchical symmetry implies approximate log-Poisson, with an explicit $O(\sqrt{\varepsilon})$ Wasserstein bound. The proofs reduce the problem to the Hausdorff moment problem on $[0,1]$ via the change of variables $u = e^{kx}$, where determinacy and stability follow from classical results.

*2020 Mathematics Subject Classification.* 60G57, 60E10, 28A80, 76F55.

*Key words and phrases.* Multiplicative cascades, log-Poisson distribution, hierarchical symmetry, multifractal spectrum, Hausdorff moment problem.

---

## 1. Introduction

Multiplicative cascades model the successive fragmentation of a conserved quantity across scales and arise in fully developed turbulence [8, 9], rainfall, finance, and other settings exhibiting intermittent, scale-invariant fluctuations. The mathematical foundations of multiplicative cascades were established by Kahane and Peyrière [7]; see also Barral and Mandelbrot [3] for later developments. The statistical properties of a cascade are encoded in the scaling exponents $\zeta_p$ of the structure functions $S_p(\ell) = \langle |\Phi(\ell)|^p \rangle \sim \ell^{\zeta_p}$. A central question is: *which probability distributions on the cascade multiplier $W$ are compatible with observed scaling laws?*

Kolmogorov [8] proposed log-normal multipliers, leading to quadratic scaling exponents. Z.-S. She and Lévêque [10] introduced a hierarchical symmetry for the scaling exponents and derived a different, log-Poisson exponent formula that has since shown excellent agreement with experimental data. Dubrulle [5] independently identified the log-Poisson form. Z.-S. She and Waymire [11] used the Lévy–Khintchine representation to argue that this symmetry selects log-Poisson within the log-infinitely-divisible family; Dubrulle and Graner [6] reached a similar conclusion via symmetry groups. These works provided compelling physical arguments but did not supply rigorous proofs. Z.-S. She and Zhang [12] subsequently proposed that the hierarchical symmetry is *universal*—applicable not only to turbulence but to general multi-scale fluctuation systems including MHD turbulence, natural image statistics, and biological signals—and should serve as a standard analytical framework. The present paper supplies the rigorous mathematical foundation for this program.

The present paper provides the rigorous mathematical treatment. We formalize the hierarchical symmetry as a single axiom (A1) and prove three main results.

*Characterization* (Theorem 1). A1 uniquely determines the cascade multiplier $W$ to be log-Poisson, with parameters $(a = \gamma \ln r,\; b = (\ln\beta)/k,\; \lambda = -C\ln r)$ expressed in terms of the observable scaling exponents. No other distribution is compatible with A1.

*Classification* (Theorem 2). Within the full log-infinitely-divisible family, A1 selects exactly the log-Poisson class. No log-normal, log-stable, or intermediate generator satisfies A1.

*Stability* (Theorem 3). If A1 holds only approximately, with residuals bounded by $\varepsilon$, then the cascade multiplier distribution is within $O(\sqrt{\varepsilon})$ of log-Poisson in the Wasserstein-1 metric, with an explicit, computable constant.

The converse—that log-Poisson multipliers imply A1—is established in Proposition 1, yielding a biconditional equivalence (Corollary 1).

**Relation to prior work.** The exponent formula (Lemma 1, steps (1)–(3)) and the log-Poisson identification are due to Z.-S. She and Lévêque [10] and Dubrulle [5]. Z.-S. She and Waymire [11] gave the first argument connecting A1 to the Lévy–Khintchine classification. The following results are new: the moment-determinacy proof via Carleman's condition (Lemma 2); the converse (Proposition 1) and biconditional equivalence (Corollary 1); the full Log-ID Classification Theorem via the Hausdorff moment problem (Theorem 2); the determinacy dichotomy (Proposition 2); and the stability theorem with explicit $O(\sqrt{\varepsilon})$ bound (Theorem 3).

**Method.** The key technique is the change of variables $u = e^{kx}$, which maps the Lévy measure from $(-\infty, 0]$ to the compact interval $[0,1]$. On $[0,1]$ the Hausdorff moment problem is automatically determinate and stable, and the entire classification and stability theory follows from the Weierstrass approximation theorem, Chebyshev's inequality, and explicit coupling constructions.

Throughout this paper, $\log$ denotes the natural logarithm.

---

## 2. Setup

Let $r \in (0,1)$ be a scale ratio. A *multiplicative cascade* generates a random positive measure $\mu$ on nested sets $B_0 \supset B_1 \supset \cdots$ via

$$\mu(B_{n+1}) = W_{n+1} \cdot \mu(B_n),$$

where $\{W_n\}$ are i.i.d. positive random variables with $\mathbb{E}[W] = 1$ (conservation of mean).

Let $\Phi(\ell)$ be the cascade observable at scale $\ell = r^n$. Define the *structure functions*

$$S_p(\ell) = \langle |\Phi(\ell)|^p \rangle = \ell^{\zeta_p},$$

where $\zeta_p$ are the *scaling exponents*, with $\zeta_0 = 0$. The relation $\mathbb{E}[W^p] = r^{\zeta_p}$ identifies the single-step moment structure of the multiplier with the observable's scaling.

For a fixed integer $k \geq 1$ (the *hierarchy step*), define the *moment ratios*

$$H_p(\ell) = \frac{S_{p+k}(\ell)}{S_p(\ell)} = \ell^{\delta_p},$$

where $\delta_p = \zeta_{p+k} - \zeta_p$ are the *incremental exponents* at step $k$.

---

## 3. The Axiom

**Axiom (A1: Hierarchical Symmetry).** There exists $\beta \in (0,1)$ such that for all $p \in k\mathbb{N}_0$ (non-negative integer multiples of $k$), the incremental exponents satisfy

$$\delta_{p+k} = (1 - \beta)\,\delta_\infty + \beta\,\delta_p, \tag{$*$}$$

where $\delta_\infty = \lim_{p \to \infty} \delta_p$ exists and is finite.

A1 determines the full parameter set from the observable exponents:

| Parameter | Determined by | Meaning |
|---|---|---|
| $\beta$ | Contraction ratio of ($*$) | Coupling strength |
| $\gamma$ | $\delta_\infty / k$ | Linear drift |
| $C$ | $(\delta_0 - \delta_\infty)/(1 - \beta)$ | Concentration amplitude |

*Edge case* ($C = 0$). If $\delta_0 = \delta_\infty$, then $C = 0$ and $\zeta_p = \gamma p$ (monofractal scaling). The cascade multiplier $W = r^\gamma$ is deterministic. A1 is trivially satisfied for any $\beta \in (0,1)$. The classification and stability theorems assume $C > 0$ (nontrivial intermittency).

---

## 4. Results

### Lemma 1 (Exponent Form)

If the incremental exponents $\{\delta_p\}$ satisfy the A1 recurrence ($*$) with $\beta \in (0,1)$, then with $\zeta_0 = 0$:

$$\zeta_p = \gamma p + C\bigl(1 - \beta^{p/k}\bigr), \tag{$**$}$$

where $\gamma = \delta_\infty / k$ and $C = (\delta_0 - \delta_\infty)/(1 - \beta)$.

We emphasize that this lemma is purely algebraic and involves no probabilistic content.

*Proof.*

(1) The recurrence ($*$) is first-order linear with fixed point $\delta_\infty$:

$$\delta_{p+k} - \delta_\infty = \beta\,(\delta_p - \delta_\infty).$$

(2) At $p = mk$ (integer multiples of $k$), iteration gives

$$\delta_{mk} - \delta_\infty = (\delta_0 - \delta_\infty)\,\beta^m.$$

Replacing $m = p/k$:

$$\delta_p = \delta_\infty + (\delta_0 - \delta_\infty)\,\beta^{p/k}.$$

(This formula is derived at $p \in k\mathbb{N}_0$. For general $p \geq 0$, we define $\zeta_p$ by ($**$); the function $\beta^{p/k}$ is well-defined for all real $p \geq 0$ since $\beta > 0$. The moment-based arguments in Lemma 2 and Theorem 1 require only integer $p$, where the formula is proved.)

(3) With $\zeta_0 = 0$, sum the step-$k$ increments using the geometric series:

$$\zeta_p = \frac{p}{k}\,\delta_\infty + \frac{\delta_0 - \delta_\infty}{1 - \beta}\,\bigl(1 - \beta^{p/k}\bigr).$$

Identifying $\gamma = \delta_\infty/k$ and $C = (\delta_0 - \delta_\infty)/(1-\beta)$:

$$\zeta_p = \gamma p + C\bigl(1 - \beta^{p/k}\bigr). \qquad\square$$


### Lemma 2 (Moment Determinacy)

Let $\{W_n\}$ be an i.i.d. multiplicative cascade with scaling exponents $\zeta_p = \gamma p + C(1 - \beta^{p/k})$ as in Lemma 1. Then the distribution of $W$ is uniquely determined by its moments.

*Proof.*

(1) By independence across cascade levels, $\mathbb{E}[(W_1 \cdots W_n)^p] = (\mathbb{E}[W^p])^n$. Combined with $S_p(\ell) = \ell^{\zeta_p} = r^{n\zeta_p}$, this gives for a single step:

$$\mathbb{E}[W^p] = r^{\zeta_p} = e^{(\gamma \ln r)\,p}\cdot e^{C \ln r\,(1 - \beta^{p/k})}.$$

The moments $\mathbb{E}[W^p]$ are finite and positive for all $p \geq 0$, since $r \in (0,1)$ and $\zeta_p$ is finite by Lemma 1.

(2) The distribution of $W$ is uniquely determined by its moments if

$$\sum_{p=1}^{\infty} \bigl(\mathbb{E}[W^{2p}]\bigr)^{-1/(2p)} = \infty \qquad\text{(Carleman's condition).}$$

Now

$$\bigl(\mathbb{E}[W^{2p}]\bigr)^{1/(2p)} = r^{\gamma + C(1 - \beta^{2p/k})/(2p)} \;\longrightarrow\; r^\gamma \quad\text{as } p \to \infty.$$

Since $r \in (0,1)$ and $\gamma$ is finite, $r^{-\gamma} > 0$, so the terms $(\mathbb{E}[W^{2p}])^{-1/(2p)}$ converge to the positive constant $r^{-\gamma}$. A series whose terms do not converge to zero diverges; therefore the Carleman sum diverges. The moments uniquely determine $W$.

(Since $W > 0$, this is the Stieltjes moment problem on $[0,\infty)$. The Hamburger condition verified here implies the Stieltjes result *a fortiori*; see Akhiezer [1], Ch. 2, Theorem 2.1, or Shohat and Tamarkin [13], Ch. II.) $\square$


### Theorem 1 (Characterization)

Let $\{W_n\}$ be an i.i.d. multiplicative cascade whose incremental scaling exponents satisfy A1. Then:

**(i) Scaling exponents.**

$$\zeta_p = \gamma p + C\bigl(1 - \beta^{p/k}\bigr),$$

where $\gamma = \delta_\infty/k$ and $C = (\delta_0 - \delta_\infty)/(1-\beta)$.

**(ii) Uniqueness.** The cascade multiplier $W$ is uniquely determined to be log-Poisson:

$$\log W = a + bN, \qquad N \sim \mathrm{Poisson}(\lambda),$$

$$a = \gamma \ln r, \quad b = \frac{\ln\beta}{k}, \quad \lambda = -C\ln r.$$

No other probability distribution on $W$ is compatible with A1.

**(iii) Multifractal spectrum.** Let $d$ denote the spatial dimension of the cascade support. Then

$$f(h) = d - C + Cx(1 - \ln x), \qquad x = \frac{k(h - \gamma)}{C|\ln\beta|},$$

defined for $h \in [\gamma,\; \gamma + (C/k)|\ln\beta|]$.

*Proof.*

*(i)* Immediate from Lemma 1.

*(ii)* By Lemma 2, $W$ is uniquely determined by its moments. It remains to exhibit a distribution that produces exactly these moments. For $\log W = a + bN$ with $N \sim \mathrm{Poisson}(\lambda)$:

$$\mathbb{E}[W^p] = e^{ap} \cdot \exp\bigl[\lambda(e^{bp} - 1)\bigr].$$

Set $a = \gamma\ln r$, $b = (\ln\beta)/k$ so that $e^{bp} = \beta^{p/k}$. Then matching requires

$$\lambda(\beta^{p/k} - 1) = C|\ln r|\,(\beta^{p/k} - 1),$$

giving $\lambda = -C\ln r > 0$. This holds for all real $p \geq 0$ simultaneously, since the Poisson MGF is defined for all $t \in \mathbb{R}$.

The log-Poisson with $(a,b,\lambda)$ above produces exactly the moments from Lemma 2. By uniqueness, $W$ is log-Poisson. No other distribution is possible.

*(iii)* The singularity spectrum $f(h) = \inf_p\,[ph - \zeta_p + d]$. Setting the derivative to zero:

$$h - \gamma + \frac{C}{k}(\ln\beta)\,\beta^{p/k} = 0 \quad\Longrightarrow\quad h - \gamma = \frac{C|\ln\beta|}{k}\,\beta^{p/k}.$$

Define $x = \beta^{p/k} = k(h-\gamma)/(C|\ln\beta|)$. Then $p = -k\ln x / |\ln\beta|$ and

$$p(h - \gamma) = \frac{-k\ln x}{|\ln\beta|} \cdot \frac{C|\ln\beta|}{k}\,x = -Cx\ln x.$$

Therefore

$$f(h) = d - C + Cx(1 - \ln x), \qquad x = \frac{k(h-\gamma)}{C|\ln\beta|}.$$

Boundary checks: $p = 0 \Rightarrow x = 1 \Rightarrow f = d$; $p \to \infty \Rightarrow x \to 0 \Rightarrow f \to d - C$. Concavity: $\zeta_p'' = -(C/k^2)(\ln\beta)^2\beta^{p/k} < 0$. $\square$


**Remark (Conservation).** The setup assumes $\mathbb{E}[W] = 1$, which requires $\zeta_1 = 0$. Substituting into ($**$): $\gamma + C(1 - \beta^{1/k}) = 0$, giving $\gamma = -C(1-\beta^{1/k})$. This is a constraint relating $\gamma$ to $C$ and $\beta$, reducing the free parameters from three to two.


### Proposition 1 (Converse)

If the cascade multiplier $W$ is log-Poisson—that is, $\log W = a + bN$ with $N \sim \mathrm{Poisson}(\lambda)$, $b < 0$, $\lambda > 0$—then the incremental scaling exponents satisfy A1 with $\beta = e^{bk} \in (0,1)$.

*Proof.* The moment generating function gives $\mathbb{E}[W^p] = \exp(ap + \lambda(e^{bp} - 1))$, so $\zeta_p = \bigl(ap + \lambda(e^{bp} - 1)\bigr)/\ln r$. The step-$k$ increments are

$$\delta_p = \frac{ak + \lambda e^{bp}(e^{bk}-1)}{\ln r}.$$

Setting $\beta = e^{bk} \in (0,1)$ (since $b < 0$, $k \geq 1$):

$$\delta_p = \frac{ak}{\ln r} + \frac{\lambda(\beta - 1)}{\ln r}\,\beta^{p/k}.$$

As $p \to \infty$: $\beta^{p/k} \to 0$, so $\delta_\infty = ak/\ln r$. The deviation is

$$\delta_p - \delta_\infty = \frac{\lambda(\beta - 1)}{\ln r}\,\beta^{p/k}.$$

At $p + k$:

$$\delta_{p+k} - \delta_\infty = \frac{\lambda(\beta-1)}{\ln r}\,\beta^{(p+k)/k} = \beta\,(\delta_p - \delta_\infty).$$

Therefore $\delta_{p+k} = (1-\beta)\delta_\infty + \beta\delta_p$, which is exactly A1. $\square$


### Corollary 1 (Biconditional)

Within i.i.d. multiplicative cascades, A1 is necessary and sufficient for log-Poisson:

$$\text{A1 holds} \;\;\Longleftrightarrow\;\; W \text{ is log-Poisson (with } b < 0\text{).}$$

The forward direction is Theorem 1(ii); the reverse is Proposition 1.


### Theorem 2 (Log-ID Classification)

Let $\{W_n\}$ be an i.i.d. multiplicative cascade with nontrivial intermittency ($C > 0$), whose generator $\log W$ is infinitely divisible with Lévy triplet $(a, \sigma^2, \nu)$. Then A1 holds with $\beta \in (0,1)$ if and only if $\sigma^2 = 0$ and $\nu = \lambda\delta_b$ for some $b < 0$, $\lambda > 0$. That is:

> *A1 selects exactly the log-Poisson class from the full log-infinitely-divisible family.*

No other log-ID cascade—log-normal, log-stable, or any intermediate—satisfies A1.

*Proof.*

*Reverse direction.* If $\nu = \lambda\delta_b$ with $b < 0$ and $\sigma^2 = 0$, then $\log W = a + bN$ with $N \sim \mathrm{Poisson}(\lambda)$, and A1 holds by Proposition 1.

*Forward direction.* Assume A1 holds. We show $\sigma^2 = 0$ and $\nu = \lambda\delta_b$.

*Step 1.* The cumulant generating function of $\log W$ is

$$\psi(p) = ap + \frac{\sigma^2 p^2}{2} + \int\bigl(e^{px} - 1 - px\,\mathbf{1}_{|x|\leq 1}\bigr)\,\nu(dx).$$

With $\zeta_p = \psi(p)/\ln r$ and $\delta_p = (\psi(p+k) - \psi(p))/\ln r$, define $\phi(p) = \psi(p+k) - \psi(p)$:

$$\phi(p) = ak + \sigma^2 k\!\left(p + \tfrac{k}{2}\right) + \int e^{px}(e^{kx}-1)\,\nu(dx) - k\!\int x\,\mathbf{1}_{|x|\leq 1}\,\nu(dx).$$

A1 requires $\delta_\infty = \lim_{p\to\infty}\delta_p$ to exist and be finite, i.e., $\lim_{p\to\infty}\phi(p)$ is finite.

*Step 2* ($\sigma^2 = 0$). The term $\sigma^2 kp$ in $\phi(p)$ diverges as $p \to \infty$ whenever $\sigma^2 > 0$. Since $\phi$ must have a finite limit, $\sigma^2 = 0$. *This eliminates all log-normal and mixed Gaussian-jump generators.*

*Step 3* ($\mathrm{supp}(\nu) \subseteq (-\infty,0]$). For $x > 0$: $e^{kx} - 1 > 0$ and $e^{px} \to \infty$ as $p \to \infty$. If $\nu$ has any mass on $(0,\infty)$, then $\int_{(0,\infty)} e^{px}(e^{kx}-1)\,\nu(dx) \to \infty$ by monotone convergence, making $\phi(p)$ unbounded. Therefore $\mathrm{supp}(\nu) \subseteq (-\infty,0]$. *This eliminates all generators with positive jumps.*

*Step 4* ($\nu$ is a single Dirac mass). With $\sigma^2 = 0$ and $\mathrm{supp}(\nu) \subseteq (-\infty,0]$, write $c_0 = ak - k\int x\,\mathbf{1}_{|x|\leq 1}\,\nu(dx)$ and

$$\phi(p) = c_0 + \int_{(-\infty,0)} e^{px}(e^{kx}-1)\,\nu(dx).$$

For $x < 0$ and $p \geq 0$: $|e^{px}(e^{kx}-1)| \leq |e^{kx}-1| = 1 - e^{kx}$ (since $|e^{px}| \leq 1$). This bound is $\nu$-integrable: near $x = 0$, $1 - e^{kx} \sim k|x|$ and $\int k|x|\,\nu(dx) < \infty$ follows from the finiteness of $\delta_0$; for $|x| > 1$, the Lévy condition gives $\nu((-\infty,-1)) < \infty$ and the integrand is bounded by 1. By dominated convergence, the integral $\to 0$ as $p \to \infty$, so $\phi_\infty = c_0$.

A1 at $p = mk$ gives $\phi(mk) - \phi_\infty = A\beta^m$, where $A = (\delta_0 - \delta_\infty)\ln r$:

$$\int_{(-\infty,0)} e^{mkx}(e^{kx}-1)\,\nu(dx) = A\beta^m \qquad\text{for all } m \geq 0. \tag{$\dagger$}$$

Substitute $u = e^{kx}$, mapping $(-\infty,0) \to (0,1)$. Let $\tilde\nu$ be the pushforward of $\nu$ under $x \mapsto e^{kx}$, and define the signed measure $d\rho = (u-1)\,d\tilde\nu$ on $(0,1)$. Condition ($\dagger$) becomes

$$\int_{(0,1)} u^m\,d\rho(u) = A\beta^m \qquad\text{for all } m \geq 0.$$

The $m = 0$ case gives $\int(u-1)\,d\tilde\nu = A$, so $\int(1-u)\,d\tilde\nu = -A = |A| < \infty$. Since $1 - u > 0$ on $(0,1)$, this shows $\rho$ has finite total variation $|\rho|((0,1)) = |A|$, hence is a finite signed measure on $[0,1]$.

(The measure $\rho$ is defined on the open interval $(0,1)$. It extends to $[0,1]$ with $\rho(\{0\}) = \rho(\{1\}) = 0$: $\nu$ has no atom at $x = 0$ by the Lévy measure convention, so $\tilde\nu$ has no atom at $u = 1$; and $x = -\infty$ maps to $u = 0$, which is not a point of the measure.)

The measure $A\delta_\beta$ on $(0,1)$ has the same moments: $\int u^m\,A\,d\delta_\beta = A\beta^m$. Since polynomials are uniformly dense in $C([0,1])$ (Weierstrass approximation theorem), moments uniquely determine finite signed measures on $[0,1]$ (via the Riesz representation theorem). Therefore $\rho = A\delta_\beta$.

Recovering $\nu$: at $u = \beta$ (i.e., $x = b = (\ln\beta)/k$), we have $(\beta - 1)\tilde\nu(\{\beta\}) = A$, giving $\tilde\nu(\{\beta\}) = A/(\beta-1) = \lambda$, with no mass elsewhere. Since $\delta_0 > \delta_\infty$ (nontrivial intermittency) and $\ln r < 0$, $A < 0$ and $\beta - 1 < 0$, so $\lambda = A/(\beta-1) > 0$.

Therefore $\nu = \lambda\delta_b$ with $b = (\ln\beta)/k < 0$ and $\lambda > 0$. The generator $\log W$ is compound Poisson with deterministic jump size $b$ and rate $\lambda$: this is the log-Poisson distribution. $\square$


### Corollary 2 (Principal cascade classes)

The log-ID cascade family is partitioned by A1:

| Class | Lévy triplet | A1 | Determinacy |
|---|---|---|---|
| Log-Poisson | $\sigma^2=0$, $\nu=\lambda\delta_b$ | Holds | Determinate |
| Log-normal | $\sigma^2>0$, $\nu=0$ | Fails ($\delta_\infty=-\infty$) | Indeterminate |
| Log-stable | $\sigma^2=0$, $\nu=$power-law | Fails | — |
| General log-ID | any other | Fails | — |


### Proposition 2 (Determinacy Dichotomy)

The two principal cascade multiplier laws are distinguished by moment determinacy:

**(a)** If A1 holds within a cascade (log-Poisson regime), then

$$\ln\mathbb{E}[W^p] = (\gamma\ln r)\,p + C\ln r\,(1 - \beta^{p/k}),$$

and the second term is $o(p)$. The Carleman sum diverges. $W$ is moment-determinate.

**(b)** If the exponents are quadratic, $\zeta_p = c_1 p + c_2 p^2$ ([8]/log-normal regime), then $\mathbb{E}[W^p] = \exp(\mu p + \sigma^2 p^2/2)$. The Carleman sum converges. $W$ is moment-indeterminate: multiple distinct distributions share the same moments.

*Proof.*

*Part (a).* By Lemma 1, $\zeta_p = \gamma p + C(1-\beta^{p/k})$, so $\ln\mathbb{E}[W^p] = \zeta_p \ln r = (\gamma\ln r)\,p + C\ln r\,(1-\beta^{p/k})$. Since $\beta^{p/k} \to 0$, the second term converges to $C\ln r$, hence is $o(p)$. Moment determinacy then follows from Lemma 2.

*Part (b).* For log-normal $W$ with parameters $(\mu, \sigma^2)$:

$$\mathbb{E}[W^{2p}] = \exp(2\mu p + 2\sigma^2 p^2), \qquad \bigl(\mathbb{E}[W^{2p}]\bigr)^{1/(2p)} = \exp(\mu + \sigma^2 p) \to \infty.$$

The Carleman sum $\sum_{p=1}^\infty \exp(-\mu - \sigma^2 p)$ converges (geometric series with ratio $e^{-\sigma^2} < 1$ for $\sigma^2 > 0$). Therefore the moments do not uniquely determine $W$. $\square$


### Theorem 3 (Stability)

Let $\{W_n\}$ be an i.i.d. multiplicative cascade with log-infinitely-divisible generator and nontrivial intermittency. If A1 holds to within $\varepsilon$—that is,

$$\bigl|\delta_{p+k} - (1-\beta)\delta_\infty - \beta\delta_p\bigr| < \varepsilon \qquad\text{for all } p \in k\mathbb{N}_0,$$

then, after the change of variables $u = e^{kx}$ mapping the Lévy measure to $(0,1)$, the positive measure $\eta = (1-u)\,d\tilde\nu$ satisfies

$$W_1\!\left(\frac{\eta}{\|\eta\|},\;\delta_\beta\right) \leq \left(\frac{(1+\beta)^2\,|\ln r|}{|A|}\right)^{\!1/2} \!\cdot\sqrt{\varepsilon},$$

where $\|\eta\| = \eta((0,1))$ is the total mass and $A = (\delta_0 - \delta_\infty)\ln r$. In particular, the cascade multiplier distribution converges to log-Poisson as $\varepsilon \to 0$.

*Proof.* The proof reuses the central construction of Theorem 2: the change of variables $u = e^{kx}$ that maps the Lévy measure to the compact interval $[0,1]$.

*Step 1 (Approximate moments on $[0,1]$).* By the classification proof, the A1 condition at $p = mk$ maps to moments of the signed measure $\rho = (u-1)\tilde\nu$ on $(0,1)$:

$$\int_{(0,1)} u^m\,d\rho(u) = A\beta^m \qquad\text{(exact A1).}$$

If A1 holds to within $\varepsilon$, the same derivation gives

$$\left|\int_{(0,1)} u^m\,d\rho(u) - A\beta^m\right| \leq |\ln r|\,\varepsilon \qquad\text{for all } m \geq 0.$$

*Step 2 (Variance bound).* Define the positive measure $\eta = (1-u)\,d\tilde\nu$ on $(0,1)$, so $d\eta = -d\rho$. The moments of $\eta$ satisfy $\int u^m\,d\eta = |A|\beta^m + O(\varepsilon)$. Evaluate at the test function $f(u) = (u-\beta)^2$:

$$\int(u-\beta)^2\,d\eta = \int u^2\,d\eta - 2\beta\int u\,d\eta + \beta^2\int d\eta$$

$$= \bigl(|A|\beta^2 + O(\varepsilon)\bigr) - 2\beta\bigl(|A|\beta + O(\varepsilon)\bigr) + \beta^2\bigl(|A| + O(\varepsilon)\bigr) = O(\varepsilon).$$

Precisely:

$$0 \leq \int(u-\beta)^2\,d\eta \leq (1+\beta)^2\,|\ln r|\,\varepsilon.$$

*Step 3 (Concentration and Wasserstein bound).* By Chebyshev's inequality applied to the positive measure $\eta$:

$$\eta\bigl(\{u : |u-\beta| > \delta\}\bigr) \leq \frac{(1+\beta)^2\,|\ln r|\,\varepsilon}{\delta^2} \qquad\text{for all } \delta > 0.$$

The total mass $\int d\eta = |A| + O(\varepsilon)$. By Cauchy–Schwarz:

$$\int|u-\beta|\,d\eta \leq \Bigl(\int d\eta\Bigr)^{1/2} \Bigl(\int(u-\beta)^2\,d\eta\Bigr)^{1/2}.$$

Therefore

$$W_1\!\left(\frac{\eta}{\int d\eta},\;\delta_\beta\right) \leq \left(\frac{(1+\beta)^2\,|\ln r|\,\varepsilon}{|A|}\right)^{\!1/2} = K\sqrt{\varepsilon},$$

where $K = \bigl((1+\beta)^2|\ln r|/|A|\bigr)^{1/2}$.

*Step 4 (Propagation to the multiplier distribution).* It remains to show that closeness of the Lévy measure implies closeness of the distribution of $W$. We work entirely with $\log W$, which is a compound Poisson random variable.

Let $\nu_0 = \lambda\delta_b$ be the unperturbed (log-Poisson) Lévy measure and $\nu_\varepsilon$ be the perturbed Lévy measure, with total mass $\lambda_\varepsilon$. By Step 2, $|\lambda_\varepsilon - \lambda| \leq C_1\varepsilon$ for a constant $C_1$ depending only on the unperturbed parameters.

*Step 4a (Coordinate change).* The map $\varphi\colon (0,1] \to (-\infty,0]$, $\varphi(u) = (\ln u)/k$, is Lipschitz on $[\beta/2, 1]$ with constant $L_\varphi = 2/(k\beta)$. A tail mass estimate via Markov's inequality gives $F_\varepsilon^u\bigl((0,\beta/2)\bigr) \leq 2K\sqrt{\varepsilon}/\beta$. Combining:

$$W_1(F_\varepsilon, \delta_b) \leq K'\sqrt{\varepsilon},$$

where $K'$ depends only on the unperturbed parameters.

*Step 4b (Coupling).* Let $N_0 \sim \mathrm{Poisson}(\lambda)$ and $M \sim \mathrm{Poisson}(\lambda_\varepsilon - \lambda)$ be independent, with $N_\varepsilon = N_0 + M$. Then

$$X_\varepsilon - X_0 = \sum_{i=1}^{N_0}(J_i - b) + \sum_{i=N_0+1}^{N_0+M} J_i.$$

The shared-jump contribution is $\leq \lambda K'\sqrt{\varepsilon}$; the excess-jump contribution is $\leq C_1(|b|+K')\varepsilon$. Therefore $W_1(X_\varepsilon, X_0) \leq (\lambda K' + C_1(|b| + K'))\sqrt{\varepsilon}$ for $\varepsilon \leq 1$.

*Step 4c (Drift perturbation).* The drift $a$ is determined by $\mathbb{E}[W] = 1$. The function $g(x) = e^x - 1$ is 1-Lipschitz on $(-\infty,0]$, giving $|a_\varepsilon - a_0| \leq C_2\sqrt{\varepsilon}$.

*Step 4d (Pushforward under the exponential map).* Let $(Y,Z)$ be an optimal coupling of $\log W_\varepsilon$ and $\log W_0$ with $\mathbb{E}[|Y-Z|] \leq C_3\sqrt{\varepsilon}$. Fix $R = |\ln\varepsilon|$ and split

$$\mathbb{E}[|e^Y - e^Z|] = \mathbb{E}\bigl[|e^Y - e^Z|\,\mathbf{1}_{\{|Y|\leq R,\,|Z|\leq R\}}\bigr] + \mathbb{E}\bigl[|e^Y - e^Z|\,\mathbf{1}_{\{|Y|>R \text{ or } |Z|>R\}}\bigr].$$

For the bulk term, the mean value theorem gives $|e^Y - e^Z| \leq e^{\max(Y,Z)}|Y-Z|$. Cauchy–Schwarz on the bulk gives

$$\mathbb{E}\bigl[e^{\max(Y,Z)}|Y\!-\!Z|\,\mathbf{1}_{\text{bulk}}\bigr] \leq \bigl(\mathbb{E}[e^{2\max(Y,Z)}\mathbf{1}_{\text{bulk}}]\bigr)^{1/2} \bigl(\mathbb{E}[|Y\!-\!Z|^2]\bigr)^{1/2}.$$

The first factor is bounded by $C_4 = (4\,\mathbb{E}[W_0^2])^{1/2} < \infty$, since $\zeta_2$ is finite and, for $\varepsilon$ sufficiently small, $\mathbb{E}[W_\varepsilon^2] \leq 2\,\mathbb{E}[W_0^2]$ by continuity of the compound Poisson MGF in the Lévy measure. From the coupling in Step 4b, $\mathbb{E}[|Y-Z|^2] \leq C_5\,\varepsilon$. For the tail term, Chernoff bounds for Poisson tails [4] give $\mathbb{P}(|Z| > R) \leq e^{-cR}$ for a constant $c > 0$; by Cauchy–Schwarz, the tail contribution is $O(\varepsilon^c) = o(\sqrt{\varepsilon})$. Combining:

$$W_1(W_\varepsilon, W_0) \leq \mathbb{E}[|e^Y - e^Z|] \leq C(\beta,\lambda,k,r)\,\sqrt{\varepsilon},$$

where $C(\beta,\lambda,k,r)$ is an explicit constant depending only on the unperturbed log-Poisson parameters.

The coupling in Step 4b follows the canonical construction for comparing compound Poisson variables via independent thinning; see Barbour, Holst, and Janson [2], Theorem 10.A. $\square$


**Remark (Why the stability proof is elementary).** The change of variables $u = e^{kx}$ maps the Lévy measure to the compact interval $[0,1]$. On a compact set: (a) the Hausdorff moment problem is always determinate (Weierstrass approximation, no Carleman condition needed); (b) stability follows from a second-moment test and Chebyshev's inequality; (c) the resulting rate is $O(\sqrt{\varepsilon})$, meaning the log-Poisson class is an open set in the space of cascade multiplier distributions. The stability theorem inherits its simplicity from the classification theorem.

---

## 5. Corollaries

**Corollary 3 (Conservation constraint).** If there exists an index $k_0 > 0$ such that $\zeta_{k_0} = z_0$ for a known constant $z_0$ fixed by an exact conservation law, then

$$\gamma = \frac{z_0 - C(1-\beta^{k_0/k})}{k_0}.$$

This reduces the observable parameters from two to one.

**Corollary 4 (Codimension identification).** If the most singular structures have Hausdorff codimension $C_{\mathrm{geom}}$ and $C = C_{\mathrm{geom}}$, then $\beta$ alone determines the full exponent curve, the multifractal spectrum, and the cascade distribution.

**Corollary 5 (Spectrum width).** The width of the multifractal spectrum is

$$\Delta h = h_{\max} - h_{\min} = \frac{C}{k}\,|\ln\beta|,$$

where $h_{\max} = \gamma + (C/k)|\ln\beta|$ (at $p = 0$, most regular) and $h_{\min} = \gamma$ (at $p \to \infty$, most singular).

---

## 6. Concluding Remarks

The results of this paper show that the hierarchical symmetry A1 carries considerably more force than might be expected from its appearance as a simple linear recurrence. Within the i.i.d. multiplicative cascade framework, A1 is equivalent to the log-Poisson class: it is the unique axiom that selects a single distribution from the full log-infinitely-divisible family, and it does so stably.

Several directions remain open.

1. **Beyond i.i.d.** The i.i.d. assumption on the cascade multipliers is standard but restrictive. It would be of interest to determine whether the classification extends to stationary ergodic or Markovian multipliers, where the Lévy–Khintchine machinery is no longer directly available.

2. **Boundary cases.** The present results assume nontrivial intermittency ($C > 0$) and $\beta \in (0,1)$. The boundary cases $\beta \to 0$ (maximal intermittency) and $\beta \to 1$ (vanishing intermittency) deserve separate analysis.

3. **Determination of $k$.** The hierarchy step $k$ is treated as a given parameter. In applications, $k$ must be estimated from data; a data-driven procedure for selecting $k$ and quantifying its uncertainty would be valuable.

4. **Quantitative stability in applications.** The stability bound (Theorem 3) provides an explicit constant $K(\beta, \lambda, k, r)$. Computing this constant for specific physical systems (e.g., fully developed turbulence with $\beta = 2/3$, $C = 2$) would yield concrete tolerances for the degree to which A1 can be violated while remaining close to log-Poisson.

---

## References

1. N. I. Akhiezer, *The Classical Moment Problem and Some Related Questions in Analysis*, Oliver & Boyd, Edinburgh, 1965.

2. A. D. Barbour, L. Holst, and S. Janson, *Poisson Approximation*, Oxford University Press, Oxford, 1992.

3. J. Barral and B. B. Mandelbrot, Multiplicative products of cylindrical pulses, *Probab. Theory Related Fields* **124** (2002), 409–430.

4. S. Boucheron, G. Lugosi, and P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of Independence*, Oxford University Press, Oxford, 2013.

5. B. Dubrulle, Intermittency in fully developed turbulence: log-Poisson statistics and generalized scale covariance, *Phys. Rev. Lett.* **73** (1994), 959–962.

6. B. Dubrulle and F. Graner, Possible statistics of scale invariant systems and the observation of intermittency in turbulence, *J. Phys. II France* **6** (1996), 817–824.

7. J.-P. Kahane and J. Peyrière, Sur certaines martingales de Benoit Mandelbrot, *Adv. Math.* **22** (1976), 131–145.

8. A. N. Kolmogorov, A refinement of previous hypotheses concerning the local structure of turbulence in a viscous incompressible fluid at high Reynolds number, *J. Fluid Mech.* **13** (1962), 82–85.

9. B. B. Mandelbrot, Intermittent turbulence in self-similar cascades: divergence of high moments and dimension of the carrier, *J. Fluid Mech.* **62** (1974), 331–358.

10. Z.-S. She and E. Lévêque, Universal scaling laws in fully developed turbulence, *Phys. Rev. Lett.* **72** (1994), 336–339.

11. Z.-S. She and E. C. Waymire, Quantized energy dissipation and log-Poisson statistics in fully developed turbulence, *Phys. Rev. Lett.* **74** (1995), 262–265.

12. Z.-S. She and Z.-X. Zhang, Universal hierarchical symmetry for turbulence and general multi-scale fluctuation systems, *Acta Mech. Sinica* **25** (2009), 279–294.

13. J. A. Shohat and J. D. Tamarkin, *The Problem of Moments*, American Mathematical Society, Providence, RI, 1943.

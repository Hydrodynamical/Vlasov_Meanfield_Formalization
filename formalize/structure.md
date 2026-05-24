# Outline of Derivation of the Vlasov Equation from N-Particle Hamiltonian Dynamics

## Notation

- `\R` → `\mathbb{R}` — real numbers (`ℝ` in Lean / Mathlib)
- `\T` → `\mathbb{T}` — torus (defined but not used in the body)
- `\N` → `\mathbb{N}` — natural numbers (`ℕ`)
- `\eps` → `\varepsilon` — small parameter (epsilon)
- `\X` → `\mathbf{X}` — bold X; tuple of positions `(x_1, …, x_N) ∈ (ℝ^d)^N`
- `\V` → `\mathbf{V}` — bold V; tuple of velocities `(v_1, …, v_N) ∈ (ℝ^d)^N`
- `\Z` → `\mathbf{Z}` — bold Z; phase-space configuration `(\X, \V) ∈ (ℝ^d × ℝ^d)^N`
- `\supp` → `supp` — support of a function or measure (`MeasureTheory.Measure.support`)
- `\Lip` → `Lip` — Lipschitz constant (`LipschitzWith` / `Real.lipschitzWith`)

---

## Items

### 1. Equation (Hamiltonian)   {#eq:HN}
**Kind:** equation
**Tex label:** eq:HN
**Depends on:** none
**Statement (informal):**
> The mean-field Hamiltonian for N identical unit-mass particles in ℝ^d is
> H_N(X, V) = Σ_{i=1}^{N} |v_i|²/2  +  (1/N) Σ_{1 ≤ i < j ≤ N} W(x_i − x_j),
> where the factor 1/N normalizes the interaction energy so that kinetic and potential energies
> are of the same order as N → ∞.
**Symbols introduced:**
- `H_N` — the N-particle Hamiltonian; a function `(Fin N → ℝ^d) × (Fin N → ℝ^d) → ℝ`
- `W` — pair potential; a function `ℝ^d → ℝ`
- `N` — number of particles; `ℕ`
- `d` — spatial dimension; `ℕ` with `d ≥ 1`

---

### 2. Equation (Hamilton / Newton equations of motion)   {#eq:newton}
**Kind:** equation
**Tex label:** eq:newton
**Depends on:** eq:HN
**Statement (informal):**
> The Hamilton equations derived from H_N are
> ẋ_i = v_i,   v̇_i = −(1/N) Σ_{j ≠ i} ∇W(x_i − x_j),   for i = 1, …, N.
> These are the N-particle mean-field Newton equations (second-order ODE system).
**Symbols introduced:**
- `∇W` — gradient of the pair potential; `ℝ^d → ℝ^d`

---

### 3. Assumption   {#ass:W}
**Kind:** assumption
**Tex label:** ass:W
**Depends on:** none
**Statement (informal):**
> The pair potential W : ℝ^d → ℝ belongs to C^{1,1}(ℝ^d) (i.e., has a globally Lipschitz
> gradient), is even (W(−x) = W(x) for all x), and the Lipschitz constant of its gradient is
> finite:
> L := Lip(∇W) = sup_{x ≠ y} |∇W(x) − ∇W(y)| / |x − y|  <  ∞.
**Symbols introduced:**
- `L` — Lipschitz constant of ∇W; `ℝ≥0` (or `ℝ` with a positivity hypothesis); expected Mathlib type `NNReal` or the hypothesis `LipschitzWith L (∇W)`

---

### 4. Definition (Empirical measure)   {#def:empirical}
**Kind:** definition
**Tex label:** none
**Depends on:** eq:newton
**Statement (informal):**
> The empirical measure of a configuration Z = (X, V) ∈ (ℝ^d × ℝ^d)^N is the probability
> measure on ℝ^d × ℝ^d defined by
> μ^N[Z] := (1/N) Σ_{i=1}^{N} δ_{(x_i, v_i)}.
> Along a solution t ↦ (X(t), V(t)) of eq:newton, one writes μ_t^N := μ^N[X(t), V(t)].
**Symbols introduced:**
- `μ^N[Z]` — empirical measure; `MeasureTheory.Measure (ℝ^d × ℝ^d)`, specifically a `MeasureTheory.ProbabilityMeasure`
- `μ_t^N` — time-dependent empirical measure along a solution; a curve `ℝ → MeasureTheory.ProbabilityMeasure (ℝ^d × ℝ^d)`
- `δ_{z}` — Dirac delta at z; `MeasureTheory.Measure.dirac z`

---

### 5. Proposition (Weak evolution of the empirical measure)   {#prop:weak}
**Kind:** proposition
**Tex label:** prop:weak
**Depends on:** eq:newton, def:empirical, ass:W
**Statement (informal):**
> Let (X, V) : [0, T] → (ℝ^d × ℝ^d)^N solve eq:newton, and let ρ_t^N(x) := ∫ μ_t^N(dx, dv)
> be the spatial marginal. Then for every test function φ ∈ C_c^∞(ℝ^d × ℝ^d),
> d/dt ⟨μ_t^N, φ⟩ = ⟨μ_t^N, v · ∇_x φ − (∇W * ρ_t^N) · ∇_v φ⟩  +  R_N(t),
> where the remainder satisfies |R_N(t)| ≤ (1/N) ‖∇W‖_∞ ‖∇_v φ‖_∞ and vanishes identically
> when ∇W(0) = 0. Under Assumption ass:W (W even ⟹ ∇W(0) = 0), one has R_N ≡ 0.
**Symbols introduced:**
- `ρ_t^N` — spatial marginal of μ_t^N; `MeasureTheory.Measure ℝ^d`
- `⟨μ, φ⟩` — integral of φ against μ; `∫ φ dμ` in Mathlib notation
- `∇W * ρ` — convolution of ∇W with the measure ρ; `(fun x => ∫ ∇W(x − y) dρ(y))`
- `R_N(t)` — remainder term from the diagonal i = j; `ℝ`

---

### 6. Equation (Weak form of empirical-measure evolution)   {#eq:weak-eq}
**Kind:** equation
**Tex label:** eq:weak-eq
**Depends on:** prop:weak
**Statement (informal):**
> The distributional evolution identity for the empirical measure:
> d/dt ⟨μ_t^N, φ⟩  =  ⟨μ_t^N, v · ∇_x φ − (∇W * ρ_t^N) · ∇_v φ⟩  +  R_N(t),
> for every φ ∈ C_c^∞(ℝ^d × ℝ^d), with remainder bound |R_N(t)| ≤ (1/N) ‖∇W‖_∞ ‖∇_v φ‖_∞.
> This is eq:weak-eq referenced throughout the paper; it is the content of Proposition prop:weak.
**Symbols introduced:**
- (No new symbols beyond those in prop:weak)

---

### 7. Corollary   {#cor:empirical-vlasov}
**Kind:** corollary
**Tex label:** cor:empirical-vlasov
**Depends on:** prop:weak, ass:W, eq:weak-eq, eq:vlasov
**Statement (informal):**
> Under Assumption ass:W, the empirical measure μ_t^N is a distributional solution of the
> nonlinear Vlasov equation eq:vlasov, in the sense that eq:weak-eq holds with R_N ≡ 0 for
> every φ ∈ C_c^∞(ℝ^d × ℝ^d).
**Symbols introduced:**
- (No new symbols)

---

### 8. Equation (Vlasov equation)   {#eq:vlasov}
**Kind:** equation
**Tex label:** eq:vlasov
**Depends on:** eq:weak-eq
**Statement (informal):**
> The nonlinear Vlasov equation (the formal N → ∞ limit of eq:weak-eq) is the PDE
> ∂_t f + v · ∇_x f − (∇W * ρ_t)(x) · ∇_v f = 0,
> with ρ_t(x) = ∫_{ℝ^d} f(t, x, v) dv.
> Here f = f(t, x, v) is a time-dependent probability measure on ℝ^d × ℝ^d (or a density),
> and ρ_t is its spatial marginal.
**Symbols introduced:**
- `f` — solution of the Vlasov equation; `MeasureTheory.ProbabilityMeasure (ℝ^d × ℝ^d)` (measure-valued), or a density `ℝ^{≥0} × ℝ^d × ℝ^d → ℝ≥0`
- `ρ_t` — spatial marginal of f_t; `MeasureTheory.Measure ℝ^d`

---

### 9. Theorem (Existence and uniqueness for Vlasov)   {#thm:vlasov-wp}
**Kind:** theorem
**Tex label:** thm:vlasov-wp
**Depends on:** ass:W, eq:vlasov, eq:char
**Statement (informal):**
> Let f_0 ∈ 𝒫_1(ℝ^d × ℝ^d) be a probability measure with finite first moment. Under
> Assumption ass:W, there exists a unique narrowly continuous curve t ↦ f_t ∈ 𝒫_1(ℝ^d × ℝ^d)
> satisfying the Vlasov equation eq:vlasov in the distributional sense with initial condition
> f_{t=0} = f_0.
**Symbols introduced:**
- `𝒫_1(ℝ^d × ℝ^d)` — probability measures on ℝ^d × ℝ^d with finite first moment; `MeasureTheory.ProbabilityMeasure` with an additional `∫ ‖z‖ dμ < ∞` hypothesis (Mathlib: `MeasureTheory.Memℒp` or `HasFiniteIntegral`)

---

### 10. Equation (Characteristic / mean-field ODE)   {#eq:char}
**Kind:** equation
**Tex label:** eq:char
**Depends on:** eq:vlasov
**Statement (informal):**
> The mean-field characteristic ODE associated to the Vlasov equation is
> Ẋ(t, z) = V(t, z),   V̇(t, z) = −(∇W * ρ_t)(X(t, z)),   (X, V)(0, z) = z,
> where ρ_t = (X(t, ·))_# (∫ f_0 dv) is the pushforward of the initial spatial marginal
> under the position flow. The solution f_t is then the pushforward f_t = (X(t,·), V(t,·))_# f_0.
**Symbols introduced:**
- `X(t, z)` — position component of the characteristic flow; `ℝ → ℝ^d × ℝ^d → ℝ^d`
- `V(t, z)` — velocity component of the characteristic flow; `ℝ → ℝ^d × ℝ^d → ℝ^d`
- `(Φ)_# μ` — pushforward of a measure under a map Φ; `MeasureTheory.Measure.map`

---

### 11. Theorem (Dobrushin, 1979)   {#thm:dobrushin}
**Kind:** theorem
**Tex label:** thm:dobrushin
**Depends on:** ass:W, eq:vlasov, eq:dobrushin
**Statement (informal):**
> Under Assumption ass:W, there exists a constant C = C(L) > 0 such that for any two
> measure-valued solutions f_t, g_t ∈ 𝒫_1(ℝ^d × ℝ^d) of the Vlasov equation eq:vlasov,
> W_1(f_t, g_t) ≤ e^{Ct} W_1(f_0, g_0)   for all t ≥ 0,
> where W_1 is the Wasserstein-1 distance. The proof (sketched in the paper) uses a coupling
> argument via the characteristic flows eq:char and a Gronwall inequality; the key estimate is
> |∇W * ρ − ∇W * σ|_∞ ≤ L · W_1(ρ, σ). Attribution: Dobrushin (1979), see [Dobrushin].
**Symbols introduced:**
- `W_1(μ, ν)` — Wasserstein-1 (Kantorovich–Rubinstein) distance; `MeasureTheory.ProbabilityMeasure.wasserstein 1` or `MeasureTheory.Measure.toFiniteWasserstein` in Mathlib
- `C(L)` — explicit constant depending only on L = Lip(∇W); `ℝ`, stated to exist but not given explicitly

---

### 12. Equation (Dobrushin stability estimate)   {#eq:dobrushin}
**Kind:** equation
**Tex label:** eq:dobrushin
**Depends on:** thm:dobrushin
**Statement (informal):**
> The exponential Wasserstein-1 stability estimate for Vlasov solutions:
> W_1(f_t, g_t) ≤ e^{Ct} · W_1(f_0, g_0),   for all t ≥ 0,
> for any two measure solutions f_t, g_t of eq:vlasov. This is the content of Theorem thm:dobrushin.
**Symbols introduced:**
- (No new symbols beyond those in thm:dobrushin)

---

### 13. Corollary (Mean-field limit)   {#cor:mfl}
**Kind:** corollary
**Tex label:** cor:mfl
**Depends on:** thm:dobrushin, cor:empirical-vlasov, eq:dobrushin
**Statement (informal):**
> Let f_0 ∈ 𝒫_1(ℝ^d × ℝ^d), and let (X_0^N, V_0^N) be initial particle data whose empirical
> measure μ_0^N satisfies W_1(μ_0^N, f_0) → 0 as N → ∞. Under Assumption ass:W, for every
> T > 0,
> sup_{t ∈ [0,T]} W_1(μ_t^N, f_t) ≤ e^{CT} · W_1(μ_0^N, f_0)  →  0   as N → ∞,
> where f_t is the unique Vlasov solution with initial datum f_0 (from thm:vlasov-wp) and μ_t^N
> is the empirical measure of the N-particle system. This is the mean-field limit theorem.
**Symbols introduced:**
- (No new symbols)

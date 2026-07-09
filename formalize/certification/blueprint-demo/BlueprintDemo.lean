import Architect
import Vlasov.Basic
import Vlasov.OT.Wasserstein
import Vlasov.OT.Coupling
import Vlasov.OT.CharacteristicFlow
import Vlasov.OT.WeakToLagrangian

/-!
# Vlasov blueprint driver

This module tags a curated set of the Vlasov project's headline declarations with
`@[blueprint …]` so that LeanArchitect can extract a dependency graph + LaTeX nodes for
the rendered blueprint.  Tagging is done via `attribute [blueprint …]` here in the driver
(rather than on the production source), so that `Vlasov/Vlasov/*` is left untouched.

Dependency edges between nodes are collected automatically from the actual Lean proof terms,
so tagging a connected set of declarations makes the graph wire itself.

The node set and its narrative order follow the companion paper (PAPER.tex, "Mathematician
in the Loop"): the Newton-to-Vlasov derivation, the Kantorovich–Rubinstein $W_1$ distance,
well-posedness, Dobrushin stability and the mean-field limit, and the weak ⟹ Lagrangian
superposition principle.  Where a node corresponds to a numbered statement of the paper,
the paper's number appears in its title.
-/

open Vlasov

/-! ## Chapter 1 — From Newton to the Vlasov equation (Basic.lean) -/

attribute [blueprint "ass:W"
  (title := /-- Assumption 1 of the paper ($\mathrm{AssW}$) -/)
  (statement := /-- Let $W : \mathbb{R}^d \to \mathbb{R}$ be an even function of class
    $C^{1,1}$: differentiable, with a globally Lipschitz gradient of constant
    $L := \mathrm{Lip}(\nabla W) < \infty$.  This assumption is in force throughout.
    Evenness gives $\nabla W(0) = 0$ — the cancellation that makes the empirical measure
    an \emph{exact} weak solution below. -/)]
  Vlasov.AssW

attribute [blueprint "def:hamiltonian"
  (statement := /-- The mean-field Hamiltonian of $N$ identical unit-mass particles,
    \[ H_N(X,V) \;=\; \sum_{i=1}^{N} \frac{|v_i|^2}{2}
       \;+\; \frac{1}{N} \sum_{1 \le i < j \le N} W(x_i - x_j). \]
    The $1/N$ scaling keeps the kinetic and potential energies of the same order as
    $N \to \infty$. -/)]
  Vlasov.hamiltonianN

attribute [blueprint "def:newton"
  (statement := /-- Newton's equations for $N$ particles under the mean-field force:
    \[ \dot x_i = v_i, \qquad
       \dot v_i = -\frac{1}{N} \sum_{j \ne i} \nabla W(x_i - x_j), \qquad i = 1, \dots, N. \]
    A solution is a curve $(X,V) : \mathbb{R} \to (\mathbb{R}^d \times \mathbb{R}^d)^N$
    satisfying both systems at every time. -/)]
  Vlasov.IsNewtonSolution

attribute [blueprint "def:empirical"
  (statement := /-- The empirical measure of a configuration
    $(X,V) \in (\mathbb{R}^d \times \mathbb{R}^d)^N$:
    \[ \mu^N[X,V] \;:=\; \frac{1}{N} \sum_{i=1}^{N} \delta_{(x_i,\,v_i)}, \]
    a probability measure on phase space. -/)]
  Vlasov.empiricalMeasure

attribute [blueprint "def:empirical-curve"
  (statement := /-- The curve of empirical measures $t \mapsto \mu^N_t$ carried by a
    solution of Newton's equations. -/)]
  Vlasov.empiricalMeasureCurve

attribute [blueprint "prop:weak-evolution"
  (title := /-- Weak evolution of the empirical measure -/)
  (statement := /-- Along any Newton solution, for every test function
    $\varphi \in C_c^\infty(\mathbb{R}^d \times \mathbb{R}^d)$ the pairing
    $t \mapsto \langle \mu^N_t, \varphi \rangle$ is differentiable and
    \[ \frac{\mathrm{d}}{\mathrm{d}t} \langle \mu^N_t, \varphi \rangle
       \;=\; \big\langle \mu^N_t,\; v \cdot \nabla_x \varphi
       - (\nabla W * \rho^N_t) \cdot \nabla_v \varphi \big\rangle \;+\; R_N, \]
    where the remainder is the diagonal correction
    $R_N = \frac{1}{N^2} \sum_i \nabla W(0) \cdot \nabla_v \varphi(x_i, v_i)$, of size
    $|R_N| \le \frac{1}{N} \|\nabla W\|_\infty \|\nabla_v \varphi\|_\infty$. -/)
  (proof := /-- Differentiate the pairing along the trajectories and apply the chain rule
    with Newton's equations.  Completing the interaction sum $\sum_{j \ne i}$ to $\sum_j$
    produces exactly the diagonal term $\nabla W(0)$, and the stated bound follows from the
    sup-norms of $\nabla W$ and $\nabla_v \varphi$. -/)]
  Vlasov.weakEvolutionEmpiricalMeasure

attribute [blueprint "cor:empirical-vlasov"
  (title := /-- An exact weak solution -/)
  (statement := /-- Under Assumption 1 the remainder vanishes identically: $W$ even forces
    $\nabla W(0) = 0$, so the empirical measure of every Newton solution satisfies the
    distributional Vlasov equation \emph{exactly} — not merely up to an $O(1/N)$ error.
    This is the sense in which the particle system already solves the limit equation. -/)
  (proof := /-- Evenness of $W$ gives $\nabla W(0) = 0$, which kills the diagonal correction
    in the weak-evolution identity. -/)]
  Vlasov.empiricalMeasureSolvesVlasov

attribute [blueprint "def:convolve"
  (statement := /-- The convolution of a vector field $k : \mathbb{R}^d \to \mathbb{R}^d$ with a
    finite measure $\rho$: $(k * \rho)(x) := \int k(x - y)\,\mathrm{d}\rho(y)$.  The Vlasov force
    is $\nabla W * \rho_t$, with $\rho_t$ the spatial marginal of $f_t$. -/)]
  Vlasov.convolveFunctionMeasure

attribute [blueprint "def:vlasov-sol"
  (title := /-- Weak (Eulerian) solution -/)
  (statement := /-- A \emph{weak} solution of the Vlasov equation: a curve $t \mapsto f_t$ of
    measures such that for every $\varphi \in C_c^\infty(\mathbb{R}^d \times \mathbb{R}^d)$
    the map $t \mapsto \langle f_t, \varphi \rangle$ is differentiable at every
    $t \in \mathbb{R}$ with
    \[ \frac{\mathrm{d}}{\mathrm{d}t} \langle f_t, \varphi \rangle
       \;=\; \big\langle f_t,\; v \cdot \nabla_x \varphi
       - (\nabla W * \rho_t) \cdot \nabla_v \varphi \big\rangle . \]
    The predicate states exactly this identity; membership in $\mathcal{P}_1$, windows, and
    continuity in time enter as explicit hypotheses of the theorems that consume it
    (cf.\ the definition in Section 1.3 of the paper, whose prose imposes them up front). -/)]
  Vlasov.IsVlasovSolution

attribute [blueprint "def:char-flow"
  (statement := /-- A characteristic flow for the field driven by $\rho$: a map
    $\Phi = (X,V)$ solving the mean-field ODE
    \[ \dot X(t,z) = V(t,z), \qquad \dot V(t,z) = -(\nabla W * \rho_t)\big(X(t,z)\big),
       \qquad \Phi(0,z) = z, \]
    the system along which the Vlasov equation transports mass. -/)]
  Vlasov.IsCharacteristicFlow

attribute [blueprint "def:lagrangian-sol"
  (title := /-- Lagrangian solution -/)
  (statement := /-- A \emph{Lagrangian} solution is a weak solution $f$ for which there exists
    a characteristic flow $\Phi$ driven by its own marginal $\rho^f$ with
    $f_t = (\Phi_t)_\# f_0$ for every $t$ — the solution is transported by the flow it
    generates.  Every Lagrangian solution is weak by definition; the converse is the
    superposition principle (Theorem 1.7 of the paper, the final chapter). -/)]
  Vlasov.IsLagrangianVlasovSolution

/-! ## Chapter 2 — The Kantorovich–Rubinstein $W_1$ distance (OT/Wasserstein, OT/Coupling) -/

attribute [blueprint "ot:wcost" (statement := /-- The cost-generic Wasserstein functional
  $W_c(\mu,\nu) := \sup\{\int \varphi\,\mathrm{d}\mu - \int \psi\,\mathrm{d}\nu\}$ over the
  $c$-admissible dual pairs ($\varphi(x) - \psi(y) \le c(x,y)$).  The $W_1$ distance is its
  specialization to the metric ground cost $c = \mathrm{dist}$. -/)] Vlasov.wassersteinCost
attribute [blueprint "ot:wcost-self" (statement := /-- $W_c(\mu,\mu) = 0$. -/)
  (proof := /-- The diagonal pairing $\varphi=\psi$ realizes the value $0$, while any
    $c$-admissible pair gives $\int\varphi\,\mathrm{d}\mu-\int\varphi\,\mathrm{d}\mu=0$;
    hence the supremum is exactly $0$. -/)]
  Vlasov.wassersteinCost_self
attribute [blueprint "ot:wcost-comm" (statement := /-- Symmetry: $W_c(\mu,\nu) = W_c(\nu,\mu)$
  for a symmetric cost. -/)
  (proof := /-- Negating the dual functional and swapping the admissible pair
    $(\varphi,\psi)\mapsto(\psi,\varphi)$ exchanges the roles of $\mu$ and $\nu$ while
    preserving admissibility, so the two suprema coincide. -/)]
  Vlasov.wassersteinCost_comm
attribute [blueprint "ot:wcost-tri" (statement := /-- The triangle inequality for $W_c$. -/)
  (proof := /-- Given admissible pairs for $(\mu,\eta)$ and $(\eta,\nu)$, their sum is
    admissible for $(\mu,\nu)$ and the terms tested against $\eta$ telescope; taking suprema
    gives subadditivity. -/)]
  Vlasov.wassersteinCost_triangle
attribute [blueprint "ot:wcost-lip" (statement := /-- Non-expansion of $W_c$ under a
  $1$-Lipschitz pushforward: $W_c(T_\#\mu, T_\#\nu) \le W_c(\mu,\nu)$. -/)
  (proof := /-- If $T$ is $1$-Lipschitz then $\varphi\circ T$ is $c$-admissible whenever
    $\varphi$ is; substituting into the dual supremum for $T_\#\mu,T_\#\nu$ recovers the dual
    functional for $\mu,\nu$, so the value cannot increase. -/)]
  Vlasov.wassersteinCost_le_of_lipschitz_map
attribute [blueprint "ot:w1"
  (title := /-- Definition 1.4 of the paper — the Kantorovich–Rubinstein distance -/)
  (statement := /-- For probability measures $\mu, \nu$ with finite first moment,
  \[ W_1(\mu,\nu) \;:=\; \sup_{\mathrm{Lip}(\varphi) \le 1}
     \Big( \int \varphi\,\mathrm{d}\mu - \int \varphi\,\mathrm{d}\nu \Big), \]
  the \emph{dual} face of Definition 1.4 of the paper.  The \emph{primal} (coupling) face and
  the equality between them are the duality theorem closing this chapter.  Neither optimum is
  attained anywhere in the development — every bound is $\varepsilon$-optimal. -/)]
  Vlasov.wasserstein1
attribute [blueprint "ot:w1-self" (statement := /-- $W_1(\mu,\mu) = 0$. -/)
  (proof := /-- Specialize the cost-generic identity to the metric ground cost
    $c=\mathrm{dist}$. -/)] Vlasov.wasserstein1_self
attribute [blueprint "ot:w1-comm" (statement := /-- Symmetry of $W_1$. -/)
  (proof := /-- Specialize the cost-generic symmetry to the symmetric cost
    $c=\mathrm{dist}$. -/)] Vlasov.wasserstein1_comm
attribute [blueprint "ot:w1-tri" (statement := /-- The triangle inequality for $W_1$. -/)
  (proof := /-- Specialize the cost-generic triangle inequality to $c=\mathrm{dist}$. -/)]
  Vlasov.wasserstein1_triangle
attribute [blueprint "ot:w1-lip" (statement := /-- Non-expansion of $W_1$ under a $1$-Lipschitz
  pushforward — the workhorse estimate for transporting mass along flows. -/)
  (proof := /-- Specialize the cost-generic non-expansion: a $1$-Lipschitz test composed with a
    $1$-Lipschitz map is again $1$-Lipschitz. -/)]
  Vlasov.wasserstein1_le_of_lipschitz_map
attribute [blueprint "ot:w1-fin" (statement := /-- Finiteness: if $\mu$ and $\nu$ have finite
  first moment then $W_1(\mu,\nu) < \infty$. -/)
  (proof := /-- A $1$-Lipschitz test normalized by $\varphi(0)=0$ obeys
    $|\varphi(x)|\le\|x\|$, so the dual functional is bounded by
    $\int\|x\|\,\mathrm{d}\mu+\int\|x\|\,\mathrm{d}\nu$. -/)]
  Vlasov.wasserstein1_lt_top_of_finite_moment
attribute [blueprint "ot:coupling" (statement := /-- A coupling $\pi$ of $\mu$ and $\nu$:
  a probability measure on the product space whose marginals are $\mu$ and $\nu$.  The set of
  couplings is the domain of the primal face of $W_1$. -/)] Vlasov.IsCoupling
attribute [blueprint "ot:wcost-coupling" (statement := /-- The Monge–Kantorovich (primal)
  cost: $\inf_\pi \int \mathrm{dist}\,\mathrm{d}\pi$ over couplings $\pi$ of $\mu$ and
  $\nu$. -/)] Vlasov.wassersteinCost_coupling
attribute [blueprint "ot:w1-coupling" (statement := /-- $W_1$ expressed via the infimum over
  couplings — the primal face of Definition 1.4. -/)] Vlasov.wasserstein1_coupling
attribute [blueprint "ot:w1-le-coupling" (statement := /-- The easy direction of duality:
  the dual value is at most any coupling cost. -/)
  (proof := /-- For any coupling $\pi$ and $1$-Lipschitz $\varphi$,
    $\int\varphi\,\mathrm{d}\mu-\int\varphi\,\mathrm{d}\nu
    =\int(\varphi(x)-\varphi(y))\,\mathrm{d}\pi\le\int\mathrm{dist}(x,y)\,\mathrm{d}\pi$;
    take the supremum over $\varphi$ and the infimum over $\pi$. -/)]
  Vlasov.wasserstein1_le_wasserstein1_coupling
attribute [blueprint "ot:coupling-le-dual" (statement := /-- The hard direction of duality:
  the optimal coupling cost is at most the dual value. -/)
  (proof := /-- By reduction to finite transport problems: restrict to finite-range
    approximations, exhibit an $\varepsilon$-optimal coupling for each finite problem via
    cone-separation (the hyperplane separation theorem, Farkas duality), and transfer the
    bound to arbitrary marginals by a disintegration and triangle argument.  No compactness
    of the ambient space is used, and no optimum is ever attained. -/)]
  Vlasov.wassersteinCost_coupling_le_dual
attribute [blueprint "ot:w1-eq-coupling"
  (title := /-- Kantorovich–Rubinstein duality -/)
  (statement := /-- At the metric ground cost, for probability measures with finite first
    moment on a Polish-type space, the dual and primal faces agree:
    $W_1(\mu,\nu) = \inf_\pi \int \mathrm{dist}\,\mathrm{d}\pi$.  This is the bridge on which
    the Dobrushin argument crosses between the two faces of Definition 1.4. -/)
  (proof := /-- Combine the easy inequality (dual $\le$ any coupling cost) with the hard
    inequality (optimal coupling cost $\le$ dual); equality is Kantorovich–Rubinstein
    duality. -/)] Vlasov.wasserstein1_eq_coupling

/-! ## Chapter 3 — The characteristic flow and well-posedness (CharacteristicFlow.lean) -/

attribute [blueprint "def:vlasov-field"
  (statement := /-- The phase-space velocity field
    $b(t,x,v) = \big(v,\; -(\nabla W * \rho_t)(x)\big)$ generating the characteristic flow.
    Under Assumption 1 it is Lipschitz in the phase variable, with constant governed by
    $\max(1, L)$. -/)]
  Vlasov.vlasovVectorField

attribute [blueprint "def:vlasov-sol-on"
  (statement := /-- The window-localized weak-solution predicate: the distributional Vlasov
    equation holds on the open interval $(0,T)$.  The predicate carries only the PDE;
    continuity in time, where needed, is a separate hypothesis (as in Theorem 1.7 of the
    paper).  Local existence lives on windows; the global theorem glues them. -/)]
  Vlasov.IsVlasovSolutionOn

attribute [blueprint "def:lagrangian-sol-on"
  (statement := /-- The window-localized Lagrangian-solution predicate on $[0,T]$: a weak
    solution on the window together with a characteristic-flow witness transporting the
    initial datum. -/)]
  Vlasov.IsLagrangianVlasovSolutionOn

attribute [blueprint "thm:vlasov-wp"
  (title := /-- Global well-posedness — Theorem 1.3 of the paper -/)
  (statement := /-- Let $W$ satisfy Assumption 1 and let $f_0$ be a probability measure with
    finite first moment.  The forward Cauchy problem is well-posed: there exists a
    \emph{single} curve $f : [0,\infty) \to \mathcal{P}_1(\mathbb{R}^d \times \mathbb{R}^d)$
    with datum $f(0) = f_0$ and finite first moment at every $t \ge 0$, which is a Lagrangian
    solution on every window $[0,T]$; and on each window it is the \emph{unique} Lagrangian
    solution with that datum. -/)
  (proof := /-- Freeze the field and run Picard iteration on curves of measures: on a short
    window the solution map is a contraction in the $W_1$-sup metric, with ratio controlled by
    $L \cdot T$, so Banach's fixed-point theorem yields a unique local Lagrangian solution.
    Windows of a fixed length depending only on $L$ are then glued to reach arbitrary
    horizons — no smallness of $L$ is required.  Per-window uniqueness follows from the
    stability estimate of the next chapter for $L > 0$, and is explicit in the degenerate
    constant-force case $L = 0$. -/)]
  Vlasov.vlasovWellPosedness

/-! ## Chapter 4 — Dobrushin stability and the mean-field limit -/

attribute [blueprint "thm:dobrushin"
  (title := /-- Dobrushin stability (1979) — Theorem 1.5 of the paper -/)
  (statement := /-- Let $W$ satisfy Assumption 1.  Any two Lagrangian solutions $f, g$ with
    finite first moment at every time are stable in $W_1$ at an exponential rate:
    \[ W_1(f_t, g_t) \;\le\; e^{C t}\, W_1(f_0, g_0), \qquad t \ge 0, \]
    with the explicit rate $C = 2\max(1, L)$. -/)
  (proof := /-- Dobrushin's own coupling argument, followed piece for piece.  Couple the data
    $\varepsilon$-optimally and push the coupling forward along the pair of characteristic
    flows; the force difference at coupled points is bounded by the coupling cost (the
    force-versus-metric estimate), the mild integral form of the trajectories turns this into
    a Gronwall inequality for the transported cost, and integrating gives the exponential
    estimate.  Kantorovich–Rubinstein duality converts between the coupling cost and the
    $W_1$ distance at both ends. -/)]
  Vlasov.dobrushin

attribute [blueprint "def:dobrushin-estimate"
  (statement := /-- The stability estimate packaged as a reusable predicate on a pair of
    measure curves: $W_1(f_t, g_t) \le e^{Ct}\, W_1(f_0, g_0)$ for all $t \ge 0$. -/)]
  Vlasov.DobrushinStabilityEstimate

attribute [blueprint "cor:mean-field-limit"
  (title := /-- Mean-field limit — Corollary 1.6 of the paper -/)
  (statement := /-- Let $f$ be the Vlasov solution with datum $f_0$ and let $\mu^N_t$ be the
    empirical measures of $N$ particles evolving by Newton's equations.  Assume the Dobrushin
    estimate holds for every pair $(\mu^N, f)$ with one constant $C$ — Theorem 1.5 supplies
    it, each empirical curve being a Lagrangian solution with the rate uniform in $N$, and the
    Lean takes it as an explicit hypothesis rather than re-deriving it.  If the initial
    empirical measures converge, $W_1(\mu^N_0, f_0) \to 0$, then for every $T > 0$
    \[ \sup_{t \in [0,T]} W_1(\mu^N_t, f_t) \;\longrightarrow\; 0
       \qquad (N \to \infty). \]
    Propagation of chaos for the Vlasov equation, in its quantitative $W_1$ form. -/)
  (proof := /-- For each $N$ the stability estimate lifts to the window supremum,
    $\sup_{t \le T} W_1(\mu^N_t, f_t) \le e^{CT}\, W_1(\mu^N_0, f_0)$, and the right-hand
    side tends to $0$ by the assumed initial convergence. -/)]
  Vlasov.meanFieldLimit

/-! ## Chapter 5 — The superposition principle: weak ⟹ Lagrangian (WeakToLagrangian.lean) -/

attribute [blueprint "ass:W2"
  (title := /-- Assumption 2 of the paper ($\mathrm{AssW2}$) -/)
  (statement := /-- In addition to Assumption 1, let $\nabla W \in C^1$ (equivalently
    $W \in C^2$).  One degree of regularity beyond Assumption 1, spent to make the phase-space
    field $C^1$ in space — exactly what the variational equation for the flow's derivative in
    its initial point requires.  Only the superposition principle carries this assumption. -/)]
  Vlasov.AssW2

attribute [blueprint "def:fundamental-matrix"
  (statement := /-- The canonical Dyson-series solution $M(t)$ of the matrix variational
    equation $\dot M = A(s)\,M$, $M(0) = I$, continuous jointly in time and the parameter.
    It provides the candidate derivative of the flow with respect to its initial point —
    constructed explicitly rather than chosen, so that its regularity in the parameter is
    provable. -/)]
  Vlasov.fundamentalMatrix

attribute [blueprint "thm:charflow-fderiv-fundamental"
  (statement := /-- The flow's Fréchet derivative in its initial point is the Dyson-series
    fundamental matrix $M(t)$ evaluated along the trajectory. -/)
  (proof := /-- Both the trajectory difference $u_h(s)=\Phi_s(z+h)-\Phi_s(z)$ and its
    linearization $M(s)h$ solve the linear ODE $\dot w=A(s)w$ up to the first-order Taylor
    remainder of the field, which is $o(\|h\|)$ uniformly over the compact flow image; a
    Gronwall estimate on approximate trajectories bounds their gap, giving
    $\Phi_t(z+h)-\Phi_t(z)-M(t)h=o(\|h\|)$. -/)]
  Vlasov.charFlow_hasFDerivAt_of_fundamentalMatrix

attribute [blueprint "thm:variational-eq"
  (title := /-- The variational equation -/)
  (statement := /-- The map $z \mapsto \Phi_t(z)$ is Fréchet differentiable in the initial
    point, with derivative solving the linearized (variational) equation
    $\dot M = (D_z b)\,M$, $M(0)=I$, and depending continuously on $z$.  The research-grade
    core of the bridge. -/)
  (proof := /-- Construct the fundamental matrix explicitly as a Dyson series and prove its
    joint $(t,z)$-continuity by a parameter Weierstrass $M$-test; the difference-quotient
    Gronwall bound then identifies $M(t)$ as the Fréchet derivative of $z\mapsto\Phi_t(z)$. -/)]
  Vlasov.charFlow_hasFDerivAt_in_initialPoint

attribute [blueprint "thm:charflow-inverse-joint"
  (statement := /-- The two-time flow $(s,z) \mapsto \Phi_{s \to t}(z)$ and its inverse are
    jointly $C^1$ on the window — the jointly-smooth change of variables used to transport
    test functions along characteristics. -/)
  (proof := /-- A lower Gronwall bound makes $\Phi_t$ antilipschitz, hence injective with
    closed range; the inverse function theorem gives open range, so by connectedness $\Phi_t$
    is a $C^1$ diffeomorphism.  Applying the inverse function theorem to the space-time chart
    $(s,z)\mapsto(s,\Phi_s z)$ — block-triangular, invertible derivative — makes the inverse
    jointly $C^1$, hence so is $\Phi_{s\to t}=\Phi_t\circ\Phi_s^{-1}$. -/)]
  Vlasov.charFlow_inverse_contDiffOn_joint

attribute [blueprint "thm:test-c1c"
  (title := /-- Test-class enlargement -/)
  (statement := /-- The weak-solution test class is enlarged from $C_c^\infty$ to $C^1_c$.
    Needed because the transported test $\psi_s = \varphi \circ \Phi_{s \to t}$ is only
    $C^1_c$ — the flow is once, not infinitely, differentiable in space. -/)
  (proof := /-- Mollify the $C^1_c$ test $\chi$ by a shrinking smooth bump,
    $\chi_n=\rho_n\star\chi$, and apply the $C^\infty_c$ weak equation to each.  Pass to the
    limit using $\chi_n\to\chi$ and the \emph{uniform} convergence $\nabla\chi_n\to\nabla\chi$
    (the analytic core of the step), the field bound providing a uniform dominating
    function. -/)]
  Vlasov.weakEvolution_test_C1c_On

attribute [blueprint "thm:transport-identity"
  (statement := /-- The dual transport identity: the transported test
    $\psi_s = \varphi \circ \Phi_{s \to t}$ satisfies
    $\partial_s \psi_s + D\psi_s \cdot b_s = 0$ along the flow — the dual of the pushforward
    chain rule. -/)
  (proof := /-- Set $z_0=\Psi_s w$, so $w=\Phi_s z_0$.  Then
    $\psi_{s'}(\Phi_{s'}z_0)=\varphi(\Phi_t z_0)$ is constant in $s'$; differentiating this
    composite at $s'=s$ and splitting by the chain rule gives
    $\partial_s\psi_s(w)+(D\psi_s(w))\,b_s(w)=0$. -/)]
  Vlasov.transportedTest_transport_identity

attribute [blueprint "thm:diagonal-chain-rule"
  (title := /-- The diagonal chain rule -/)
  (statement := /-- $\dfrac{\mathrm{d}}{\mathrm{d}s} \int \psi_s\,\mathrm{d}f_s = 0$ for
    $s \in (0,T)$: differentiating through both the moving test function and the moving
    measure, the transport identity and the weak PDE cancel exactly. -/)
  (proof := /-- Split $I(\sigma)=\int\psi_\sigma\,\mathrm{d}f_\sigma=B(\sigma)+q(\sigma)$,
    with $B$ the fixed-integrand part — its derivative $V_b$ supplied by the weak equation on
    the enlarged $C^1_c$ test class — and $q(\sigma)=\int(\psi_\sigma-\psi_s)\,\mathrm{d}f_\sigma$.
    A little-$o$ argument gives $q'(s)=-V_b$: the remainder splits into a
    uniform-differentiability term (Heine–Cantor over the fixed compact carrying the moving
    supports) and a narrow-continuity term.  The transport identity forces
    $V_b=-\int\partial_s\psi_s\,\mathrm{d}f_s$, so the two contributions cancel and
    $I'(s)=0$. -/)]
  Vlasov.transportedIntegral_hasDerivAt_zero

attribute [blueprint "thm:dual-core"
  (title := /-- The dual core -/)
  (statement := /-- $\int \varphi\,\mathrm{d}f_T = \int \varphi\,\mathrm{d}g_T$ for every
    $C_c^\infty$ test function $\varphi$, where $g = (\Phi)_\# f_0$ is the pushforward of the
    initial datum along the frozen-field flow.  Hence $f_T = g_T$ by measure
    extensionality. -/)
  (proof := /-- By the diagonal chain rule the map $s\mapsto\int\psi_s\,\mathrm{d}f_s$ has
    zero derivative on $(0,T)$, hence is constant.  Evaluating at the endpoints —
    $\psi_T=\varphi$ and $\psi_0=\varphi\circ\Phi_T$ — gives
    $\int\varphi\,\mathrm{d}f_T=\int\varphi\circ\Phi_T\,\mathrm{d}f_0
    =\int\varphi\,\mathrm{d}g_T$.  Ranging over $\varphi\in C_c^\infty$ and measure
    extensionality give $f_T=g_T$. -/)]
  Vlasov.weak_eq_frozenField_pushforward_dualCore

attribute [blueprint "thm:weak-lagrangian"
  (title := /-- The superposition principle — Theorem 1.7 of the paper -/)
  (statement := /-- Let $W$ satisfy Assumption 2 and let $T > 0$ satisfy $L\,T^2 < 1$.  Every
    weak solution on $[0,T]$ whose first moments are uniformly bounded on the window and whose
    force field is regular — $(\nabla W * \rho_t)(x)$ continuous in $t$ for each $x$, with
    jointly continuous spatial derivative — is Lagrangian on $[0,T]$: it coincides with the
    pushforward of its initial datum along the characteristic flow it generates.  Weak
    solutions cannot branch away from the Lagrangian one on the window. -/)
  (proof := /-- Freeze the field at $\rho^f$ and build its characteristic flow $\Phi$; the
    pushforward $g=(\Phi_t)_\#f_0$ is Lagrangian by construction and solves the same frozen
    linear equation.  The dual core shows $f_T=g_T$ for every window endpoint, so $f$
    coincides with its own characteristic pushforward and is therefore Lagrangian. -/)]
  Vlasov.weak_isLagrangianVlasovSolutionOn

#show_blueprint

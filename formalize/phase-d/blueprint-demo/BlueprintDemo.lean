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

The node set follows `formalize/codebase-outline.md` (the "Mathematical ↔ Lean
correspondence" table): assumptions, the Vlasov / characteristic-flow predicates, the marquee
well-posedness + Dobrushin results, the optimal-transport core (W₁ via KR duality, couplings,
triangle, finiteness), and the weak ⟹ Lagrangian bridge (the superposition principle).
-/

open Vlasov

/-! ## §1 Standing assumptions and basic objects (Basic.lean) -/

attribute [blueprint "ass:W"
  (title := /-- Standing assumption $\mathrm{AssW}$ -/)
  (statement := /-- The interaction potential $W : \mathbb{R}^d \to \mathbb{R}$ is in
    $C^{1,1}$: continuously differentiable, even ($W(-x) = W(x)$), with globally Lipschitz
    gradient $\nabla W$ (Lipschitz constant $L := \mathrm{Lip}(\nabla W) < \infty$). -/)]
  Vlasov.AssW

attribute [blueprint "ass:W2"
  (title := /-- Strengthened assumption $\mathrm{AssW2}$ -/)
  (statement := /-- $\mathrm{AssW}$ together with $\nabla W \in C^1$ (so $W \in C^2$, Hessian
    bounded).  This is what makes the phase-space field $C^1$ in space, which the variational
    equation for the flow's dependence on its initial point requires.  Only the
    weak $\Rightarrow$ Lagrangian bridge carries $\mathrm{AssW2}$. -/)]
  Vlasov.AssW2

attribute [blueprint "def:convolve"
  (statement := /-- The convolution of a vector field $k : \mathbb{R}^d \to \mathbb{R}^d$ with a
    finite measure $\rho$: $(k * \rho)(x) := \int k(x - y)\,\mathrm{d}\rho(y)$.  The Vlasov force
    is $\nabla W * \rho_t$. -/)]
  Vlasov.convolveFunctionMeasure

attribute [blueprint "def:char-flow"
  (statement := /-- A characteristic flow $\Phi$ for the field driven by $\rho$:
    $\dot X = V$, $\dot V = -(\nabla W * \rho_t)(X)$, the mean-field ODE along which mass is
    transported. -/)]
  Vlasov.IsCharacteristicFlow

attribute [blueprint "def:vlasov-sol"
  (statement := /-- A weak (Eulerian) Vlasov solution: a narrowly continuous curve of
    probability measures $f_t$ satisfying the distributional PDE
    $\partial_t f + v \cdot \nabla_x f - (\nabla W * \rho_t) \cdot \nabla_v f = 0$
    tested against $C_c^\infty$ functions. -/)]
  Vlasov.IsVlasovSolution

attribute [blueprint "def:lagrangian-sol"
  (statement := /-- A Lagrangian Vlasov solution: a weak solution that admits a characteristic
    flow representation, i.e. $f_t = (\Phi_t)_\# f_0$ for a flow $\Phi$ driven by $\rho^f$. -/)]
  Vlasov.IsLagrangianVlasovSolution

/-! ## §2 Optimal-transport core: the $W_1$ Kantorovich–Rubinstein distance -/

attribute [blueprint "ot:wcost" (statement := /-- The cost-generic Wasserstein functional
  $W_c(\mu,\nu) := \sup\{\int \varphi\,\mathrm{d}\mu - \int \psi\,\mathrm{d}\nu\}$ over the
  $c$-admissible dual pairs. -/)] Vlasov.wassersteinCost
attribute [blueprint "ot:wcost-self" (statement := /-- $W_c(\mu,\mu) = 0$. -/)
  (proof := /-- The diagonal pairing $\varphi=\psi$ realizes the value $0$, while any $c$-admissible pair gives $\int\varphi\,\mathrm{d}\mu-\int\varphi\,\mathrm{d}\mu=0$; hence the supremum is exactly $0$. -/)]
  Vlasov.wassersteinCost_self
attribute [blueprint "ot:wcost-comm" (statement := /-- Symmetry: $W_c(\mu,\nu) = W_c(\nu,\mu)$. -/)
  (proof := /-- Negating the dual functional and swapping the admissible pair $(\varphi,\psi)\mapsto(\psi,\varphi)$ exchanges the roles of $\mu$ and $\nu$ while preserving admissibility, so the two suprema coincide. -/)]
  Vlasov.wassersteinCost_comm
attribute [blueprint "ot:wcost-tri" (statement := /-- Triangle inequality for $W_c$. -/)
  (proof := /-- Given admissible pairs for $(\mu,\eta)$ and $(\eta,\nu)$, their sum is admissible for $(\mu,\nu)$ and the terms tested against $\eta$ telescope; taking suprema gives subadditivity. -/)]
  Vlasov.wassersteinCost_triangle
attribute [blueprint "ot:wcost-lip" (statement := /-- Non-expansion of $W_c$ under a
  $1$-Lipschitz pushforward. -/)
  (proof := /-- If $T$ is $1$-Lipschitz then $\varphi\circ T$ is $c$-admissible whenever $\varphi$ is; substituting into the dual sup for $T_\#\mu,T_\#\nu$ recovers the dual functional for $\mu,\nu$, so the value cannot increase. -/)] Vlasov.wassersteinCost_le_of_lipschitz_map
attribute [blueprint "ot:w1" (statement := /-- The Kantorovich–Rubinstein $W_1$ distance,
  defined via the dual sup-formula
  $W_1(\mu,\nu) = \sup\{\int \varphi\,\mathrm{d}\mu - \int \varphi\,\mathrm{d}\nu : \mathrm{Lip}(\varphi) \le 1\}$. -/)]
  Vlasov.wasserstein1
attribute [blueprint "ot:w1-self" (statement := /-- $W_1(\mu,\mu) = 0$. -/)
  (proof := /-- Specialize the cost-generic identity to the metric ground cost $c=\mathrm{dist}$. -/)] Vlasov.wasserstein1_self
attribute [blueprint "ot:w1-comm" (statement := /-- Symmetry of $W_1$. -/)
  (proof := /-- Specialize the cost-generic symmetry to the symmetric cost $c=\mathrm{dist}$. -/)] Vlasov.wasserstein1_comm
attribute [blueprint "ot:w1-tri" (statement := /-- Triangle inequality for $W_1$. -/)
  (proof := /-- Specialize the cost-generic triangle inequality to $c=\mathrm{dist}$. -/)]
  Vlasov.wasserstein1_triangle
attribute [blueprint "ot:w1-lip" (statement := /-- $W_1$ non-expansion under a $1$-Lipschitz
  pushforward (the easy KR direction at the metric level). -/)
  (proof := /-- Specialize the cost-generic non-expansion: a $1$-Lipschitz test composed with a $1$-Lipschitz map is again $1$-Lipschitz. -/)]
  Vlasov.wasserstein1_le_of_lipschitz_map
attribute [blueprint "ot:w1-fin" (statement := /-- Finiteness: a measure with finite first
  moment has $W_1(\mu,\nu) < \infty$. -/)
  (proof := /-- A $1$-Lipschitz test normalized by $\varphi(0)=0$ obeys $|\varphi(x)|\le\|x\|$, so the dual functional is bounded by $\int\|x\|\,\mathrm{d}\mu+\int\|x\|\,\mathrm{d}\nu$; finiteness of the first moments bounds $W_1$. -/)] Vlasov.wasserstein1_lt_top_of_finite_moment
attribute [blueprint "ot:coupling" (statement := /-- A coupling $\pi$ of $\mu$ and $\nu$:
  a measure on the product with the correct marginals. -/)] Vlasov.IsCoupling
attribute [blueprint "ot:wcost-coupling" (statement := /-- The Monge–Kantorovich (coupling)
  cost $\int \mathrm{dist}\,\mathrm{d}\pi$ over couplings $\pi$. -/)] Vlasov.wassersteinCost_coupling
attribute [blueprint "ot:w1-coupling" (statement := /-- $W_1$ expressed via the infimum over
  couplings. -/)] Vlasov.wasserstein1_coupling
attribute [blueprint "ot:w1-le-coupling" (statement := /-- Dual $\le$ coupling: the KR-dual
  $W_1$ is at most any coupling cost. -/)
  (proof := /-- For any coupling $\pi$ and $1$-Lipschitz $\varphi$, $\int\varphi\,\mathrm{d}\mu-\int\varphi\,\mathrm{d}\nu=\int(\varphi(x)-\varphi(y))\,\mathrm{d}\pi\le\int\mathrm{dist}(x,y)\,\mathrm{d}\pi$; sup over $\varphi$ and inf over $\pi$ give the easy KR inequality. -/)] Vlasov.wasserstein1_le_wasserstein1_coupling
attribute [blueprint "ot:coupling-le-dual" (statement := /-- The hard KR direction: the optimal
  coupling cost is at most the dual value. -/)
  (proof := /-- The hard direction of Kantorovich--Rubinstein duality: the optimal coupling cost is bounded by the dual value, via a minimax / Hahn--Banach separation argument exhibiting a coupling whose cost matches the dual supremum. -/)] Vlasov.wassersteinCost_coupling_le_dual
attribute [blueprint "ot:w1-eq-coupling" (statement := /-- Kantorovich–Rubinstein duality:
  $W_1$ equals the optimal coupling cost (both directions unified). -/)
  (proof := /-- Combine the easy inequality (dual $\le$ coupling) (dual $\le$ coupling) with the hard inequality (coupling $\le$ dual) (coupling $\le$ dual); equality is Kantorovich--Rubinstein duality. -/)] Vlasov.wasserstein1_eq_coupling

/-! ## §3 Localized predicates and the characteristic vector field (CharacteristicFlow.lean) -/

attribute [blueprint "def:vlasov-field"
  (statement := /-- The phase-space velocity field $b(t,x,v) = (v,\,-(\nabla W * \rho_t)(x))$
    generating the characteristic flow. -/)]
  Vlasov.vlasovVectorField

attribute [blueprint "def:vlasov-sol-on"
  (statement := /-- The window-localized weak Vlasov solution predicate on $[0,T]$: the
    distributional PDE holds on the open time interval, with narrow continuity up to the
    boundary. -/)]
  Vlasov.IsVlasovSolutionOn

attribute [blueprint "def:lagrangian-sol-on"
  (statement := /-- The window-localized Lagrangian solution predicate on $[0,T]$: a weak
    solution on the window together with a characteristic-flow witness. -/)]
  Vlasov.IsLagrangianVlasovSolutionOn

/-! ## §4 Marquee results: well-posedness and Dobrushin (CharacteristicFlow.lean) -/

attribute [blueprint "thm:vlasov-wp"
  (title := /-- Vlasov well-posedness -/)
  (statement := /-- \textbf{Forward well-posedness.}  Under $\mathrm{AssW}$, for any
    finite-first-moment probability datum $f_0$ there exists a unique forward-in-time Lagrangian
    Vlasov solution with initial datum $f_0$.  Existence is by Banach fixed point on the
    $W_1$-sup metric (Picard iteration), extended to arbitrary $T$ by window gluing; uniqueness is
    per-window.  Axiom-clean: $[\mathtt{propext}, \mathtt{Classical.choice}, \mathtt{Quot.sound}]$. -/)
  (proof := /-- Freeze the field and run Picard iteration on the curve of measures: on a short window the solution map is a contraction in the $W_1$-sup metric (ratio controlled by $\mathrm{Lip}(\nabla W)\cdot T$), so Banach's fixed-point theorem yields a unique local Lagrangian solution.  Arbitrary horizons follow by gluing windows; uniqueness is per-window from the same contraction. -/)]
  Vlasov.vlasovWellPosedness

attribute [blueprint "thm:dobrushin"
  (title := /-- Dobrushin stability (1979) -/)
  (statement := /-- \textbf{Dobrushin's theorem.}  Under $\mathrm{AssW}$, any two Lagrangian
    Vlasov solutions obey the exponential $W_1$-stability estimate
    $W_1(f_t, g_t) \le e^{Ct}\, W_1(f_0, g_0)$ for all $t \ge 0$, where $C$ depends on
    $\mathrm{Lip}(\nabla W)$.  Proved via the optimal-coupling Gronwall argument.  Axiom-clean. -/)
  (proof := /-- Couple the two solutions optimally at each time.  The coupling cost obeys the Gronwall inequality $\tfrac{\mathrm{d}}{\mathrm{d}t}W_1(f_t,g_t)\le C\,W_1(f_t,g_t)$, with $C$ governed by $\mathrm{Lip}(\nabla W)$; integrating gives the exponential estimate. -/)]
  Vlasov.dobrushin

/-! ## §5 The weak ⟹ Lagrangian bridge (the superposition principle, WeakToLagrangian.lean)

This is the project's newest highlight.  Under the strengthened $\mathrm{AssW2}$ assumption,
every weak solution is in fact Lagrangian.  The argument freezes the field at $\rho^f$, builds the
variational (fundamental-matrix) equation for the $C^1$ dependence of the flow on its initial point,
enlarges the test class to $C^1_c$, and runs a diagonal chain-rule / dual-transport argument. -/

attribute [blueprint "def:fundamental-matrix"
  (statement := /-- The canonical Dyson-series solution $M(t)$ of the matrix variational equation
    $\dot M = A(s)\,M$, $M(0) = I$; continuous in both time and the parameter, providing the
    derivative of the flow with respect to its initial point. -/)]
  Vlasov.fundamentalMatrix

attribute [blueprint "thm:charflow-fderiv-fundamental"
  (statement := /-- The flow's Fréchet derivative in its initial point is assembled from the
    Dyson-series fundamental matrix $M(t)$. -/)
  (proof := /-- Both the trajectory difference $u_h(s)=\Phi_s(z+h)-\Phi_s(z)$ and its linearization $M(s)h$ solve the linear ODE $\dot w=A(s)w$ with the same initial value $h$; a Gronwall estimate on approximate trajectories bounds their gap by the first-order Taylor remainder of $b$, which is $o(\|h\|)$ uniformly over the compact flow image.  Hence $\Phi_t(z+h)-\Phi_t(z)-M(t)h=o(\|h\|)$. -/)]
  Vlasov.charFlow_hasFDerivAt_of_fundamentalMatrix

attribute [blueprint "thm:variational-eq"
  (title := /-- Variational equation (\#3) -/)
  (statement := /-- \textbf{Variational equation.}  The map $z \mapsto \Phi_t(z)$ is Fréchet
    differentiable in the initial point $z$, with derivative solving the linearized equation
    $\dot M = (D_z b)\,M$.  The research-grade core of the bridge, closed via a Gronwall
    difference-quotient estimate. -/)
  (proof := /-- Construct $M$ as the Dyson series the fundamental matrix $M$ and prove its joint $(t,z)$-continuity by a parameter Weierstrass $M$-test; the difference-quotient bound the difference-quotient Gronwall bound then identifies $M(t)$ as the Fréchet derivative of $z\mapsto\Phi_t(z)$, depending continuously on $z$. -/)]
  Vlasov.charFlow_hasFDerivAt_in_initialPoint

attribute [blueprint "thm:charflow-inverse-joint"
  (statement := /-- The two-time flow $(s,z) \mapsto \Phi_{s \to t}(z)$ and its inverse are
    jointly $C^1$ on the window, supplying the jointly-smooth inverse map used to transport
    test functions. -/)
  (proof := /-- A lower Gronwall bound makes $\Phi_t$ antilipschitz, hence injective with closed range; the inverse function theorem gives open range, so by connectedness $\Phi_t$ is a $C^1$ diffeomorphism.  Applying the IFT to the space-time chart $(s,z)\mapsto(s,\Phi_s z)$ (block-triangular, invertible derivative) makes the inverse jointly $C^1$, hence so is $\Phi_{s\to t}=\Phi_t\circ\Phi_s^{-1}$. -/)]
  Vlasov.charFlow_inverse_contDiffOn_joint

attribute [blueprint "thm:test-c1c"
  (title := /-- Test-class enlargement (\#4) -/)
  (statement := /-- The weak-solution test class is enlarged from $C_c^\infty$ to $C^1_c$ by
    mollification and a uniform dominated-convergence argument.  Needed because the transported
    test $\psi_s = \varphi \circ \Phi_{s \to t}$ is only $C^1_c$. -/)
  (proof := /-- Mollify the $C^1_c$ test $\chi$ by a shrinking $C^\infty$ bump $\chi_n=\rho_n\star\chi$ and apply the $C^\infty_c$ weak equation to each.  Pass to the limit using $\chi_n\to\chi$ and the \emph{uniform} convergence $\nabla\chi_n\to\nabla\chi$ (the analytic core), with the field bound providing a uniform dominating function. -/)]
  Vlasov.weakEvolution_test_C1c_On

attribute [blueprint "thm:transport-identity"
  (statement := /-- The dual transport identity: the transported test satisfies
    $\partial_s \psi_s + D\psi_s \cdot b_s = 0$ along the flow. -/)
  (proof := /-- Set $z_0=\Psi_s w$, so $w=\Phi_s z_0$.  Then $\psi_{s'}(\Phi_{s'}z_0)=\varphi(\Phi_t z_0)$ is constant in $s'$; differentiating this composite at $s'=s$ and applying the chain rule splits as $\partial_s\psi_s(w)+(D\psi_s(w))\,b_s(w)=0$.  This is the dual of the pushforward chain rule. -/)]
  Vlasov.transportedTest_transport_identity

attribute [blueprint "thm:diagonal-chain-rule"
  (title := /-- Diagonal chain rule (\#6a) -/)
  (statement := /-- The diagonal chain rule: $\frac{\mathrm{d}}{\mathrm{d}s} \int \psi_s\,\mathrm{d}f_s = 0$
    for $s \in (0,T)$, combining the transport identity with the weak PDE on the enlarged $C^1_c$
    test class. -/)
  (proof := /-- Split $I(\sigma)=\int\psi_\sigma\,\mathrm{d}f_\sigma=B(\sigma)+q(\sigma)$ with $B$ the fixed-integrand part (derivative $V_b$ from the $C^1_c$ weak equation the $C^1_c$-extended weak equation) and $q(\sigma)=\int(\psi_\sigma-\psi_s)\,\mathrm{d}f_\sigma$.  A little-o argument gives $q'(s)=-V_b$: the remainder splits into a uniform-differentiability term (Heine--Cantor over the fixed compact carrying the moving supports) and a narrow-continuity term.  The transport identity the transport identity forces $V_b=-\int\partial_s\psi_s\,\mathrm{d}f_s$, so the two cancel and $I'(s)=0$. -/)]
  Vlasov.transportedIntegral_hasDerivAt_zero

attribute [blueprint "thm:dual-core"
  (title := /-- Dual core -/)
  (statement := /-- The dual core: $\int \varphi\,\mathrm{d}f_T = \int \varphi\,\mathrm{d}g_T$ for
    all $C_c^\infty$ test functions $\varphi$, where $g = (\Phi)_\# f_0$ is the frozen-field
    pushforward.  Hence $f_T = g_T$ by measure extensionality. -/)
  (proof := /-- By the diagonal chain rule the map $s\mapsto\int\psi_s\,\mathrm{d}f_s$ has zero derivative on $(0,T)$, hence is constant.  Evaluating at the endpoints ($\psi_t=\varphi$, $\psi_0=\varphi\circ\Phi_t$) gives $\int\varphi\,\mathrm{d}f_T=\int\varphi\circ\Phi_t\,\mathrm{d}f_0=\int\varphi\,\mathrm{d}g_T$ for the pushforward $g=(\Phi_t)_\#f_0$.  Ranging over $\varphi\in C_c^\infty$ and measure extensionality give $f_T=g_T$. -/)]
  Vlasov.weak_eq_frozenField_pushforward_dualCore

attribute [blueprint "thm:weak-lagrangian"
  (title := /-- Superposition principle -/)
  (statement := /-- \textbf{Weak $\Rightarrow$ Lagrangian.}  Under $\mathrm{AssW2}$, every weak
    Vlasov solution on a window is Lagrangian: it coincides with the pushforward of its initial
    datum along the characteristic flow it generates.  The apex of the bridge. -/)
  (proof := /-- Freeze the field at $\rho^f$ and build its characteristic flow $\Phi$; the pushforward $g=(\Phi_t)_\#f_0$ is Lagrangian by construction and solves the same frozen linear equation.  The dual core the dual core shows $f_T=g_T$, so $f$ coincides with its own characteristic pushforward and is therefore Lagrangian. -/)]
  Vlasov.weak_isLagrangianVlasovSolutionOn

#show_blueprint

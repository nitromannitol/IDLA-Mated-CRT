import MatedCRT.FirstPass.Derived.TargetLawRotation
import MatedCRT.FirstPass.Derived.TemplateEventCompactOpen
import LatticeProb.Prob.PortmanteauOpenIntegral

/-!
# The robust disconnection event for paths converging weakly to an isotropic Brownian motion

Condition 3 of Lemma 3.14 of Gwynne-Miller-Sheffield, *An invariance principle for ergodic scale-free
random environments* (arXiv:1807.07515, p. 44), asks that the rescaled walk disconnect a small disc
around its starting point from `∞` before leaving a square, with conditional probability close to `1`.
Its continuum input is that "a Brownian motion started from `0` has probability tending to `1` as
`δ → 0` to disconnect `B_δ(0)` from `∞` before leaving `B_1(0)`", realised here by the robust template
disconnection event `E_δ = templateDisconnectionEvent δ`, which is open in the topology of uniform
convergence on compacts.  Its transfer to the walk is the open-set half of the portmanteau theorem:
if the laws of random paths `Y ε` converge weakly in `C([0,∞), ℝ²)` (the convergence mode of GMS
Theorem 1.16) to the law of a Brownian motion from `0` with covariance `c · I`, then

* `le_liminf_measure_templateDisconnectionEvent`: `P(B ∈ E_δ) ≤ liminf_{ε → 0} P(Y ε ∈ E_δ)` for any
  anisotropic limit `B`;
* `one_sub_le_liminf_measure_templateDisconnectionEvent`: for an isotropic limit,
  `1 - (1 - p₀)^{K(δ)} ≤ liminf_{ε → 0} P(Y ε ∈ E_δ)`, with `p₀ = templateTubeConst` and
  `K(δ) = templateScaleCount δ` the number of template scales `4^{-k}` used at radius `δ`;
* `eventually_lt_measure_templateDisconnectionEvent`: below that bound, `P(Y ε ∈ E_δ)` is eventually
  larger as `ε → 0`;
* `eventually_eventually_lt_measure_templateDisconnectionEvent`: for every `η > 0`, for every small
  enough `δ > 0`, eventually as `ε → 0`, `P(Y ε ∈ E_δ) > 1 - η`.

The last statement keeps the probability bound `1 - η` separate from the radius `δ`, which is the
form of the continuum fact (a probability tending to `1` as `δ → 0`).
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.TemplateEventWalkLimit

open MatedCRT.TemplateEventCompactOpen MatedCRT.TargetLawTemplateEvent MatedCRT.TargetLawRotation
open ReflectedGMS.GMS ReflectedGMS.StatementIngredients

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {Y : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2} {target : AnisotropicBrownianTarget}

/-- **Open-set portmanteau bound for `E_δ`**: under weak convergence in `C([0,∞), ℝ²)` to an
anisotropic Brownian law, the limit probability of the robust disconnection event is at most the
liminf of the probabilities for the approximating paths. -/
theorem le_liminf_measure_templateDisconnectionEvent (h : ConvergesWeaklyInC Q Y target) (δ : ℝ) :
    (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
        (eucPathToComplex ⁻¹' templateDisconnectionEvent δ) ≤
      (𝓝[>] (0 : ℝ≥0)).liminf
        (fun ε => Q {ω | eucPathToComplex (Y ε ω) ∈ templateDisconnectionEvent δ}) :=
  LatticeProb.Portmanteau.le_liminf_measure_setOf_mem_of_convergesWeaklyInC Q Y target h
    (isOpen_preimage_eucPathToComplex_templateDisconnectionEvent δ)

/-- **Lower bound for the approximating paths**: with an isotropic limit of covariance `c · I`,
`1 - (1 - p₀)^{K(δ)} ≤ liminf_{ε → 0} P(Y ε ∈ E_δ)`. -/
theorem one_sub_le_liminf_measure_templateDisconnectionEvent (h : ConvergesWeaklyInC Q Y target)
    {c : ℝ≥0} (hc : 0 < c) (hcov : target.covariance = (c : ℝ) • 1) (δ : ℝ) :
    1 - (1 - templateTubeConst) ^ templateScaleCount δ ≤
      (𝓝[>] (0 : ℝ≥0)).liminf
        (fun ε => Q {ω | eucPathToComplex (Y ε ω) ∈ templateDisconnectionEvent δ}) :=
  (one_sub_le_pathLaw_templateDisconnectionEvent_of_covariance target hc hcov δ).trans
    (le_liminf_measure_templateDisconnectionEvent h δ)

/-- Below the lower bound, the probability of `E_δ` for the approximating paths is eventually larger
as `ε → 0`. -/
theorem eventually_lt_measure_templateDisconnectionEvent (h : ConvergesWeaklyInC Q Y target)
    {c : ℝ≥0} (hc : 0 < c) (hcov : target.covariance = (c : ℝ) • 1) (δ : ℝ) {θ : ℝ≥0∞}
    (hθ : θ < 1 - (1 - templateTubeConst) ^ templateScaleCount δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), θ < Q {ω | eucPathToComplex (Y ε ω) ∈ templateDisconnectionEvent δ} :=
  eventually_lt_of_lt_liminf
    (hθ.trans_le (one_sub_le_liminf_measure_templateDisconnectionEvent h hc hcov δ))

/-- **The robust disconnection event has probability close to `1` for the approximating paths**:
for every `η > 0`, for every small enough radius `δ > 0`, eventually as `ε → 0` the paths `Y ε` lie
in `E_δ` with probability larger than `1 - η`. -/
theorem eventually_eventually_lt_measure_templateDisconnectionEvent
    (h : ConvergesWeaklyInC Q Y target) {c : ℝ≥0} (hc : 0 < c)
    (hcov : target.covariance = (c : ℝ) • 1) {η : ℝ≥0∞} (hη : 0 < η) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      1 - η < Q {ω | eucPathToComplex (Y ε ω) ∈ templateDisconnectionEvent δ} := by
  have hlt : 1 - η < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hη.ne'
  filter_upwards [(tendsto_order.1 tendsto_planarBrownianMotion_templateDisconnectionEvent).1 _ hlt]
    with δ hδ
  rw [← pathLaw_preimage_templateDisconnectionEvent_of_covariance target hc hcov δ] at hδ
  exact eventually_lt_of_lt_liminf (hδ.trans_le (le_liminf_measure_templateDisconnectionEvent h δ))

end MatedCRT.TemplateEventWalkLimit

/-! ## Audit -/
#print axioms MatedCRT.TemplateEventWalkLimit.le_liminf_measure_templateDisconnectionEvent
#print axioms MatedCRT.TemplateEventWalkLimit.one_sub_le_liminf_measure_templateDisconnectionEvent
#print axioms MatedCRT.TemplateEventWalkLimit.eventually_lt_measure_templateDisconnectionEvent
#print axioms MatedCRT.TemplateEventWalkLimit.eventually_eventually_lt_measure_templateDisconnectionEvent

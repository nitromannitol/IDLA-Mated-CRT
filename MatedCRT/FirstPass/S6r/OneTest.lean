import Mathlib
import MatedCRT.LPStaging.Prob.SecondMomentMethod

/-!
# One-test estimate (§3 `S5_oneTest`): the deterministic part

For a measure `P` (for the paper, the conditional law given `(h, η)`) and a measurable one-test variable
`V : Ω → ℝ≥0∞`:
* `paley_zygmund_sq`: `(∫⁻ V dP)² ≤ (∫⁻ V² dP) · P{V ≠ 0}` (second-moment method, Cauchy-Schwarz = Hölder with p = q = 2);
* `oneTest_prob_lower` (S5.3): under the first moment `c ε⁻¹ m ≤ E V` (S5.1) and the second moment
  `E V² ≤ C ε⁻² (1 + log(1/R))² m²` (S5.2), with `0 < R ≤ 1`: `c²/(C (1 + log(1/R))²) ≤ P{V ≠ 0}`;
* `oneTest_prob_lower_log` (S5.4): for `r² ≤ R ≤ 1` and `0 < r ≤ 1`: `(c²/(4C)) / (1 + log(1/r))² ≤ P{V ≠ 0}`.

NAMED INPUTS, not proved in this file: the first moment (S5.1) and the second moment (S5.2) are hypotheses of the
statements. In the chat they come from the printed Steps 2-4 with the corrected good event, the Green lower bound
(Lemma 2.16), the corrected ball-form exit-time estimate, and the mass condition `μ_h(B_{R/4}(x)) ≥ c R^{β⁻}`. The
shell form of the test start (S7' step 9, `S5_geometry_at_shell_test`) is likewise not proved here. `m` is the real
value of `m_R^φ` (positive and finite on the good event). `V` is abstract: the chat does not define it in §7.

Terminology: second-moment (Paley-Zygmund) method; Armstrong-Kuusi-Mourrat (good annuli and one-test estimates).

## Conditional form and the hypothesis `hone`

`oneTest_hone_shell` is the one-test estimate (7.50) in the form consumed by `prefix_bad_bound`
(`hone` of `S6r/Amplification.lean`): with `𝓖 = 𝓕_{T_k}`, `P = prefixSet`, `F = testFailSet`, `q = q0/(1 + log(1/r))²`
(the (7.51) bound, `shellTestQ q0 r`). The conditional Paley-Zygmund step (`condExp_sq_le_mul`,
`oneTest_hone_of_moments`) is proved. NAMED INPUTS (hypotheses, not proved here):
* `hVF`: the one-test variable `V` vanishes on the test-success event `F` (V > 0 only on an escape during the test);
* `hfirst`, `hsecond`: the conditional first and second moments (S5.1), (S5.2) given `𝓕_{T_k}` on the prefix event;
  they are the (h, η)-conditional bounds transported to `T_k` by the strong Markov property (not formalized here).
-/

open MeasureTheory
open scoped ENNReal

namespace MatedCRT

namespace Lemma68Window

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `(x ^ (1/2))² = x` in `ℝ≥0∞`. -/
lemma rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x :=
  LatticeProb.SecondMomentMethod.rpow_half_sq x

/-- Second-moment (Paley-Zygmund) inequality: `(∫ V)² ≤ (∫ V²) · P{V ≠ 0}`. -/
theorem paley_zygmund_sq (P : Measure Ω) {V : Ω → ℝ≥0∞} (hV : Measurable V) :
    (∫⁻ ω, V ω ∂P) ^ 2 ≤ (∫⁻ ω, V ω ^ 2 ∂P) * P {ω | V ω ≠ 0} :=
  LatticeProb.SecondMomentMethod.paley_zygmund_sq P hV

/-- (S5.3): the one-test lower bound `P{V ≠ 0} ≥ c²/(C (1 + log(1/R))²)` from the first moment (S5.1) and
the second moment (S5.2); `0 < R ≤ 1` makes `1 + log(1/R) ≥ 1 > 0`. -/
theorem oneTest_prob_lower {c C ε m R : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hm : 0 < m)
    (hR : 0 < R) (hR1 : R ≤ 1) (P : Measure Ω) {V : Ω → ℝ≥0∞} (hV : Measurable V)
    (h1 : ENNReal.ofReal (c * ε⁻¹ * m) ≤ ∫⁻ ω, V ω ∂P)
    (h2 : ∫⁻ ω, V ω ^ 2 ∂P ≤ ENNReal.ofReal (C * (ε⁻¹ ^ 2) * (1 + Real.log (1 / R)) ^ 2 * m ^ 2)) :
    ENNReal.ofReal (c ^ 2 / (C * (1 + Real.log (1 / R)) ^ 2)) ≤ P {ω | V ω ≠ 0} :=
  LatticeProb.SecondMomentMethod.oneTest_prob_lower hc hC hε hm hR hR1 P hV h1 h2

/-- (S5.4): for `r² ≤ R ≤ 1`, `log(1/R) ≤ 2 log(1/r)`, so the one-test bound has the form
`q(r) / (1 + log(1/r))²` with `q = c²/(4C)`. -/
theorem oneTest_prob_lower_log {c C ε m r R : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hm : 0 < m)
    (hr : 0 < r) (hr1 : r ≤ 1) (hRr : r ^ 2 ≤ R) (hR : 0 < R) (hR1 : R ≤ 1)
    (P : Measure Ω) {V : Ω → ℝ≥0∞} (hV : Measurable V)
    (h1 : ENNReal.ofReal (c * ε⁻¹ * m) ≤ ∫⁻ ω, V ω ∂P)
    (h2 : ∫⁻ ω, V ω ^ 2 ∂P ≤ ENNReal.ofReal (C * (ε⁻¹ ^ 2) * (1 + Real.log (1 / R)) ^ 2 * m ^ 2)) :
    ENNReal.ofReal (c ^ 2 / (4 * C) / (1 + Real.log (1 / r)) ^ 2) ≤ P {ω | V ω ≠ 0} :=
  LatticeProb.SecondMomentMethod.oneTest_prob_lower_log hc hC hε hm hr hr1 hRr hR hR1 P hV h1 h2

/-! ### Conditional second-moment method (notes (8.4)) -/

/-- Complement for the ambient σ-algebra only (a local instance `𝓖` would otherwise be picked up). -/
theorem measurableSet_compl_ambient {F : Set Ω} (hF : MeasurableSet[mΩ] F) :
    MeasurableSet[mΩ] Fᶜ :=
  hF.compl

/-- Integrability of an ambient-measurable indicator of `1` (ambient σ-algebra only). -/
theorem integrable_indicator_ambient {μ : Measure Ω} [IsFiniteMeasure μ] {F : Set Ω}
    (hF : MeasurableSet[mΩ] F) : Integrable (F.indicator (fun _ => (1 : ℝ))) μ :=
  (integrable_const (1 : ℝ)).indicator hF

/-- Conditional Cauchy-Schwarz (conditional second-moment method): if `V = 0` on the test-success
event `F`, so that `V = V · 1_{Fᶜ}`, then `(E[V | 𝓖])² ≤ E[V² | 𝓖] · E[1_{Fᶜ} | 𝓖]` a.s.
Proof: for every real `x`, `E[(V - x 1_{Fᶜ})² | 𝓖] ≥ 0`, which is a quadratic in `x` with
nonpositive discriminant. -/
theorem condExp_sq_le_mul {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓖 : MeasurableSpace Ω}
    {F : Set Ω} (hF : MeasurableSet[mΩ] F) {V : Ω → ℝ}
    (hVF : ∀ ω ∈ F, V ω = 0) (hV1 : Integrable V μ) (hV2 : Integrable (fun ω => V ω ^ 2) μ) :
    ∀ᵐ ω ∂μ, (μ[V | 𝓖] ω) ^ 2 ≤ μ[fun ω => V ω ^ 2 | 𝓖] ω * μ[Fᶜ.indicator (fun _ => (1 : ℝ)) | 𝓖] ω :=
  @LatticeProb.SecondMomentMethod.condExp_sq_le_mul Ω mΩ μ (by assumption) 𝓖 F hF V hVF hV1 hV2

/-- The conditional one-test bound (notes (8.4)): if `V = 0` on `F`, and on the prefix event `P`
the conditional first moment `E[V | 𝓖]` is at least `a ≥ 0` and the conditional second moment
`E[V² | 𝓖]` is at most `b > 0`, then `E[1_F | 𝓖] ≤ 1 - a²/b` a.s. on `P`. -/
theorem oneTest_hone_of_moments {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓖 : MeasurableSpace Ω}
    (h𝓖 : 𝓖 ≤ mΩ) {P F : Set Ω} (hF : MeasurableSet[mΩ] F) {V : Ω → ℝ}
    (hVF : ∀ ω ∈ F, V ω = 0) (hV1 : Integrable V μ) (hV2 : Integrable (fun ω => V ω ^ 2) μ)
    {a b : Ω → ℝ}
    (ha : ∀ᵐ ω ∂μ, ω ∈ P → 0 ≤ a ω ∧ a ω ≤ μ[V | 𝓖] ω)
    (hb : ∀ᵐ ω ∂μ, ω ∈ P → 0 < b ω ∧ μ[fun ω => V ω ^ 2 | 𝓖] ω ≤ b ω) :
    ∀ᵐ ω ∂μ, ω ∈ P → μ[F.indicator (fun _ => (1 : ℝ)) | 𝓖] ω ≤ 1 - a ω ^ 2 / b ω :=
  @LatticeProb.SecondMomentMethod.oneTest_hone_of_moments Ω mΩ μ (by assumption) 𝓖 h𝓖 P F hF V hVF hV1 hV2 a b ha hb

/-- Pure real inequality for the (S5.3)-(S5.4) arithmetic: with `a = c ε⁻¹ m`, `b = C ε⁻² (1 + log(1/R))² m²`
and `r² ≤ R ≤ 1`, the ratio `a²/b = c²/(C (1 + log(1/R))²)` dominates `q0 / (1 + log(1/r))²` when
`q0 ≤ c²/(4C)`, since `log(1/R) ≤ 2 log(1/r)`. -/
theorem oneTest_ratio_bound {c C ε m R r q0 : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hm : 0 < m)
    (hr : 0 < r) (hr1 : r ≤ 1) (hRr : r ^ 2 ≤ R) (hR1 : R ≤ 1) (hq0c : q0 ≤ c ^ 2 / (4 * C)) :
    q0 / (1 + Real.log (1 / r)) ^ 2
      ≤ (c * ε⁻¹ * m) ^ 2 / (C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R)) ^ 2 * m ^ 2) :=
  LatticeProb.SecondMomentMethod.oneTest_ratio_bound hc hC hε hm hr hr1 hRr hR1 hq0c

/-- The (7.51) constant is a probability: `0 ≤ q0/(1 + log(1/r))² ≤ q0 ≤ 1` for `0 < r ≤ 1`, so the
hypothesis `q ≤ 1` of `prefix_bad_bound` holds. -/
theorem oneTest_q_bounds {q0 r : ℝ} (hq0 : 0 ≤ q0) (hq01 : q0 ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) :
    0 ≤ q0 / (1 + Real.log (1 / r)) ^ 2 ∧ q0 / (1 + Real.log (1 / r)) ^ 2 ≤ 1 :=
  LatticeProb.SecondMomentMethod.oneTest_q_bounds hq0 hq01 hr hr1

/-- The one-test estimate (7.50) in the form `hone` of `prefix_bad_bound` (`S6r/Amplification.lean`):
with `𝓖 = 𝓕_{T_k}`, `P = prefixSet`, `F = testFailSet`, the conditional probability of `F` given `𝓖` is at
most `1 - q0/(1 + log(1/r))²` a.s. on `P`, provided the conditional moments (S5.1)-(S5.2) hold on `P`
with the random scales `m`, `R`, `r² ≤ R ≤ 1` on `P`, and `V = 0` on `F`.
Named inputs: `hVF`, `hfirst`, `hsecond` (see the module docstring). `q0 ≤ c²/(4C)` and `q0 ≤ 1` make
the constant `q0/(1 + log(1/r))²` satisfy the (7.51) bound and `q ≤ 1` for `prefix_bad_bound`. -/
theorem oneTest_hone_shell {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓖 : MeasurableSpace Ω}
    (h𝓖 : 𝓖 ≤ mΩ) {P F : Set Ω} (hF : MeasurableSet[mΩ] F)
    {V : Ω → ℝ} (hVF : ∀ ω ∈ F, V ω = 0) (hV1 : Integrable V μ)
    (hV2 : Integrable (fun ω => V ω ^ 2) μ)
    {c C ε r q0 : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ c ^ 2 / (4 * C))
    {m R : Ω → ℝ} (hm : ∀ ω ∈ P, 0 < m ω) (hRr : ∀ ω ∈ P, r ^ 2 ≤ R ω ∧ R ω ≤ 1)
    (hfirst : ∀ᵐ ω ∂μ, ω ∈ P → c * ε⁻¹ * m ω ≤ μ[V | 𝓖] ω)
    (hsecond : ∀ᵐ ω ∂μ, ω ∈ P →
      μ[fun ω => V ω ^ 2 | 𝓖] ω ≤ C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R ω)) ^ 2 * m ω ^ 2) :
    ∀ᵐ ω ∂μ, ω ∈ P → μ[F.indicator (fun _ => (1 : ℝ)) | 𝓖] ω ≤ 1 - q0 / (1 + Real.log (1 / r)) ^ 2 :=
  @LatticeProb.SecondMomentMethod.oneTest_hone_shell Ω mΩ μ (by assumption) 𝓖 h𝓖 P F hF V hVF hV1 hV2 c C ε r q0 hc hC hε hr hr1 hq0c m R hm hRr hfirst hsecond

end Lemma68Window

end MatedCRT

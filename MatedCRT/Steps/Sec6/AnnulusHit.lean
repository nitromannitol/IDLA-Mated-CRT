import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section6
import MatedCRT.Proofs.Sec6.AnnulusHit.EventInvariance

/-!
# Lemma 6.5 (lemma:annulus-hit, line 2333): steps of the printed proof (lines 2343-2368)

The event is the corrected one, with the scale-invariant integrand `log (r/|u - v|) + 1` (CORRECTION [C5]).

The printed proof compares the `γ`-quantum cone field `h` with a whole-plane GFF `h^ℂ` (Step 1) and uses the exact
scale and translation invariance of `h^ℂ` modulo additive constants (Step 2). The literature facts on the fields are
the step Props below (INPUT-REQUESTS IR-c4-1 to IR-c4-4). Their deterministic content is proved in
`MatedCRT/Proofs/Sec6/AnnulusHit/EventInvariance.lean`:

* Step 1 (lines 2348-2363). `ConeWholePlaneWeylComparisonStep`: eq:gff (line 444, `h|_{B_1} =d (h^ℂ - γ log|·|)|_{B_1}`)
  with Weyl scaling (Fact 2.2) gives `μ_h|_{B_1} =d (|x|^{-γ²} μ_{h^ℂ})|_{B_1}`, applied to `E_r(z)`. The comparison
  `E_r(z; C₁)` for `μ_{h^ℂ}` ⟹ `E_r(z; 601^{2γ²} C₁)` for `|x|^{-γ²} μ_{h^ℂ}` is
  `isGoodAnnulusEvent_withDensity_norm_rpow`. It is deterministic.
* Step 2 (line 2367). `WholePlaneLQGCoordinateChangeStep`: by eq:gff-scaling and the LQG coordinate change,
  `μ_{h^ℂ} ∘ (x ↦ r x + z)` is `c μ''` with `c ∈ (0, ∞)` random and `μ''` the LQG measure of another whole-plane GFF.
  `E_r(z)` for `μ_{h^ℂ}` is then `E_1(0)` for `μ''` (`isGoodAnnulusEvent_map_iff`, `isGoodAnnulusEvent_smul_iff`).
  `WholePlaneGoodAnnulusTightnessStep`: `L_1(0)/R_1(0)` is a positive finite random variable, so `P[E_1(0; C₁)]`
  tends to `1` as `C₁ → ∞`.
* `WholePlaneLQGExistenceStep`: a whole-plane GFF with its `γ`-LQG measure exists.

Fact 2.2 (`LQGMeasurePropertiesStmt`) is drafted for the cone field only. Every use of Weyl scaling and of the
coordinate change in this proof is for the whole-plane field `h^ℂ`, so these uses sit inside the step Props, and the
deduction below takes no Fact 2.2 hypothesis.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls
open scoped ENNReal

/-- **A whole-plane GFF with its LQG measure exists** (Sheffield 2007, Section 2; Duplantier-Sheffield 2011,
Proposition 1.1; INPUT-REQUESTS IR-c4-1). -/
def WholePlaneLQGExistenceStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
    (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
    IsProbabilityMeasure P' ∧ IsWholePlaneGFF P' hC' hcirc' ∧ IsLQGMeasure P' γ hcirc' μ'

/-- **Step 1 input: the cone field near an admissible annulus is the whole-plane field with the density `|x|^{-γ²}`**
(lines 2348-2355). By eq:gff (line 444), `h|_{B_1} =d (h^ℂ - γ log |·|)|_{B_1}`. Weyl scaling (Fact 2.2(iii),
Duplantier-Sheffield 2011 Proposition 1.2) gives `μ_{h^ℂ - γ log|·|} = |x|^{-γ²} μ_{h^ℂ}` away from `0`. Hence
`μ_h|_{B_1}` and `(|x|^{-γ²} μ_{h^ℂ})|_{B_1}` have the same law. Applied to the event `E_r(z; C)`, which depends
only on the measure on `𝔸_{r/3,3r}(z) ⊆ B_ρ`, this gives the comparison below (INPUT-REQUESTS IR-c4-2). -/
def ConeWholePlaneWeylComparisonStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ c₀ : ℝ, 0 < c₀ → c₀ < 1 / 5 → ∀ C : ℝ, 0 < C →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
    (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
    IsProbabilityMeasure P' → IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasure P' γ hcirc' μ' →
  ∀ (r : ℝ) (z : ℂ), 0 < r → annulus z (r / 3) (3 * r) ⊆ ball 0 ρ →
    r / 100 ≤ infDist 0 (annulus z (r / 3) (3 * r)) →
    P {ω | ¬ IsGoodAnnulusEvent (μ ω) c₀ C r z} ≤
      P' {ω | ¬ IsGoodAnnulusEvent ((μ' ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-γ ^ 2))) c₀ C r z}

/-- **Step 2 input: scale and translation invariance of the whole-plane LQG measure modulo constants** (line 2367;
eq:gff-scaling for `h^ℂ`, the LQG coordinate change formula and Weyl scaling by constants, Duplantier-Sheffield 2011
Propositions 1.2 and 2.1). For `r > 0` and `z ∈ ℂ`, `h'' = h^ℂ(r · + z) - h^ℂ_r(z)` is again a whole-plane GFF.
Its LQG measure `μ''` satisfies `μ_{h^ℂ} ∘ (x ↦ r x + z) = c μ''` with
`c = r^{γQ} e^{γ h^ℂ_r(z)} ∈ (0, ∞)` (INPUT-REQUESTS IR-c4-3). -/
def WholePlaneLQGCoordinateChangeStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
    (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
    IsProbabilityMeasure P' → IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasure P' γ hcirc' μ' →
  ∀ (r : ℝ), 0 < r → ∀ z : ℂ, ∃ (hC'' : Ω' → (ℂ → ℝ) → ℝ) (hcirc'' : Ω' → ℝ → ℂ → ℝ)
    (μ'' : Ω' → Measure ℂ) (c : Ω' → ℝ≥0∞),
    IsWholePlaneGFF P' hC'' hcirc'' ∧ IsLQGMeasure P' γ hcirc'' μ'' ∧
    ∀ᵐ ω ∂P', c ω ≠ 0 ∧ c ω ≠ ∞ ∧ (μ' ω).map (fun x => (x - z) / (r : ℂ)) = c ω • μ'' ω

/-- **Step 2 input: the ratio `L_1(0)/R_1(0)` is a positive finite random variable** (line 2367, last sentence). For
the whole-plane LQG measure, a.s. `sup_v ∫_{𝔸_{1,2}} (log (1/|u - v|) + 1) dμ(u) < ∞` (the LQG measure of
`B_s(v)` is at most `s^α` uniformly, Rhodes-Vargas 2014 Theorem 2.6) and `min_w μ(B_{𝐜₀}(w)) > 0` (full support).
Hence `P[E_1(0; C)] → 1` as `C → ∞` (INPUT-REQUESTS IR-c4-4). -/
def WholePlaneGoodAnnulusTightnessStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ c₀ : ℝ, 0 < c₀ → c₀ < 1 / 5 → ∀ p : ℝ, 0 < p → p < 1 → ∃ C : ℝ, 0 < C ∧
  ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
    (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
    IsProbabilityMeasure P' → IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasure P' γ hcirc' μ' →
    P' {ω | ¬ IsGoodAnnulusEvent (μ' ω) c₀ C 1 0} ≤ ENNReal.ofReal (1 - p)

/-- **Lemma 6.5 from its steps** (proof lines 2343-2368). With `C₁` from the tightness step and
`C = 601^{2γ²} C₁`, compare the cone field with a whole-plane field (Step 1), then move the annulus to `𝔸_{1,2}(0)`
(Step 2). -/
theorem annulusHit_of_steps (h0 : WholePlaneLQGExistenceStep)
    (h1 : ConeWholePlaneWeylComparisonStep) (h2a : WholePlaneLQGCoordinateChangeStep)
    (h2b : WholePlaneGoodAnnulusTightnessStep) : AnnulusHitStmt := by
  intro γ hγ hγ2 ρ hρ hρ1 c₀ hc₀ hc₀' p hp hp1
  obtain ⟨C₁, hC₁, htight⟩ := h2b γ hγ hγ2 c₀ hc₀ hc₀' p hp hp1
  have hA : (0 : ℝ) < ((601 : ℝ) ^ (γ ^ 2)) ^ 2 * C₁ := by positivity
  refine ⟨((601 : ℝ) ^ (γ ^ 2)) ^ 2 * C₁, hA, ?_⟩
  intro Ω _ P hC hcirc μ hcone r z hr hsub hdist
  obtain ⟨Ω', mΩ', P', hC', hcirc', μ', hP', hwp, hlqg⟩ := h0 γ hγ hγ2
  obtain ⟨hC'', hcirc'', μ'', c, hwp'', hlqg'', hc⟩ :=
    h2a γ hγ hγ2 Ω' P' hC' hcirc' μ' hP' hwp hlqg r hr z
  calc P {ω | ¬ IsGoodAnnulusEvent (μ ω) c₀ (((601 : ℝ) ^ (γ ^ 2)) ^ 2 * C₁) r z}
      ≤ P' {ω | ¬ IsGoodAnnulusEvent ((μ' ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-γ ^ 2))) c₀
          (((601 : ℝ) ^ (γ ^ 2)) ^ 2 * C₁) r z} :=
        h1 γ hγ hγ2 ρ hρ hρ1 c₀ hc₀ hc₀' _ hA Ω P hC hcirc μ hcone Ω' P' hC' hcirc' μ' hP' hwp hlqg r z
          hr hsub hdist
    _ ≤ P' {ω | ¬ IsGoodAnnulusEvent (μ' ω) c₀ C₁ r z} := by
        refine measure_mono fun ω hω hE => hω ?_
        exact isGoodAnnulusEvent_withDensity_norm_rpow hr hc₀' hC₁.le (sq_nonneg γ) hdist hE
    _ = P' {ω | ¬ IsGoodAnnulusEvent (μ'' ω) c₀ C₁ 1 0} := by
        refine measure_congr ?_
        filter_upwards [hc] with ω hω
        refine propext (not_congr ?_)
        rw [isGoodAnnulusEvent_map_iff hr, hω.2.2]
        exact isGoodAnnulusEvent_smul_iff hω.1 hω.2.1
    _ ≤ ENNReal.ofReal (1 - p) := htight Ω' P' hC'' hcirc'' μ'' hP' hwp'' hlqg''

end MatedCRT

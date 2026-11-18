import MatedCRT.FirstPass.Derived.ConeAreaMeasureCode
import MatedCRT.FirstPass.Derived.CouplingReferenceCone
import MatedCRT.FirstPass.Derived.StoppedHeatBoundOfBallBound
import MatedCRT.FirstPass.Derived.LBMLawContinuityValid
import MatedCRT.Proofs.Sec1.EnvironmentScaling.CanonicalObservableAssembly

/-!
# Ball-mass bounds for the approximants of the LQG measure of a valid environment

For a valid mated-CRT environment `S` and `γ ∈ (0, 2)`, almost surely the dyadic approximants
`ε^{γ²/2} e^{γ h_ε(x)} dx`, `ε = 2^{-k}`, of the `γ`-LQG measure of the quantum cone field satisfy,
on every disc `B̄(0, R)`, a ball-mass bound `C r^β` uniformly in the level `k`.

Route. The mating-of-trees coupling of `S` carries a reference quantum cone, built from a normalized
whole-plane GFF and an independent conditioned Brownian path, for which the bound holds almost surely
(`ae_coneRef_approximant_ball_rpow_bound`). The bound is an event of the field code
`φ ↦ (h, φ)` (countably many centres and radii, rational exponents and constants; the dyadic circle
averages are Borel functions of the code, `fieldCodeDyadicCircle`), and two quantum cones have the same
joint law of all admissible observables (`map_coneObservables_eq_of_isQuantumCone`), hence the same law of
their field codes. So the bound transfers to the field of `S`.

Consequences: the stopped heat bound for the circle averages of `S`
(`stoppedHeatBound_of_forall_ballBound`), and the continuity in the starting point of the law of the
Liouville Brownian path of every valid environment (`lbmLawContinuity_of_isValid`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set MarkovProcess
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- The dyadic approximant `ε^{γ²/2} e^{γ h_ε(x)} dx`, `ε = 2^{-k}`, of the `γ`-LQG measure computed
from a field code. -/
def codeApprox (γ : ℝ) (k : ℕ) (F : FieldPairingCode) : Measure ℂ :=
  (volume : Measure ℂ).withDensity fun z => ENNReal.ofReal
    (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCodeDyadicCircle k F z))

theorem measurable_codeApprox (γ : ℝ) (k : ℕ) : Measurable (codeApprox γ k) := by
  have hd : Measurable (Function.uncurry fun (F : FieldPairingCode) (z : ℂ) =>
      LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCodeDyadicCircle k F z)) :=
    measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_fieldCodeDyadicCircle k)))
  exact LQGMeasureField.measurable_withDensity_ofReal hd

/-- If the code computes the circle averages of `h` at the radius `2^{-k}`, its approximant is the
approximant of `h`. -/
theorem lqgApprox_dyadicScale_eq_codeApprox {γ : ℝ} {h : ℝ → ℂ → ℝ} {F : FieldPairingCode} {k : ℕ}
    (hk : ∀ z, fieldCodeDyadicCircle k F z = h ((2 : ℝ)⁻¹ ^ k) z) :
    LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k) = codeApprox γ k F := by
  unfold LatticeProb.LQG.lqgApprox codeApprox
  congr 1
  funext z
  rw [hk z]
  rfl

/-- The countable ball-mass event of a field code: for every `R ∈ ℕ` there are rational `β, C > 0`
such that every approximant gives every ball centred at a point of the dense sequence of `ℂ` in
`B̄(0, R + 1)`, of rational radius `r ∈ (0, 1]`, mass at most `C r^β`. -/
def codeBallEvent (γ : ℝ) : Set FieldPairingCode :=
  {F | ∀ R : ℕ, ∃ β C : ℚ, 0 < β ∧ 0 < C ∧ ∀ n : ℕ,
    ‖TopologicalSpace.denseSeq ℂ n‖ ≤ (R : ℝ) + 1 → ∀ r : ℚ, 0 < (r : ℝ) → (r : ℝ) ≤ 1 → ∀ k : ℕ,
      codeApprox γ k F (Metric.ball (TopologicalSpace.denseSeq ℂ n) r) ≤
        ENNReal.ofReal ((C : ℝ) * (r : ℝ) ^ (β : ℝ))}

theorem measurableSet_codeBallEvent (γ : ℝ) : MeasurableSet (codeBallEvent γ) := by
  have hatom : ∀ (k : ℕ) (s : Set ℂ) (c : ℝ≥0∞), MeasurableSet s →
      Measurable fun F : FieldPairingCode => codeApprox γ k F s ≤ c := fun k s c hs =>
    measurableSet_setOfPred.1
      (measurableSet_le ((Measure.measurable_coe hs).comp (measurable_codeApprox γ k))
        measurable_const)
  exact measurableSet_setOfPred.2 (Measurable.forall fun R => Measurable.exists fun β =>
    Measurable.exists fun C => measurable_const.and (measurable_const.and
      (Measurable.forall fun n => measurable_const.imp (Measurable.forall fun r =>
        measurable_const.imp (measurable_const.imp (Measurable.forall fun k =>
          hatom k _ _ Metric.isOpen_ball.measurableSet))))))

/-- A ball-mass bound with real constants on every disc gives the countable code event. -/
theorem mem_codeBallEvent_of_ballBound {γ : ℝ} {h : ℝ → ℂ → ℝ} {F : FieldPairingCode}
    (hF : ∀ k, LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k) = codeApprox γ k F)
    (hb : ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
        LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k) (Metric.ball z r) ≤
          ENNReal.ofReal (C * r ^ β)) :
    F ∈ codeBallEvent γ := by
  intro R
  obtain ⟨β, C, hβ, hC, hb⟩ := hb ((R : ℝ) + 1) (by positivity)
  obtain ⟨β', hβ'0, hβ'⟩ := exists_rat_btwn hβ
  obtain ⟨C', hC'⟩ := exists_rat_gt C
  refine ⟨β', C', by exact_mod_cast hβ'0, by exact_mod_cast hC.trans hC',
    fun n hn r hr hr1 k => ?_⟩
  rw [← hF k]
  refine (hb _ hn r hr hr1 k).trans (ENNReal.ofReal_le_ofReal ?_)
  have hpow : (r : ℝ) ^ β ≤ (r : ℝ) ^ (β' : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 hβ'.le
  exact mul_le_mul hC'.le hpow (Real.rpow_nonneg hr.le _) (hC.trans hC').le

/-- The countable code event gives a ball-mass bound on every disc. -/
theorem ballBound_of_mem_codeBallEvent {γ : ℝ} {h : ℝ → ℂ → ℝ} {F : FieldPairingCode}
    (hF : ∀ k, LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k) = codeApprox γ k F)
    (hE : F ∈ codeBallEvent γ) :
    ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
        LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k) (Metric.ball z r) ≤
          ENNReal.ofReal (C * r ^ β) := by
  intro R _
  obtain ⟨β, C, hβ, hC, hb⟩ := hE ⌈R⌉₊
  refine ⟨β, C, by exact_mod_cast hβ, by exact_mod_cast hC, fun z hz r hr hr1 k => ?_⟩
  exact lqgApprox_ball_le_of_denseSeq (R := (⌈R⌉₊ : ℝ)) (by exact_mod_cast hβ.le)
    (by exact_mod_cast hC.le) (fun n hn q hq hq1 => by rw [hF k]; exact hb n hn q hq hq1 k)
    (hz.trans (Nat.le_ceil R)) hr hr1

/-- The dyadic circle averages of a quantum cone are recovered, almost surely at all scales and all
points at once, from its pairings with test functions. -/
theorem ae_fieldCodeDyadicCircle_eq_of_isQuantumCone_pairing {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ z : ℂ,
      fieldCodeDyadicCircle n (fun φ => hC ω φ.1) z = hcirc ω ((2 : ℝ)⁻¹ ^ n) z :=
  ae_fieldCodeDyadicCircle_eq_of_isQuantumCone
    (S := ⟨P, hC, hcirc, fun _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ => 0⟩) h

/-- The field code of a sample of admissible observables: its pairings with test functions. -/
def admissiblePairingCode (x : GFFObservable.Admissible → ℝ) : FieldPairingCode :=
  fun φ => x (Subtype.mk (p := GFFObservable.IsAdmissible) (GFFObservable.pairing φ.1) φ.2)

theorem measurable_admissiblePairingCode : Measurable admissiblePairingCode :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem measurable_coneObservables {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    Measurable fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω) := by
  refine measurable_pi_iff.2 fun o => ?_
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => exact h.measurable_pairing φ ho
  | circle r z => exact h.measurable_circle r z ho

/-- **Transfer of the approximant ball-mass bound between quantum cones.** If the dyadic approximants
of the `γ`-LQG measure of one `γ`-quantum cone almost surely satisfy a ball-mass bound `C r^β` on every
disc, uniformly in the level, then so do those of every other `γ`-quantum cone, possibly on another
probability space. -/
theorem ae_approximant_ballBound_of_isQuantumCone {γ : ℝ} {Ω Ω' : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC hcirc) (h' : IsQuantumCone γ P' hC' hcirc')
    (hball' : ∀ᵐ ω ∂P', ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
        LatticeProb.LQG.lqgApprox γ (hcirc' ω) (LatticeProb.LQG.dyadicScale k) (Metric.ball z r) ≤
          ENNReal.ofReal (C * r ^ β)) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
        LatticeProb.LQG.lqgApprox γ (hcirc ω) (LatticeProb.LQG.dyadicScale k) (Metric.ball z r) ≤
          ENNReal.ofReal (C * r ^ β) := by
  have hm : MeasurableSet (admissiblePairingCode ⁻¹' codeBallEvent γ) :=
    measurable_admissiblePairingCode (measurableSet_codeBallEvent γ)
  have hE' : ∀ᵐ ω ∂P', admissiblePairingCode (fun o : GFFObservable.Admissible =>
      o.1.eval (hC' ω) (hcirc' ω)) ∈ codeBallEvent γ := by
    filter_upwards [hball', ae_fieldCodeDyadicCircle_eq_of_isQuantumCone_pairing h'] with ω hb hf
    exact mem_codeBallEvent_of_ballBound (fun k => lqgApprox_dyadicScale_eq_codeApprox (hf k)) hb
  have hlaw := MatedCRT.Sec1.map_coneObservables_eq_of_isQuantumCone h h'
  have h1 := (ae_map_iff (measurable_coneObservables h').aemeasurable hm).2 hE'
  rw [← hlaw] at h1
  have hE := (ae_map_iff (measurable_coneObservables h).aemeasurable hm).1 h1
  filter_upwards [hE, ae_fieldCodeDyadicCircle_eq_of_isQuantumCone_pairing h] with ω hb hf
  exact ballBound_of_mem_codeBallEvent (fun k => lqgApprox_dyadicScale_eq_codeApprox (hf k)) hb

/-- **Ball-mass bound for a valid environment.** For `γ ∈ (0, 2)` and a valid environment `S`,
almost surely for every `R > 0` there are `β, C > 0` such that the dyadic approximants of the
`γ`-LQG measure of the field of `S` give every ball `B(z, r)` with `‖z‖ ≤ R` and `0 < r ≤ 1` mass
at most `C r^β`, for every level `k`. -/
theorem ae_approximant_ballBound_of_isValid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
        LatticeProb.LQG.lqgApprox γ (S.hcirc ω) (LatticeProb.LQG.dyadicScale k)
            (Metric.ball z r) ≤ ENNReal.ofReal (C * r ^ β) := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, D, -⟩ := hS.matingOfTrees
  obtain ⟨R, W, F, hC, c, -, -, -, -, -, -, -, -, -, hG, -, -, hhC, hc, hcont, hmeas, hcone⟩ :=
    MatedCRT.Sec1.exists_reference_cone_witnesses_of_coupling D hγ hγ2
  exact ae_approximant_ballBound_of_isQuantumCone hS.isQuantumCone hcone
    ((ae_coneRef_approximant_ball_rpow_bound hG hhC hc hcont hmeas hγ hγ2).mono
      fun ω hω => hω (F ω))

/-- **Stopped heat bound for a valid environment.** For `γ ∈ (0, 2)` and a valid environment `S`,
almost surely for every `R > 0` there are `β, C > 0` such that for every start `z` with `‖z‖ ≤ R`,
every level `k` and every `t ≥ 0`, the expected occupation integral of the approximant density
`ε^{γ²/2} e^{γ h_ε}`, `ε = 2^{-k}`, along planar Brownian motion from `z` stopped at
`t ∧ τ_{B(0, R+1)}` is at most `C t^β`. -/
theorem ae_stoppedHeatBound_of_isValid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
        ∫⁻ b, (∫⁻ s in Ioc 0 (min t
            (ContinuousPath.exitTime (Metric.ball (0 : ℂ) (R + 1)) b).toReal),
            ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
              Real.exp (γ * S.hcirc ω (LatticeProb.LQG.dyadicScale k) (b s.toNNReal))))
          ∂(planarBrownianMotion z) ≤ ENNReal.ofReal (C * t ^ β) := by
  filter_upwards [ae_approximant_ballBound_of_isValid hγ hγ2 hS,
    hS.isQuantumCone.ae_continuousOn_circle] with ω hb hcont
  refine stoppedHeatBound_of_forall_ballBound (fun k => ?_) hb
  have hk : Continuous (S.hcirc ω (LatticeProb.LQG.dyadicScale k)) := by
    apply continuousOn_univ.mp
    apply hcont.comp (continuous_const.prodMk continuous_id).continuousOn
    intro z _
    refine ⟨?_, mem_univ z⟩
    show (0 : ℝ) < (2 : ℝ)⁻¹ ^ k
    positivity
  exact hk.measurable

/-- **Continuity of the Liouville Brownian law for every valid environment.** For `γ ∈ (0, 2)` and
every valid environment, almost surely the law of the Liouville Brownian path `b ↦ (t ↦ b(F⁻¹ t))`
under planar Brownian motion from `z` is defined for every `z` and continuous in `z`. -/
theorem lbmLawContinuity_of_isValid {𝒮 : SpaceFillingSLEModel} :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ᵐ ω ∂S.P,
        ∃ hg : ∀ z : ℂ, AEMeasurable (lbmContinuousPath (S.clock ω)) (planarBrownianMotion z),
          Continuous fun z => planarBrownianPathLaw z (lbmContinuousPath (S.clock ω)) (hg z) :=
  lbmLawContinuity_of_stoppedHeatBound fun _ hγ hγ2 _ _ _ hS =>
    ae_stoppedHeatBound_of_isValid hγ hγ2 hS

end MatedCRT.FirstPass.Derived

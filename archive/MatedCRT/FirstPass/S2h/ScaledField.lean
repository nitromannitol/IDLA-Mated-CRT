import MatedCRT.FirstPass.S2h.PlateauCode
import MatedCRT.FirstPass.S2h.PlateauNull
import MatedCRT.FirstPass.S2h.PlateauTransfer
import MatedCRT.FirstPass.S2h.LogPathwise
import MatedCRT.FirstPass.S2h.LogScale
import MatedCRT.FirstPass.S2h.LogZero
import MatedCRT.FirstPass.S2l

/-!
# The scaling step `hscale` of the log-GFF zero law (fp-S2h, z1, round 20)

For a whole-plane log-GFF `h^ℂ` with `γ`-insertion LQG measure `μ` and `s > 0`, the dilated measure
`S ω = A_s(ω)^{-1} · (μ ω)(s^{-1} ·)` (`FrozenWholePlaneLQGScaling`, `FirstPass/S2l.lean`) has the law of `μ`, and it is the
LQG measure of the dilated whole-plane field (`affHC s 0`, `affHcirc s 0`, Duplantier-Sheffield scaling of the circle
averages). Applying HB Lemma 3.1 (`LeastSupersolutionMemStmt`) to this field gives the continuity of the least
supersolutions of `S ω` at every radius, so `S ω` lies in the good class `CodeGood` almost surely. The plateau event
then transfers by `plateau_prob_eq_of_momentCode`, and `hscale` follows from the pathwise identity
`mem_plateauRadii_smul_iff`.
-/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls
open scoped ENNReal

/-- The dilated measure `A_s^{-1} · μ(s^{-1} ·)` of the whole-plane LQG scaling law (the random measure of
`FrozenWholePlaneLQGScaling`), with `A_s = exp(γ(Q_γ log s + h_s(0)))`. -/
noncomputable def scaledLQG {Ω : Type*} (γ s : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (ω : Ω) :
    Measure ℂ :=
  ENNReal.ofReal (Real.exp (γ * (lqgQ γ * Real.log s + fieldCircleAverage γ (hcirc ω) s 0)))⁻¹ •
    Measure.map (fun x : ℂ => s⁻¹ • x) (μ ω)

/-- The dilated field is a whole-plane GFF and `scaledLQG` is its `γ`-insertion LQG measure (fp-S2h, z1, round 20).
The proof is the a.s. identity `hlim` of `firstPass_wholePlaneLQGScaling_of_coordinateRule` (S2l.lean:44-56), rerun
for the dilated field, together with the pointwise identification of the insertion-scaled measure (S2l.lean:79-93). -/
theorem isLQGMeasureOfField_scaledLQG (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hLQG : IsLQGMeasureOfField P γ γ hcirc μ) {s : ℝ} (hs : 0 < s) :
    IsWholePlaneGFF P (MatedCRT.Field.affHC s 0 hC hcirc) (MatedCRT.Field.affHcirc s 0 hcirc) ∧
      IsLQGMeasureOfField P γ γ (MatedCRT.Field.affHcirc s 0 hcirc) (scaledLQG γ s hcirc μ) := by
  have hna : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_of_nonneg hs.le]
  have hGFF'' : IsWholePlaneGFF P (MatedCRT.Field.affHC s 0 hC hcirc) (MatedCRT.Field.affHcirc s 0 hcirc) :=
    MatedCRT.Field.isWholePlaneGFF_affine hGFF hs 0
  have hDSae := hK γ γ hγ hγ2 (gamma_lt_lqgQ hγ hγ2) Ω P hC hcirc μ inferInstance hGFF hLQG (s : ℂ)
    (Complex.ofReal_ne_zero.mpr hs.ne') 0
  have hlim : ∀ᵐ ω ∂P, IsLQGLimit γ (fun ε z => fieldCircleAverage γ (MatedCRT.Field.affHcirc s 0 hcirc ω) ε z)
      (insertionScaledMeasure γ (insertionScaleConst γ γ s (hcirc ω)) ((μ ω).map fun x => x / (s : ℂ))) := by
    filter_upwards [hDSae, insertion_ae_continuousOn hGFF γ] with ω hω hcω
    simp only [hna, sub_zero, add_zero] at hω
    have hsh := isLQGLimit_insertion_shift (hc := hcirc ω) (m := (μ ω).map fun x => x / (s : ℂ)) hs hcω hω
    refine isLQGLimit_congr_pos ?_ hsh
    intro ε hε
    funext z
    exact (fieldCircleAverage_affHcirc_pos γ hs hcirc ω hε z).symm
  refine ⟨hGFF'', ?_⟩
  unfold IsLQGMeasureOfField IsLQGMeasure
  filter_upwards [hlim] with ω hω
  have hpt : scaledLQG γ s hcirc μ ω =
      insertionScaledMeasure γ (insertionScaleConst γ γ s (hcirc ω)) ((μ ω).map fun x => x / (s : ℂ)) := by
    have hscal : ENNReal.ofReal (Real.exp (γ * (lqgQ γ * Real.log s + fieldCircleAverage γ (hcirc ω) s 0)))⁻¹
        = ENNReal.ofReal (Real.exp (γ * -insertionScaleConst γ γ s (hcirc ω))) := by
      unfold insertionScaleConst
      congr 1
      rw [← Real.exp_neg]
      congr 1
      ring
    have hsc' : (μ ω).map (fun x : ℂ => x / (s : ℂ)) = (μ ω).map (fun x : ℂ => s⁻¹ • x) := by
      congr 1
      funext x
      rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
    unfold scaledLQG
    rw [hscal, insertionScaledMeasure, withDensity_const, hsc']
  rw [hpt]
  exact hω

/-- Local finiteness of the dilated measure on the closed integer discs. -/
theorem scaledLQG_closedBall_lt_top {ν : Measure ℂ} (hν : ∀ N : ℕ, ν (closedBall (0 : ℂ) (N : ℝ)) < ⊤)
    {s c : ℝ} (hs : 0 < s) (N : ℕ) :
    (ENNReal.ofReal c • Measure.map (fun x : ℂ => s⁻¹ • x) ν) (closedBall (0 : ℂ) (N : ℝ)) < ⊤ := by
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (continuous_const_smul _).measurable measurableSet_closedBall]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hsub : (fun x : ℂ => s⁻¹ • x) ⁻¹' closedBall (0 : ℂ) (N : ℝ) ⊆
      closedBall (0 : ℂ) ((⌈s * (N : ℝ)⌉₊ : ℕ) : ℝ) := by
    intro x hx
    rw [mem_preimage, mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)] at hx
    rw [mem_closedBall_zero_iff]
    rw [inv_mul_le_iff₀ hs] at hx
    exact hx.trans (Nat.le_ceil _)
  exact lt_of_le_of_lt (measure_mono hsub) (hν _)

/-- The code-level good event almost surely (HB Lemma 3.1 via `LeastSupersolutionMemStmt`, `.2.1`), given the local
finiteness of the integer discs. -/
theorem ae_codeGood_of_HB {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hHB : LeastSupersolutionMemStmt.{0}) (hgff : IsWholePlaneGFF P hC hcirc)
    (hlgm : IsLQGMeasureOfField P γ γ hcirc μ) (hfin : ∀ᵐ ω ∂P, ∀ N : ℕ, μ ω (closedBall (0 : ℂ) (N : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, CodeGood (μ ω) := by
  filter_upwards [hHB γ γ hγ hγ2 (gamma_lt_lqgQ hγ hγ2) Ω P hC hcirc μ hgff hlgm, hfin] with ω hω hωf
  refine ⟨hωf, fun N u hN hu => ?_⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  exact (hω u N hu hN' 0 (mem_ball_self hN')).2.1

/-- The good event of the dilated measure `scaledLQG γ s hcirc μ`, almost surely (through the dilated whole-plane
field of `isLQGMeasureOfField_scaledLQG`). -/
theorem ae_codeGood_scaledLQG {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hHB : LeastSupersolutionMemStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hlgm : IsLQGMeasureOfField P γ γ hcirc μ) {s : ℝ} (hs : 0 < s)
    (hfin : ∀ᵐ ω ∂P, ∀ N : ℕ, μ ω (closedBall (0 : ℂ) (N : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, CodeGood (scaledLQG γ s hcirc μ ω) := by
  obtain ⟨hGFF'', hLQG''⟩ := isLQGMeasureOfField_scaledLQG hK hγ hγ2 hgff hlgm hs
  have hfinS : ∀ᵐ ω ∂P, ∀ N : ℕ, scaledLQG γ s hcirc μ ω (closedBall (0 : ℂ) (N : ℝ)) < ⊤ :=
    hfin.mono fun ω hω N => scaledLQG_closedBall_lt_top hω hs N
  exact ae_codeGood_of_HB hγ hγ2 hHB hGFF'' hLQG'' hfinS

/-- **The scaling step `hscale` of the zero law (fp-S2h, z1, round 20).** For `s, r > 0`, the plateau event at `s r`
of `μ` and at `r` of the dilated measure coincide pathwise (`mem_plateauRadii_smul_iff`), and the dilated measure has the
law of `μ`, so the plateau probabilities agree (`plateau_prob_eq_of_momentCode`). -/
theorem plateau_scale_of_inputs {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF3 : FrozenDiskGreenNonnegCont)
    (hHB : LeastSupersolutionMemStmt.{0}) (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hmono : ClusterMonotoneStmt.{0}) (hcomp : ClusterCompatibilityStmt.{0})
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hlgm : IsLQGMeasureOfField P γ γ hcirc μ) {s r : ℝ} (hs : 0 < s)
    (hr : 0 < r) :
    P {ω | s * r ∈ plateauRadii (μ ω)} = P {ω | r ∈ plateauRadii (μ ω)} := by
  have hlt := gamma_lt_lqgQ hγ hγ2
  have hloc : ∀ N : ℕ, ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) (N : ℝ)) < ⊤ :=
    fun N => ae_measure_closedBall_lt_top hlgm N
  have hfin : ∀ᵐ ω ∂P, ∀ N : ℕ, μ ω (closedBall (0 : ℂ) (N : ℝ)) < ⊤ := ae_all_iff.2 hloc
  have hμ : AEMeasurable μ P := aemeasurable_lqgMeasure_of_wholePlane hgff hlgm
  have hlaw : P.map (scaledLQG γ s hcirc μ) = P.map μ :=
    (MatedCRT.FirstPass.S2l.firstPass_wholePlaneLQGScaling_of_coordinateRule hK) γ hγ hγ2 Ω P hC hcirc μ
      inferInstance hgff hlgm hμ s hs
  obtain ⟨hGFF'', hLQG''⟩ := isLQGMeasureOfField_scaledLQG hK hγ hγ2 hgff hlgm hs
  have hS : AEMeasurable (scaledLQG γ s hcirc μ) P := aemeasurable_lqgMeasure_of_wholePlane hGFF'' hLQG''
  have hCμ := ae_codeGood_of_HB hγ hγ2 hHB hgff hlgm hfin
  have hCS := ae_codeGood_scaledLQG hγ hγ2 hHB hK hgff hlgm hs hfin
  have hG : ∀ N : ℕ, 0 < N → ∀ x ∈ ball (0 : ℂ) (N : ℝ), x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) (N : ℝ)) 0 x :=
    fun N hN => (hF3 (N : ℝ) (by exact_mod_cast hN)).1
  have hGc : ∀ N : ℕ, 0 < N → ContinuousOn (greenFunction (ball (0 : ℂ) (N : ℝ)) 0) (ball (0 : ℂ) (N : ℝ) \ {0}) :=
    fun N hN => (hF3 (N : ℝ) (by exact_mod_cast hN)).2
  have hA : ∀ᵐ ω ∂P, r ∈ plateauRadii (μ ω) ↔ momentCode (μ ω) ∈ plateauCode r :=
    hCμ.mono fun ω h => mem_plateauRadii_iff_momentCode hG hGc h hr.le
  have hB : ∀ᵐ ω ∂P, r ∈ plateauRadii (scaledLQG γ s hcirc μ ω) ↔
      momentCode (scaledLQG γ s hcirc μ ω) ∈ plateauCode r :=
    hCS.mono fun ω h => mem_plateauRadii_iff_momentCode hG hGc h hr.le
  have hmonoA : ∀ᵐ ω ∂P, ClusterMonoAt (μ ω) := clusterMonoAt_of_stmt hmono hγ hγ2 hlt Ω P hC hcirc μ hgff hlgm
  have hcompA : ∀ᵐ ω ∂P, ClusterCompatAt (μ ω) :=
    ae_clusterCompatAt_of_stmt hcomp hγ hγ2 hlt Ω P hC hcirc μ hgff hlgm
  have hpath : ∀ᵐ ω ∂P, r ∈ plateauRadii (scaledLQG γ s hcirc μ ω) ↔ s * r ∈ plateauRadii (μ ω) := by
    filter_upwards [hmonoA, hcompA] with ω h1 h2
    unfold scaledLQG
    exact mem_plateauRadii_smul_iff (c := (Real.exp (γ * (lqgQ γ * Real.log s + fieldCircleAverage γ (hcirc ω) s 0)))⁻¹)
      (k := s) h1 h2 hs (inv_pos.2 (Real.exp_pos _)) r
  have h1 : P {ω | s * r ∈ plateauRadii (μ ω)} = P {ω | r ∈ plateauRadii (scaledLQG γ s hcirc μ ω)} :=
    measure_congr (Filter.eventuallyEqSet_iff.2 (hpath.mono fun ω h => h.symm))
  have h2 := plateau_prob_eq_of_momentCode hF1 μ (scaledLQG γ s hcirc μ) hμ hS hlaw r hA hB
  exact h1.trans h2

/-- **The zero law at radius `1/2` (HalfPlateauNullStep), from the frozen and cited inputs (fp-S2h, z1, round 20).** -/
theorem halfPlateauNull_of_inputs (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF3 : FrozenDiskGreenNonnegCont)
    (hHB : LeastSupersolutionMemStmt.{0}) (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hmono : ClusterMonotoneStmt.{0}) (hcomp : ClusterCompatibilityStmt.{0}) : HalfPlateauNullStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hP hgff hlgm
  have hloc : ∀ N : ℕ, ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) (N : ℝ)) < ⊤ :=
    fun N => ae_measure_closedBall_lt_top hlgm N
  have hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P :=
    fun φ hφ _ => (measurable_integral_measure_real hφ.measurable).comp_aemeasurable
      (aemeasurable_lqgMeasure_of_wholePlane hgff hlgm)
  have hscale : ∀ s r : ℝ, 0 < s → 0 < r → P {ω | s * r ∈ plateauRadii (μ ω)} = P {ω | r ∈ plateauRadii (μ ω)} :=
    fun s r hs hr => plateau_scale_of_inputs hF1 hF3 hHB hK hmono hcomp hγ hγ2 hgff hlgm hs hr
  exact plateauRadii_zero_of_HB hγ hγ2 hF1 hF3 hHB hgff hlgm hloc hmeas hscale (1 / 2) (by norm_num)

end MatedCRT

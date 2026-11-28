import MatedCRT.Defs.Setting
import MatedCRT.FirstPass.Derived.CouplingNormalizedRadialReplacement
import LatticeProb.LQG.ConeSpliceFieldDecomposition
import LatticeProb.LQG.ConeSplicePairing
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower3
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities

/-!
# The quantum cone as a normalized whole-plane GFF minus `γ log |·|` plus a continuous function

Step 3 of the localization in the proof of the coordinate change of the LQG measure for all inverse charts
(`LQGMeasureChartStmt`): the `γ`-quantum cone `h = coneField X (coneRadial γ γ B B')` of a mating-of-trees coupling
(Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating of trees*, arXiv:1409.7055, Definition 4.10)
is coupled with a whole-plane GFF `G` normalized by `G_1(0) = 0` by keeping the lateral part of `X` and the inward
radial Brownian motion `B`, and using the outward radial path of `X` itself for the outward radial part of `G`. Then
`h = G − γ log |·| + v` with `v` continuous and `v = 0` on the closed unit disc: inside the unit disc the radial
part of `h` is `B_t + γ t` and that of `G` is `B_t` (`t = −log |z|`); outside, both radial paths are continuous and
vanish at radius `1`.

* `exists_normalizedWPGFF_coneField_eq`: for a mating-of-trees coupling and `0 < γ < 2`, there are a measurable
  normalized whole-plane GFF `G` and a measurable `v : Ω → C(ℂ, ℝ)` vanishing on the closed unit disc with, almost
  surely, `coneField X (coneRadial γ γ B B') = G − γ log |·| + v`.
* `MatedCRTEnv.IsValid.exists_hC_eq_normalizedWPGFF_sub_log_add`: the same for the field `S.hC` of a valid
  environment.

The normalized whole-plane GFF is `LatticeProb.LQG.IsWholePlaneGFF.normalized_replField_twoSided` (through
`MatedCRT.Sec1.exists_normalized_radial_replacement_witnesses_of_coupling`); the decomposition of the cone field is
`LatticeProb.LQG.coneFieldOf_eq_replField_add_radial_difference`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace MatedCRT

namespace LQGMeasureChart

open MatedCRTHarmonic MatedCRTHarmonic.GMCFacts

/-- The path `u ↦ b'(u) + (Q − γ) u` whose part after its last zero is the outward radial part of the `γ`-quantum
cone (Duplantier–Miller–Sheffield (2014), Definition 4.10 and Remark 4.4). -/
def coneOuterPath (γ : ℝ) (b' : ℝ≥0 → ℝ) (u : ℝ) : ℝ :=
  b' u.toNNReal + (CellScaling.lqgQ γ - γ) * u

/-- The continuous correction of the cone splice, at `t = −log r`: for `t ≤ 0` the outward radial path of the cone
minus the outward radial path `s ↦ r(s) − r(0)` of the splice, minus `γ t` and minus the value `c(ℓ)` of the path at
its last zero (which is `0` when `b'(0) = 0`); for `t ≥ 0` it is `0`. -/
def coneSpliceCorrection (γ : ℝ) (b' : ℝ≥0 → ℝ) (r : C(ℝ, ℝ)) (t : ℝ) : ℝ :=
  coneOuterPath γ b' (CellScaling.lastZeroR (coneOuterPath γ b') - min t 0) + CellScaling.lqgQ γ * min t 0 -
    (r (min t 0) - r 0) - γ * min t 0 - coneOuterPath γ b' (CellScaling.lastZeroR (coneOuterPath γ b'))

/-- The path `s ↦ r(−s)`, `s ≥ 0`: the outward radial path of a splice. -/
def reflectPath (r : C(ℝ, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun t => r (-(t : ℝ)), r.continuous.comp (by fun_prop)⟩

theorem reflectPath_apply (r : C(ℝ, ℝ)) (t : ℝ≥0) : reflectPath r t = r (-(t : ℝ)) :=
  rfl

theorem continuous_coneOuterPath (γ : ℝ) {b' : ℝ≥0 → ℝ} (hb' : Continuous b') :
    Continuous (coneOuterPath γ b') :=
  (hb'.comp continuous_real_toNNReal).add (continuous_const.mul continuous_id)

theorem coneOuterPath_zero (γ : ℝ) {b' : ℝ≥0 → ℝ} (hb' : b' 0 = 0) : coneOuterPath γ b' 0 = 0 := by
  simp [coneOuterPath, hb']

/-- A continuous path vanishing at `0` vanishes at its last zero (`sSup {s ≥ 0 | c s = 0}`, junk `0` if unbounded). -/
theorem apply_lastZeroR_eq_zero {c : ℝ → ℝ} (hc : Continuous c) (h0 : c 0 = 0) :
    c (CellScaling.lastZeroR c) = 0 := by
  unfold CellScaling.lastZeroR
  by_cases hb : BddAbove {s : ℝ | 0 ≤ s ∧ c s = 0}
  · have hZ : IsClosed {s : ℝ | 0 ≤ s ∧ c s = 0} :=
      (isClosed_le continuous_const continuous_id).inter (isClosed_eq hc continuous_const)
    exact (hZ.csSup_mem ⟨0, le_rfl, h0⟩ hb).2
  · rw [Real.sSup_of_not_bddAbove hb]
    exact h0

theorem coneSpliceCorrection_of_nonneg (γ : ℝ) (b' : ℝ≥0 → ℝ) (r : C(ℝ, ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    coneSpliceCorrection γ b' r t = 0 := by
  simp only [coneSpliceCorrection, min_eq_right ht, sub_zero, mul_zero, add_zero, sub_self]

theorem coneSpliceCorrection_of_nonpos (γ : ℝ) (b' : ℝ≥0 → ℝ) (r : C(ℝ, ℝ)) {t : ℝ} (ht : t ≤ 0) :
    coneSpliceCorrection γ b' r t =
      coneOuterPath γ b' (CellScaling.lastZeroR (coneOuterPath γ b') - t) + CellScaling.lqgQ γ * t -
        (r t - r 0) - γ * t - coneOuterPath γ b' (CellScaling.lastZeroR (coneOuterPath γ b')) := by
  simp only [coneSpliceCorrection, min_eq_left ht]

theorem continuous_coneSpliceCorrection (γ : ℝ) {b' : ℝ≥0 → ℝ} (hb' : Continuous b') (r : C(ℝ, ℝ)) :
    Continuous (coneSpliceCorrection γ b' r) := by
  have hP := continuous_coneOuterPath γ hb'
  show Continuous fun t => coneOuterPath γ b' (CellScaling.lastZeroR (coneOuterPath γ b') - min t 0) +
    CellScaling.lqgQ γ * min t 0 - (r (min t 0) - r 0) - γ * min t 0 -
      coneOuterPath γ b' (CellScaling.lastZeroR (coneOuterPath γ b'))
  fun_prop

/-- The continuous function `z ↦ coneSpliceCorrection γ b' r (−log (max |z| 1))`. -/
def coneSpliceCorrectionMap (γ : ℝ) (b' : C(ℝ≥0, ℝ)) (r : C(ℝ, ℝ)) : C(ℂ, ℝ) :=
  ⟨fun z => coneSpliceCorrection γ b' r (-Real.log (max ‖z‖ 1)),
    (continuous_coneSpliceCorrection γ b'.continuous r).comp
      ((continuous_norm.max continuous_const).log fun z =>
        (zero_lt_one.trans_le (le_max_right ‖z‖ 1)).ne').neg⟩

theorem coneSpliceCorrectionMap_apply (γ : ℝ) (b' : C(ℝ≥0, ℝ)) (r : C(ℝ, ℝ)) (z : ℂ) :
    coneSpliceCorrectionMap γ b' r z = coneSpliceCorrection γ b' r (-Real.log (max ‖z‖ 1)) :=
  rfl

theorem coneSpliceCorrectionMap_of_norm_le (γ : ℝ) (b' : C(ℝ≥0, ℝ)) (r : C(ℝ, ℝ)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    coneSpliceCorrectionMap γ b' r z = 0 := by
  rw [coneSpliceCorrectionMap_apply, max_eq_right hz, Real.log_one, neg_zero,
    coneSpliceCorrection_of_nonneg γ b' r le_rfl]

/-- The correction is measurable in the paths, for paths continuous at every sample. -/
theorem measurable_coneSpliceCorrection {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) {b : ℝ≥0 → Ω → ℝ}
    (hbm : ∀ t, Measurable (b t)) (hbc : ∀ ω, Continuous fun t => b t ω) {r : Ω → C(ℝ, ℝ)} (hr : Measurable r)
    (t : ℝ) : Measurable fun ω => coneSpliceCorrection γ (fun s => b s ω) (r ω) t := by
  have hpc : ∀ ω, Continuous (coneOuterPath γ fun s => b s ω) := fun ω => continuous_coneOuterPath γ (hbc ω)
  have hpm : ∀ u, Measurable fun ω => coneOuterPath γ (fun s => b s ω) u := fun u =>
    (hbm _).add_const _
  have hℓ : Measurable fun ω => CellScaling.lastZeroR (coneOuterPath γ fun s => b s ω) :=
    QuantumZipper.WedgeMeas.measurable_lastZero hpc hpm
  have hJ : Measurable fun p : ℝ × Ω => coneOuterPath γ (fun s => b s p.2) p.1 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun u ω => coneOuterPath γ (fun s => b s ω) u) hpc hpm
  have hA : Measurable fun ω => coneOuterPath γ (fun s => b s ω)
      (CellScaling.lastZeroR (coneOuterPath γ fun s => b s ω) - min t 0) :=
    hJ.comp ((hℓ.sub_const _).prodMk measurable_id)
  have hC : Measurable fun ω => coneOuterPath γ (fun s => b s ω)
      (CellScaling.lastZeroR (coneOuterPath γ fun s => b s ω)) :=
    hJ.comp (hℓ.prodMk measurable_id)
  have hr' : ∀ s, Measurable fun ω => r ω s := fun s => (ContinuousMap.measurable_eval s).comp hr
  unfold coneSpliceCorrection
  exact (((hA.add_const _).sub ((hr' _).sub (hr' _))).sub_const _).sub hC

theorem coneRadial_eq_coneOuterPath_of_neg (γ : ℝ) (b b' : ℝ≥0 → ℝ) {t : ℝ} (ht : t < 0) :
    CellScaling.coneRadial γ γ b b' t =
      coneOuterPath γ b' (CellScaling.lastZeroR (coneOuterPath γ b') - t) + CellScaling.lqgQ γ * t := by
  rw [CellScaling.coneRadial, ite_eq_right (not_le.2 ht)]
  rfl

/-- **The pointwise splice identity.** If `b(0) = b'(0) = 0`, `b'` is continuous and `W = b`, the radial profile of
the cone minus that of the splice of `W` (inside) with the outward path `s ↦ r(−s)` (outside) is
`−γ log |z| + coneSpliceCorrection γ b' r (−log (max |z| 1))`. -/
theorem coneRadial_sub_radialW_twoSided (γ : ℝ) {b b' : ℝ≥0 → ℝ} (hb'c : Continuous b') (hb'0 : b' 0 = 0)
    (hb0 : b 0 = 0) {W : C(ℝ≥0, ℝ)} (hW : ∀ t, W t = b t) (r : C(ℝ, ℝ)) (z : ℂ) :
    CellScaling.coneRadial γ γ b b' (-Real.log ‖z‖) -
        radialW (twoSided W (reflectPath r)) z =
      -γ * Real.log ‖z‖ + coneSpliceCorrection γ b' r (-Real.log (max ‖z‖ 1)) := by
  rw [radialW, twoSided_apply]
  rcases le_or_gt ‖z‖ 1 with hz | hz
  · have ht : 0 ≤ -Real.log ‖z‖ := neg_nonneg.2 (Real.log_nonpos (norm_nonneg z) hz)
    rw [max_eq_right hz, Real.log_one, neg_zero, coneSpliceCorrection_of_nonneg γ b' r le_rfl,
      Real.toNNReal_of_nonpos (neg_nonpos.2 ht), sub_self, add_zero, hW, hW, hb0, sub_zero,
      coneRadial_of_nonneg γ γ b b' ht]
    ring
  · have ht : -Real.log ‖z‖ < 0 := neg_lt_zero.2 (Real.log_pos hz)
    rw [max_eq_left hz.le, coneSpliceCorrection_of_nonpos γ b' r ht.le, Real.toNNReal_of_nonpos ht.le, sub_self,
      zero_add, coneRadial_eq_coneOuterPath_of_neg γ b b' ht,
      apply_lastZeroR_eq_zero (continuous_coneOuterPath γ hb'c) (coneOuterPath_zero γ hb'0)]
    rw [reflectPath_apply, reflectPath_apply, Real.coe_toNNReal _ (neg_nonneg.2 ht.le), neg_neg, NNReal.coe_zero,
      neg_zero]
    ring

/-- The distribution of `−γ log |·| + v` for a continuous `v`. -/
theorem ofFunC_eq_neg_smul_log_add (γ : ℝ) (v : C(ℂ, ℝ)) {g : ℂ → ℝ}
    (hg : ∀ z, g z = -γ * Real.log ‖z‖ + v z) :
    MoTPort.ofFunC g = (-γ) • MatedCRTHarmonic.MatedCRT.ofFunC (fun z => Real.log ‖z‖) + LQGMetric.ofCont v := by
  have e : g = (-γ) • (fun z : ℂ => Real.log ‖z‖) + ⇑v := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hg z
  have hlog : LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) volume := QuantumZipper.K3.locallyIntegrable_log_norm
  have h1 : LocallyIntegrableOn ((-γ) • fun z : ℂ => Real.log ‖z‖) (⊤ : TopologicalSpace.Opens ℂ) volume := by
    rw [TopologicalSpace.Opens.coe_top]
    exact (hlog.smul (-γ)).locallyIntegrableOn Set.univ
  have h2 : LocallyIntegrableOn ⇑v (⊤ : TopologicalSpace.Opens ℂ) volume := by
    rw [TopologicalSpace.Opens.coe_top]
    exact v.continuous.locallyIntegrable.locallyIntegrableOn Set.univ
  rw [e]
  show Distribution.ofFun ⊤ ((-γ) • (fun z : ℂ => Real.log ‖z‖) + ⇑v) volume ⊤ = _
  rw [Distribution.ofFun_add h1 h2, Distribution.ofFun_smul]
  rfl

/-- **The cone field as a splice minus `γ log |·|` plus a continuous function**, for one sample: if
`b(0) = b'(0) = 0`, `b'` is continuous, `W = b`, and both radial profiles are locally integrable, then
`coneField X (coneRadial γ γ b b')` is the radial replacement of `X` by the splice of `W` (inside) with `s ↦ r(−s)`
(outside), minus `γ log |·|`, plus `coneSpliceCorrectionMap γ b' r`. -/
theorem coneField_eq_replField_sub_log_add (γ : ℝ) (X : LQGMetric.DistC) {b b' : ℝ≥0 → ℝ} {c : C(ℝ≥0, ℝ)}
    (hc : ⇑c = b') (hb'0 : b' 0 = 0) (hb0 : b 0 = 0) {W : C(ℝ≥0, ℝ)} (hW : ∀ t, W t = b t) (r : C(ℝ, ℝ))
    (hA : LocallyIntegrable (fun z : ℂ => CellScaling.coneRadial γ γ b b' (-Real.log ‖z‖)) volume)
    (hw : LocallyIntegrable (radialW (twoSided W (reflectPath r))) volume) :
    MatedCRTHarmonic.MatedCRT.coneField X (MatedCRTHarmonic.MatedCRT.coneRadial γ γ b b') =
      replField (fun _ : Unit => X) (fun _ => twoSided W (reflectPath r)) () -
        γ • MatedCRTHarmonic.MatedCRT.ofFunC (fun z => Real.log ‖z‖) +
          LQGMetric.ofCont (coneSpliceCorrectionMap γ c r) := by
  subst hc
  rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling, MesoModel.FrozenIdentities.coneRadial_eq_cellScaling,
    show CellScaling.coneField X (CellScaling.coneRadial γ γ b ⇑c) = CellScaling.coneFieldOf γ X b ⇑c from rfl,
    LatticeProb.LQG.coneFieldOf_eq_replField_add_radial_difference γ X b ⇑c _ hA hw,
    ofFunC_eq_neg_smul_log_add γ (coneSpliceCorrectionMap γ c r)
      (g := fun z : ℂ => CellScaling.coneRadial γ γ b ⇑c (-Real.log ‖z‖) - radialW (twoSided W (reflectPath r)) z)
      fun z => coneRadial_sub_radialW_twoSided γ c.continuous hb'0 hb0 hW r z,
    neg_smul, sub_eq_add_neg, add_assoc]

end LQGMeasureChart

open LQGMeasureChart MatedCRTHarmonic MatedCRTHarmonic.GMCFacts

/-- **The quantum cone as a normalized whole-plane GFF minus `γ log |·|` plus a continuous function.** For a
mating-of-trees coupling with `0 < γ < 2`, there are a measurable whole-plane GFF `G` with `G_1(0) = 0` and a
measurable `v : Ω → C(ℂ, ℝ)` vanishing on the closed unit disc such that almost surely
`coneField X (coneRadial γ γ B B') = G − γ log |·| + v`. -/
theorem exists_normalizedWPGFF_coneField_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ (G : Ω → LQGMetric.DistC) (v : Ω → C(ℂ, ℝ)), Measurable G ∧ LQGMetric.IsNormalizedWPGFF G P ∧
      Measurable v ∧ (∀ ω z, ‖z‖ ≤ 1 → v ω z = 0) ∧
      ∀ᵐ ω ∂P, MatedCRTHarmonic.MatedCRT.coneField (X ω)
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) =
        G ω - γ • MatedCRTHarmonic.MatedCRT.ofFunC (fun z => Real.log ‖z‖) + LQGMetric.ofCont (v ω) := by
  have := D.isProbabilityMeasure
  obtain ⟨R, W, -, hRm, -, -, -, hW, -, -, -, -, hG, -⟩ :=
    MatedCRT.Sec1.exists_normalized_radial_replacement_witnesses_of_coupling D hγ hγ2
  obtain ⟨Bc, hBcm, hBcc, hBcae⟩ := QuantumZipper.WedgeRes.exists_good_version D.bm_B'
  have hBcm' : ∀ t, Measurable (Bc t) := fun t => hBcm.comp (measurable_const.prodMk measurable_id)
  have hvm : Measurable fun ω => coneSpliceCorrectionMap γ ⟨fun s => Bc s ω, hBcc ω⟩ (R (X ω)) := by
    refine ContinuousMap.measurable_iff_eval.2 fun z => ?_
    simp only [coneSpliceCorrectionMap_apply, ContinuousMap.coe_mk]
    exact measurable_coneSpliceCorrection γ hBcm' hBcc (hRm.comp D.gff.measurable) _
  refine ⟨replField X fun ω => twoSided (W ω) (reflectPath (R (X ω))),
    fun ω => coneSpliceCorrectionMap γ ⟨fun s => Bc s ω, hBcc ω⟩ (R (X ω)), hG.1.measurable, hG, hvm,
    fun ω z hz => coneSpliceCorrectionMap_of_norm_le γ _ _ hz, ?_⟩
  -- local integrability of the radial profile of the cone
  have hBB' : IndepFun (QuantumZipper.pathOf B) (QuantumZipper.pathOf B') P := D.indep_cone.2
  have hAc := LQGCone.isConeProcess_motConeRadial (γ := γ) (α := γ) D.bm_B D.bm_B' hBB'
  have hLI : ∀ᵐ ω ∂P, LocallyIntegrable
      (fun z : ℂ => CellScaling.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω) (-Real.log ‖z‖)) volume := by
    filter_upwards [MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hAc] with ω hω
    refine hω.congr (Filter.Eventually.of_forall fun z => ?_)
    have he := LQGCone.coneRadial_eq_Q_add_motConeRadial γ γ (fun t => B t ω) (fun t => B' t ω)
      (-Real.log ‖z‖)
    change CellScaling.coneRadial γ γ _ _ _ = QuantumZipper.Qc γ * _ + _ at he
    exact he.symm
  filter_upwards [hLI,
    LatticeProb.LQG.ae_locallyIntegrable_radialW_twoSided D.bm_B W (fun ω => reflectPath (R (X ω))) hW, hW,
    D.bm_B.eval_zero_ae_eq_zero, hBcae, D.bm_B'.eval_zero_ae_eq_zero] with ω hA hw hWω hB0 hBc hB'0
  exact coneField_eq_replField_sub_log_add γ (X ω) (c := ⟨fun s => Bc s ω, hBcc ω⟩)
    (funext fun s => hBc s) hB'0 hB0 hWω (R (X ω)) hA hw

/-- **The field of a valid environment as a normalized whole-plane GFF minus `γ log |·|` plus a continuous
function.** For a valid environment with `0 < γ < 2` there are a measurable whole-plane GFF `G` with `G_1(0) = 0`
and a measurable `v : Ω → C(ℂ, ℝ)` vanishing on the closed unit disc such that almost surely the pairings of `h`
with test functions are those of `G − γ log |·| + v`. -/
theorem MatedCRTEnv.IsValid.exists_hC_eq_normalizedWPGFF_sub_log_add {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ (G : Ω → LQGMetric.DistC) (v : Ω → C(ℂ, ℝ)), Measurable G ∧ LQGMetric.IsNormalizedWPGFF G S.P ∧
      Measurable v ∧ (∀ ω z, ‖z‖ ≤ 1 → v ω z = 0) ∧
      ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC,
        S.hC ω ⇑φ =
          (G ω - γ • MatedCRTHarmonic.MatedCRT.ofFunC (fun z => Real.log ‖z‖) + LQGMetric.ofCont (v ω)) φ := by
  obtain ⟨X, _, _, B, B', _, _, _, _, _, _, hD, hae⟩ := hS.matingOfTrees
  obtain ⟨G, v, hGm, hG, hvm, hv0, hGae⟩ := exists_normalizedWPGFF_coneField_eq hD hγ hγ2
  refine ⟨G, v, hGm, hG, hvm, hv0, ?_⟩
  filter_upwards [hae, hGae] with ω hω hGω φ
  rw [hω.2 φ, hGω]

end MatedCRT

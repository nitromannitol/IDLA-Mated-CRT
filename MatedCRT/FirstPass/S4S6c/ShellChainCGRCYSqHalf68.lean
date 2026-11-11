import MatedCRT.FirstPass.S4S6c.ShellChainCGRCYSq68
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCY68
import MatedCRT.FirstPass.S4S6c.Closed6x68Y
import MatedCRT.FirstPass.S4S6c.CGRCYSqInst68

/-!
# The square chain at the half exponent: the guard, `hU` and the 6.7/6.8/6.9 closures

The consumers of the guard (`GuardProbStmt`, S6e/Uniform.lean:132; `UniformConstantOrderLowerBoundStmt`, S6d.lean:96;
the faithful headers S6d.lean:41, 57, 75) state the radius clause `10 * ε ^ ω₀' ≤ r` with an existential witness `ω₀'`.
Here `ω₀' := ω₀ / 2`, where `ω₀` is the internal exponent of the square chain. For `0 < ε ≤ 1` and
`10 * ε ^ (ω₀ / 2) ≤ r` one has `10 * ε ^ ω₀ ≤ r` and `4 * ε ^ ω₀ ≤ r ^ 2` (`radius_premises_of_half`): with
`a = ε ^ (ω₀ / 2) ≤ 1`, `ε ^ ω₀ = a ^ 2 ≤ a`, and `r ≥ 10 a` gives `r ^ 2 ≥ 100 a ^ 2`.

* `guardProbStmtCGRCYSq_of_chain`: copy of `guardProbStmtCGRCY_of_chainCGRCY` (ShellChainCGRCY68.lean:172) with the
  square chain `ShellChainCGRCYSqStmt`, the witness `ω₀ / 2`, and the event index restricted to `ε ≤ 1`.
* `hU_top_cgRCYSq`, `firstPass_6_7/8/9_of_hOneYSq`: the closures of Closed6x68Y.lean:39, 54, 70 with `hOneYSq` in place of `hOneY`.
* `firstPass_6_7/8/9_sq`: the same closures with `hOneYSq` discharged by `CGRCYSqInst68.shellOneTestOrderAeCGRCYSq_holds`.

Terminology: Armstrong-Kuusi-Mourrat (good annuli, shell order), Duplantier-Sheffield (LQG measure), Armitage-Gardiner (balls).
-/

open MeasureTheory Filter Set HarmonicBalls Metric ProbabilityTheory
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68CGRCYSqHalf

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10
open MatedCRT.Lemma68ConstOrder DyadicCutoff68 Lemma68Window
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellHoneInst
open MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- **The half-exponent radius premises.** For `0 < ε ≤ 1` and `10 * ε ^ (ω₀ / 2) ≤ r` one has
`10 * ε ^ ω₀ ≤ r` and `4 * ε ^ ω₀ ≤ r ^ 2`. With `a = ε ^ (ω₀ / 2)`: `ε ^ ω₀ = a ^ 2 ≤ a ≤ 1`. -/
theorem radius_premises_of_half {ε ω₀ r : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hω₀ : 0 < ω₀)
    (hr : 10 * ε ^ (ω₀ / 2) ≤ r) : 10 * ε ^ ω₀ ≤ r ∧ 4 * ε ^ ω₀ ≤ r ^ 2 := by
  have ha0 : 0 < ε ^ (ω₀ / 2) := Real.rpow_pos_of_pos hε0 _
  have ha1 : ε ^ (ω₀ / 2) ≤ 1 := Real.rpow_le_one hε0.le hε1 (by linarith)
  have hsq : ε ^ ω₀ = (ε ^ (ω₀ / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le]
    congr 1
    push_cast
    ring
  rw [hsq]
  have hr0 : 0 ≤ 10 * ε ^ (ω₀ / 2) := by positivity
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left ha1 ha0.le]
  · nlinarith [mul_le_mul hr hr hr0 (by linarith)]

/-- **`GuardProbStmt` from the square chain at the half exponent.** Copy of
`guardProbStmtCGRCY_of_chainCGRCY` (ShellChainCGRCY68.lean:172) with `hChain : ShellChainCGRCYSqStmt 𝒮`. The witness is
`ω₀ / 2`; the mesh, Green and exit events are those at the internal `ω₀`. The almost sure event is restricted to
`ε ≤ min (shellEps0ZCG) (min εG 1)`, so that `ε ≤ 1` holds in the radius premise (`radius_premises_of_half`). -/
theorem guardProbStmtCGRCYSq_of_chain (𝒮 : SpaceFillingSLEModel)
    (hMesh : Lemma68CGRCY.CountingMeshEventsHiStmt 𝒮) (hVol : Lemma68CGRCY.FieldVolCutoffStmt 𝒮)
    (hChain : Lemma68CGRCYSq.ShellChainCGRCYSqStmt 𝒮) :
    Lemma68Uniform.GuardProbStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ζ, hζ0, hζ1, ω₀, α, β, hω₀, hωα, hα0, hβ0, hωζ, hexp1, hexp2, ωG, hHi, hmesh⟩ := hMesh γ hγ0 hγ2
  refine ⟨ω₀ / 2, half_pos hω₀, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨CG, hCG, _, _, hPH⟩ := hmesh ρ hρ0 hρ1
  obtain ⟨_, _, _, _, hPHm⟩ := hmesh ((1 + ρ) / 2) (by linarith) (by linarith)
  have hαρ : ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ' C) := by
    intro ρ' h0 h1
    obtain ⟨_, _, CE', hCE', hPH'⟩ := hmesh ρ' h0 h1
    exact ⟨CE', hCE', fun Ω _ S hS => (hPH' Ω S hS).2.2.2.1⟩
  obtain ⟨CE, hCE, hPHc⟩ := Lemma68ExitRhoCell.polyHighProb_exitTimeEvent68_common_CE 𝒮 hαρ ρ hρ0 hρ1
  obtain ⟨q0, εG, hq0, hεG, hq1, hchain⟩ :=
    hChain γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ0 hζ0 hζ1 hρ0 hρ1 ωG hHi
  have hrA : 0 < Lemma68Cutoff.rAmp q0 ζ := Lemma68Cutoff.rAmp_pos hq0 hζ0
  have hcN : 0 < countConst ζ := countConst_pos ζ
  obtain ⟨r_amp, hra0, hra1, hbd⟩ :=
    constant_order_conclusion (c := countConst ζ * q0) (ζ := ζ) (mul_pos hcN hq0) hζ0
  obtain ⟨Rc, hRc0, hRc⟩ := exists_radius_cutoff_gap hρ0 hρ1 hζ0
  have hR0 : 0 < min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)) :=
    lt_min (by linarith) (lt_min hrA (lt_min hra0 hRc0))
  refine ⟨min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)), ζ, 2, 9 * q0, q0, hR0,
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), hζ0, hζ1, hq0, hq1,
    by ring, by linarith, by linarith, by norm_num,
    shellS1CG γ CG, shellS1CG_pos γ CG, shellS1CG_lt_one γ CG hCG, ?_⟩
  intro s₀ hs₀ hs₁ Ω _ S hS
  set R : ℝ := min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)) with hRdef
  have hRA : R ≤ Lemma68Cutoff.rAmp q0 ζ := (min_le_right _ _).trans (min_le_left _ _)
  have hRρ : R ≤ ρ / 4 := min_le_left _ _
  have hRr' : R ≤ r_amp := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRRc : R ≤ Rc := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hR1 : R ≤ 1 := hRρ.trans (by linarith)
  have hRr : ∀ r : ℝ, 0 < r → r ≤ R →
      Real.exp (-(countConst ζ * q0 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) ≤ 1 / 2 :=
    fun r hr hrle => hbd r hr (hrle.trans hRr')
  obtain ⟨hGp, hGH, _, _, hKp⟩ := hPH Ω S hS
  obtain ⟨hEp, hEr⟩ := hPHc Ω S hS
  have hCpm : HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) :=
    (hPHm Ω S hS).2.2.1
  obtain ⟨tVol, htVm, htVpos, htVae⟩ := hVol γ hγ0 hγ2 Ω S hS
  obtain ⟨Ew, hEwm, hEwp, hpt⟩ :=
    hchain R hR0 hRρ hRA (hRc R hR0 hRRc) s₀ hs₀ hs₁ Ω S hS hGp hGH hCpm hEp hEr hKp
  obtain ⟨dd0, hdd0m, hdd0pos, _, hdd0⟩ := window_cutoff (F := S.fieldSigma) S.P Ew hEwm hEwp
  have hcapm : Measurable[S.fieldSigma] (fun ω => (tVol ω / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ))) :=
    (htVm.div_const _).pow_const _
  have hcappos : ∀ ω, 0 < (tVol ω / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)) := fun ω =>
    Real.rpow_pos_of_pos (div_pos (htVpos ω) (by positivity)) _
  have hEX : ProbTendsToOne S.P (fun ε => countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε ∩
      exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε ∩ greenLowEvent68 S ωG ρ CG ε) :=
    ((probTendsToOne_countingMeshEventR hGp hCpm hEp hKp).inter (probTendsToOne_of_polyHighProb hEr)).inter
      (probTendsToOne_of_polyHighProb hGH)
  have hGae : ∀ᵐ ω ∂S.P, ω ∈ goodField S Ew dd0 ∧ ∀ δ : ℝ, 0 < δ → δ < tVol ω → ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ) := by
    filter_upwards [Lemma68Guard.ae_escapes_of_valid hS,
      Lemma68Guard.ae_finiteExit_of_valid hγ0 hγ2 hS, hdd0, htVae] with ω h1 h2 h3 h4
    exact ⟨⟨h1, h2, h3⟩, h4⟩
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ω ∈ goodField S Ew dd0 ∧ ∀ δ : ℝ, 0 < δ → δ < tVol ω →
      ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ)} := ⟨_, rfl⟩
  have hG : S.P Gᶜ = 0 := by rw [hGdef]; exact ae_iff.1 hGae
  have hGmem : ∀ ω, ω ∈ G ↔ (ω ∈ goodField S Ew dd0 ∧ ∀ δ : ℝ, 0 < δ → δ < tVol ω →
      ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ)) := by
    intro ω; subst hGdef; exact Iff.rfl
  have he0 : 0 < shellEps0ZCG γ α ω₀ ζ CG := shellEps0ZCG_pos γ α ω₀ ζ CG
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ → Set Ω, E = fun ε => if ε ≤ min (shellEps0ZCG γ α ω₀ ζ CG) (min εG 1) then
      (countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε ∩
        exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε) ∩ greenLowEvent68 S ωG ρ CG ε
      else ∅ := ⟨_, rfl⟩
  have hEp' : ProbTendsToOne S.P E :=
    probTendsToOne_congr_small (lt_min he0 (lt_min hεG one_pos)) hEX
      (fun ε _ hle => by simp only [hEdef, hle, ↓reduceIte])
  have hpt' : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε ∩ G →
      ∀ r : ℝ, 10 * ε ^ (ω₀ / 2) ≤ r →
        r ≤ min R (min (dd0 ω) ((tVol ω / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)))) →
        ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
          ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
            Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N := by
    intro ε hε
    by_cases hle : ε ≤ min (shellEps0ZCG γ α ω₀ ζ CG) (min εG 1)
    · have hle1 : ε ≤ shellEps0ZCG γ α ω₀ ζ CG := hle.trans (min_le_left _ _)
      have hle2 : ε ≤ εG := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hle3 : ε ≤ 1 := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
      filter_upwards [hpt ε hε hle1 hle2] with ω hω
      rintro ⟨hωE, hωG'⟩ r hr hrd i hadm
      have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
      obtain ⟨hr10, hr4⟩ := radius_premises_of_half hε hle3 hω₀ hr
      have hωm' : ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε ∧
          ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε ∧
          ω ∈ greenLowEvent68 S ωG ρ CG ε := by
        simp only [hEdef, hle, ↓reduceIte] at hωE
        exact ⟨hωE.1.1, hωE.1.2, hωE.2⟩
      obtain ⟨hGfs, hGvol⟩ := (hGmem ω).1 hωG'
      have hrR : r ≤ R := hrd.trans (min_le_left _ _)
      have hrd0 : r ≤ dd0 ω := hrd.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hrc : r ≤ (tVol ω / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)) :=
        hrd.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hvol : LICGRCY68.VolReady68 S γ ζ r ω := ⟨tVol ω, htVpos ω, hGvol, hrc⟩
      exact hω hωm'.1 hωm'.2.1 hωm'.2.2 hGfs.1 hGfs.2.1 r hr10 hr4 hrR (hGfs.2.2 r hr0 hrd0) hvol i hadm
    · refine Filter.Eventually.of_forall fun ω hω => ?_
      exact absurd hω.1 (by simp only [hEdef, hle, ↓reduceIte, Set.mem_empty_iff_false, not_false_eq_true])
  refine ⟨fun ω => min R (min (dd0 ω) ((tVol ω / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)))),
    measurable_const.min (hdd0m.min hcapm),
    fun ω => lt_min hR0 (lt_min (hdd0pos ω) (hcappos ω)), fun ω => min_le_left _ _, ?_⟩
  exact probTendsToOne_half_of_count (α := fun ε => 10 * ε ^ (ω₀ / 2))
    (dd := fun ω => min R (min (dd0 ω) ((tVol ω / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)))))
    (E := E) (G := G) (R := R) (cN := countConst ζ) (q0 := q0) (ζ := ζ) hEp' hG
    (fun ε hε => by positivity) (fun ω => min_le_left _ _) hR1 hcN hq0 hq1 hRr
    (fun ε ω r i => Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i)
    (Lemma68Config.exitQ S) hpt'

/-- **The uniform constant-order bound from the square chain (hU).** Copy of
`Lemma68ShellTopCGRCY.hU_top_cgRCY` (ShellChainCGRCY68.lean:295) with `hOne` the square form. -/
theorem hU_top_cgRCYSq {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hK : MatedCRT.Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : MatedCRT.ConeWholePlaneFieldLawStep)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (hVol : Lemma68CGRCY.FieldVolCutoffStmt 𝒮)
    (hOne : Lemma68CGRCYSq.ShellOneTestOrderAeCGRCYSqStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  uniformConstantOrderLowerBound_of_guard 𝒮
    (guardProbStmtCGRCYSq_of_chain 𝒮 (Lemma68CGRCY.countingMeshEventsHi_of_draft 𝒮 hG hC hK) hVol
      (Lemma68CGRCYSq.shellChainCGRCYSq_of_oneTestOrderCGRCYSq
        (ShortWindowHV.hprev_of_shortWindow_noH0V hLit hBM hCC hB1 hμ) hOne))

/-- **Lemma 6.7, first-pass form of the square counting CG route.** As
`MatedCRT.firstPass_6_7_of_hOneY` (Closed6x68Y.lean:39) with `hOneYSq`. -/
theorem firstPass_6_7_of_hOneYSq {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hVG : VolumeGrowthStmt)
    (hOneYSq : Lemma68CGRCYSq.ShellOneTestOrderAeCGRCYSqStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  firstPass_6_7_faithful 𝒮
    (hU_top_cgRCYSq (CertifiedReferenceModel.greenKernelLowerBound hCRM)
      (CertifiedReferenceModel.cellSizeEstimate hCRM) (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM)
      hLit hBM hCC hB1 hμ (fieldVolCutoffStmt_of_volumeGrowth hVG) hOneYSq)

/-- **Lemma 6.8, first-pass form of the square counting CG route.** As
`MatedCRT.firstPass_6_8_of_hOneY` (Closed6x68Y.lean:54) with `hOneYSq`. -/
theorem firstPass_6_8_of_hOneYSq {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hOneYSq : Lemma68CGRCYSq.ShellOneTestOrderAeCGRCYSqStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  firstPass_6_8_faithful 𝒮
    (hU_top_cgRCYSq (CertifiedReferenceModel.greenKernelLowerBound hCRM)
      (CertifiedReferenceModel.cellSizeEstimate hCRM) (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM)
      hLit hBM hCC hB1 hμ (fieldVolCutoffStmt_of_volumeGrowth (volumeGrowthStmt_of_berestyckiGwynne hBG)) hOneYSq)
    (volumeGrowthStmt_of_berestyckiGwynne hBG) (CertifiedReferenceModel.cellSizeEstimate hCRM)

/-- **Lemma 6.9, first-pass form of the square counting CG route.** As
`MatedCRT.firstPass_6_9_of_hOneY` (Closed6x68Y.lean:70) with `hOneYSq`. -/
theorem firstPass_6_9_of_hOneYSq {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hVG : VolumeGrowthStmt)
    (hOneYSq : Lemma68CGRCYSq.ShellOneTestOrderAeCGRCYSqStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  firstPass_6_9_faithful 𝒮
    (hU_top_cgRCYSq (CertifiedReferenceModel.greenKernelLowerBound hCRM)
      (CertifiedReferenceModel.cellSizeEstimate hCRM) (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM)
      hLit hBM hCC hB1 hμ (fieldVolCutoffStmt_of_volumeGrowth hVG) hOneYSq)

/-- **Lemma 6.7 with no named one-test input.** `firstPass_6_7_of_hOneYSq` with the square
one-test `CGRCYSqInst68.shellOneTestOrderAeCGRCYSq_holds`. -/
theorem firstPass_6_7_sq {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hVG : VolumeGrowthStmt) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  firstPass_6_7_of_hOneYSq hCRM hLit hBM hCC hB1 hμ hVG (Lemma68CGRCYSqInst.shellOneTestOrderAeCGRCYSq_holds 𝒮)

/-- **Lemma 6.8 with no named one-test input.** `firstPass_6_8_of_hOneYSq` with the square
one-test `CGRCYSqInst68.shellOneTestOrderAeCGRCYSq_holds`. -/
theorem firstPass_6_8_sq {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  firstPass_6_8_of_hOneYSq hCRM hLit hBM hCC hB1 hμ hBG (Lemma68CGRCYSqInst.shellOneTestOrderAeCGRCYSq_holds 𝒮)

/-- **Lemma 6.9 with no named one-test input.** `firstPass_6_9_of_hOneYSq` with the square
one-test `CGRCYSqInst68.shellOneTestOrderAeCGRCYSq_holds`. -/
theorem firstPass_6_9_sq {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hVG : VolumeGrowthStmt) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  firstPass_6_9_of_hOneYSq hCRM hLit hBM hCC hB1 hμ hVG (Lemma68CGRCYSqInst.shellOneTestOrderAeCGRCYSq_holds 𝒮)

#print axioms MatedCRT.Lemma68CGRCYSqHalf.guardProbStmtCGRCYSq_of_chain
#print axioms MatedCRT.Lemma68CGRCYSqHalf.hU_top_cgRCYSq
#print axioms MatedCRT.Lemma68CGRCYSqHalf.firstPass_6_7_of_hOneYSq
#print axioms MatedCRT.Lemma68CGRCYSqHalf.firstPass_6_8_of_hOneYSq
#print axioms MatedCRT.Lemma68CGRCYSqHalf.firstPass_6_9_of_hOneYSq
#print axioms MatedCRT.Lemma68CGRCYSqHalf.firstPass_6_7_sq
#print axioms MatedCRT.Lemma68CGRCYSqHalf.firstPass_6_8_sq
#print axioms MatedCRT.Lemma68CGRCYSqHalf.firstPass_6_9_sq

end Lemma68CGRCYSqHalf
end MatedCRT

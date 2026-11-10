import MatedCRT.FirstPass.S4S6c.Guard68S10
import MatedCRT.FirstPass.S4S6c.ShellConstants68
import MatedCRT.FirstPass.S4S6c.ShellCorePw68
import MatedCRT.FirstPass.S4S6c.HVolCutoffAe68

/-!
# The CG leaf thresholds of the hOne route (fp-S4S6c-b1-glue, z5)

For the leaf constant `K = shellKCG γ ρ ω₀ ζ CG` (`K.C = CG`, `K.c0 = c₀(CG) = exp(-2CG)/32 = shellC0 CG`,
`K.ω = ω₀`, `K.βm = (2+γ)²/2 + 1`), the threshold hypotheses of `shellOneTest_at_of_goodEnv_loc`
(B1Assembly68.lean, `hεc`, `hεs`, `hε1`, `hεcell`) follow from `ε ≤ shellEps0ZCG γ α ω₀ ζ CG` (Guard68S10.lean).
This is the CG version of the threshold facts of `shellOneTestPointwiseEps_of_goodEnv` (ShellCorePw68.lean).
-/

namespace MatedCRT
namespace Lemma68ShellCoreCG

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellConstants MatedCRT.Lemma68Guard10 MatedCRT.Lemma68ConstOrder

/-- The threshold facts `ε ≤ 16 K.c0`, `ε ≤ 1` and `ε ≤ ((100 K.c0)^K.βm/4)^(1/(α - 2 K.ω K.βm))` at the CG leaf. -/
theorem shellKCG_eps_le {γ ρ : ℝ} (K : Constants68 γ ρ) (ω₀ α ζ CG : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG)
    (hK : K = shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG)
    {ε : ℝ} (hεe : ε ≤ shellEps0ZCG γ α ω₀ ζ CG) :
    ε ≤ 16 * K.c0 ∧ ε ≤ 1 ∧
      ε ≤ ((100 * K.c0) ^ K.βm / 4) ^ (1 / (α - 2 * K.ω * K.βm)) := by
  subst hK
  have h1 : shellEps0ZCG γ α ω₀ ζ CG ≤ shellEps0CG γ α ω₀ CG := min_le_left _ _
  have h2 : shellEps0CG γ α ω₀ CG ≤ Real.exp (-(2 * CG)) / 2 := min_le_left _ _
  have h3 : shellEps0CG γ α ω₀ CG ≤
      ((100 * shellC0 CG) ^ chosenBetaMinus γ / 4) ^ (1 / (α - 2 * ω₀ * chosenBetaMinus γ)) :=
    min_le_right _ _
  have hexp : Real.exp (-(2 * CG)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · have h16 : 16 * (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG).c0 =
        Real.exp (-(2 * CG)) / 2 := by
      rw [shellKCG_c0]; ring
    rw [h16]
    linarith
  · linarith
  · exact le_trans (le_trans hεe h1) h3

/-- The cell entry at the CG leaf: `ε ^ (2/(2+γ)² - ζ) ≤ K.c0 r² / 100` from `ε ≤ shellEps0ZCG` and `10 ε^ω₀ ≤ r`
(the CG version of `hεcell` in `shellOneTestPointwiseEps_of_goodEnv`). -/
theorem shellKCG_eps_cell {γ ρ : ℝ} (K : Constants68 γ ρ) (ω₀ α ζ CG : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG)
    (hK : K = shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG)
    (hκ2 : 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ)
    {ε r : ℝ} (hε : 0 < ε) (hεe : ε ≤ shellEps0ZCG γ α ω₀ ζ CG) (hr : 10 * ε ^ ω₀ ≤ r) :
    ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ K.c0 * r ^ 2 / 100 := by
  subst hK
  have hthr : ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) ≤ shellC0 CG :=
    shellEps0ZCG_pow_le hε (by linarith) hεe
  have hc0 : 0 ≤ shellC0 CG := by unfold shellC0; positivity
  have hpow : 0 ≤ ε ^ ω₀ := Real.rpow_nonneg hε.le _
  have h2 : ε ^ (2 * ω₀) = (ε ^ ω₀) ^ 2 := by
    rw [show 2 * ω₀ = ω₀ * 2 by ring, Real.rpow_mul hε.le, Real.rpow_two]
  have hsplit : ε ^ (2 / (2 + γ) ^ 2 - ζ) = ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) * ε ^ (2 * ω₀) := by
    rw [← Real.rpow_add hε]; congr 1; ring
  have hsq : 100 * (ε ^ ω₀) ^ 2 ≤ r ^ 2 := by
    have := mul_le_mul hr hr (by linarith) (by linarith)
    nlinarith
  show ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ shellC0 CG * r ^ 2 / 100
  calc ε ^ (2 / (2 + γ) ^ 2 - ζ)
      = ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) * ε ^ (2 * ω₀) := hsplit
    _ ≤ shellC0 CG * ε ^ (2 * ω₀) := mul_le_mul_of_nonneg_right hthr (Real.rpow_nonneg hε.le _)
    _ = shellC0 CG * (ε ^ ω₀) ^ 2 := by rw [h2]
    _ ≤ shellC0 CG * (r ^ 2 / 100) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        linarith
    _ = shellC0 CG * r ^ 2 / 100 := by ring

/-! ### The CG pointwise input and its countable swap (fp-S4S6c-b1-glue, z5)

`ShellOneTestOrderAeCGStmt` (ShellHoneInst68.lean) is stated with `meshEvent` (cell size at `ρ`). The leaf
`shellOneTest_at_of_goodEnv_loc` (B1Assembly68.lean) needs the cell size at the mesh radius `(1+ρ)/2`, i.e. the
event `meshEventR` (q2, Guard68S10.lean). `ShellOneTestOrderAeCGRStmt` is that variant; the choice of hOne is the lead's. -/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow
open MatedCRT.Lemma68B1Assembly

/-- The mesh event at the radius `(1+ρ)/2` lies in `meshEvent` at `ρ`: the cell-size clause at the larger ball
`B(0,(1+ρ)/2) ⊇ B(0,ρ)` is the stronger one (`cellSizeEvent68` is antitone in the ball). -/
theorem meshEventR_sub_meshEvent {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {γ ω₀ ρ CG ζ α CE ε : ℝ} (hρ : ρ ≤ (1 + ρ) / 2) :
    meshEventR S γ ω₀ ρ CG ζ α CE ε ⊆ meshEvent S γ ω₀ ρ CG ζ α CE ε := by
  intro ω h
  obtain ⟨⟨hG, hC⟩, hE⟩ := h
  exact ⟨⟨hG, fun k hk => hC k (Set.Nonempty.mono
    (Set.inter_subset_inter_right _ (Metric.ball_subset_ball hρ)) hk)⟩, hE⟩

/-- **The CG Eps-pointwise input with the mesh radius `(1+ρ)/2` (the pointwise form of `ShellOneTestOrderAeCGRStmt`).**
Copy of `ShellOneTestPointwiseEpsStmt` (ShellCorePw68.lean) with `CG`-constants: `shellEps0ZCG`, `shellC0 CG`,
`shellS1CG γ CG`, `meshEventR`, `cellSizeEvent68 … ((1+ρ)/2)`; plus the cutoff premise of `ShellPtPrem`
(`cutoff_ae_K` at `K.βm = (2+γ)²/2+1`, discharged a.s. in the swap). -/
def ShellOneTestPointwiseCGRStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ ω : Ω, ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        Continuous (S.η ω) → (∀ v : ℂ, S.μ ω {v} = 0) → IsFiniteMeasureOnCompacts (S.μ ω) →
        (∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤) →
        (∀ u v : ℤ, S.mult ε ω u v ≠ 0 → (closure (cell ε (S.η ω) u) ∩ closure (cell ε (S.η ω) v)).Nonempty) →
        (∀ ε' : ℝ, 0 < ε' → ∀ u v : ℤ, S.mult ε' ω u v ≠ 0 → (cell ε' (S.η ω) u ∩ cell ε' (S.η ω) v).Nonempty) →
        (∃ t : ℝ, 0 < t ∧ ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ),
          ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ)) →
        (∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C ((1 / 2 : ℝ) ^ k)) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- **`ShellOneTestOrderAeCGStmt` with the mesh radius `(1+ρ)/2`** (the variant of ShellHoneInst68.lean:266 that
`shellOneTest_at_of_goodEnv_loc` serves): `meshEvent` → `meshEventR`, `cellSizeEvent68 … ρ` → `… ((1+ρ)/2)`. -/
def ShellOneTestOrderAeCGRStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C δ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ᵐ ω ∂S.P, ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- **The countable swap of the CG pointwise input.** The dyadic window avoidance (`ae_all_iff` over `ℕ`), the
regularity facts (`ae_continuous_eta`, `ae_null_singleton_of_valid`, `ae_finite_on_compacts_of_valid`,
`ae_adjacent`) and the cutoff (`cutoff_ae` at `β = (2+γ)²/2+1`, needs the volume-growth input `hVG`) are almost sure. -/
theorem shellOneTestOrderAeCGRStmt_of_pointwise {𝒮 : SpaceFillingSLEModel} (hVG : VolumeGrowthStmt)
    (h : ShellOneTestPointwiseCGRStmt 𝒮) : ShellOneTestOrderAeCGRStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp Ew hEwm hEwp hav ε hε hεe
  have hdy : ∀ᵐ ω ∂S.P, ∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) →
      ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C ((1 / 2 : ℝ) ^ k) :=
    ae_all_iff.mpr fun k => hav ((1 / 2 : ℝ) ^ k)
  filter_upwards [hdy, TraceInputs68.ae_continuous_eta hS, Lemma68ShellCorePw.ae_null_singleton_of_valid hS,
    Lemma68ShellCorePw.ae_finite_on_compacts_of_valid hS,
    MatedCRT.Lemma68HoneExitGeom.hdeg_of_valid hγ0 hγ2 S hS hε,
    MatedCRT.Lemma68HoneExitGeom.hadj_of_valid hγ0 hγ2 S hS hε, TraceInputs68.ae_adjacent hγ0 hγ2 S hS,
    Lemma68HVolCutoffAe.cutoff_ae S hS hVG hγ0 hγ2 (β := (2 + γ) ^ 2 / 2 + 1) (by linarith)]
    with ω hω hηc hμN hμF hdg hadjA hadjAll hcutA hmesh hcurve hmult
  exact hcl R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp ε hε hεe ω hmesh hcurve hmult
    hηc hμN hμF hdg hadjA hadjAll hcutA (fun k hk => hω k hk)

end Lemma68ShellCoreCG
end MatedCRT

#print axioms MatedCRT.Lemma68ShellCoreCG.shellKCG_eps_le
#print axioms MatedCRT.Lemma68ShellCoreCG.shellKCG_eps_cell
#print axioms MatedCRT.Lemma68ShellCoreCG.meshEventR_sub_meshEvent
#print axioms MatedCRT.Lemma68ShellCoreCG.shellOneTestOrderAeCGRStmt_of_pointwise

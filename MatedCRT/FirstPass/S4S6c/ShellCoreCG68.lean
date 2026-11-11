import MatedCRT.FirstPass.S4S6c.Guard68S10
import MatedCRT.FirstPass.S4S6c.ShellConstants68
import MatedCRT.FirstPass.S4S6c.ShellCorePw68
import MatedCRT.FirstPass.S4S6c.HVolCutoffAe68

/-!
# The CG leaf thresholds of the hOne route

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

/-! ### The CG pointwise input and its countable swap

`ShellOneTestOrderAeCGStmt` (ShellHoneInst68.lean) is stated with `meshEvent` (cell size at `ρ`). The leaf
`shellOneTest_at_of_goodEnv_loc` (B1Assembly68.lean) needs the cell size at the mesh radius `(1+ρ)/2`, i.e. the
event `meshEventR` (Guard68S10.lean). `ShellOneTestOrderAeCGRStmt` is that variant; the choice of `hOne` is a separate decision. -/

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
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE β : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE → 0 < β →
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
      HarmonicBalls.PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρ) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ ω : Ω,
        ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε →
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

/-! ### Deterministic leaf discharges at the CG leaf

The binders of `shellOneTest_at_of_goodEnv_loc_g` (B1Assembly68.lean) that are deterministic functions of the
parameters are discharged here. The gap binder `hgapShell` (ShellOrderLoc68.lean:170) is not implied by the
cut `hcut` alone; it needs `dyadicD r ^ shortExp ζ ≤ (rhoCell68 ρ - ρ)/4`, which the producer obtains by choosing
the amplitude `q0` small (`exists_q0_rAmp_le`), since `rAmp q0 ζ` is increasing in `q0`. -/

/-- The leaf inequalities `hκ2`, `hα`, `hrε` of the CG leaf at `K = shellKCG`: `K.ω = ω₀`, `K.βm = chosenBetaMinus γ`. -/
theorem shellKCG_leaf_ineqs {γ ρ : ℝ} (K : Constants68 γ ρ) (ω₀ α ζ CG : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG)
    (hK : K = shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG)
    (hω2ζ : 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ) (hαβ : 2 * ω₀ * chosenBetaMinus γ < α) {ε r : ℝ}
    (hr : 10 * ε ^ ω₀ ≤ r) :
    2 * K.ω < 2 / (2 + γ) ^ 2 - ζ ∧ 2 * K.ω * K.βm < α ∧ 10 * ε ^ K.ω ≤ r := by
  subst hK
  exact ⟨hω2ζ, hαβ, hr⟩

/-- The cut `hcutR` / `hcut` at the radius `r ≤ R`: the Stmt's range hypothesis `hRcut` instantiated. -/
theorem cut_of_hRcut {ρ ζ R r : ℝ}
    (hRcut : ∀ r' : ℝ, 0 < r' → r' ≤ R → (dyadicD r') ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    (hr0 : 0 < r) (hrR : r ≤ R) :
    dyadicD r ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ :=
  hRcut r hr0 hrR

/-- The gap `hgapShell` of ShellOrderLoc68.lean:170 at `ρmesh = rhoCell68 ρ = (1+ρ)/2`, from the smallness
`dyadicD r ^ shortExp ζ ≤ (rhoCell68 ρ - ρ)/4`. Uses `dyadicD r ≤ dyadicD r ^ shortExp ζ` (`shortExp ζ ≤ 1`, `dyadicD r ≤ 1`). -/
theorem hgapShell_of_pow_le {ρ ζ d : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hd0 : 0 < d)
    (hd1 : d ≤ 1) (hsmall : d ^ shortExp ζ ≤ (Lemma68HoneCellGood.rhoCell68 ρ - ρ) / 4) :
    2 * (d / 100) + 2 * d ^ shortExp ζ ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hda : d ≤ d ^ shortExp ζ := by
    have h := Real.rpow_le_rpow_of_exponent_ge hd0 hd1 ha1
    rwa [Real.rpow_one] at h
  have hdef : Lemma68HoneCellGood.rhoCell68 ρ = (1 + ρ) / 2 := rfl
  rw [hdef] at hsmall ⊢
  linarith

/-- For `0 < r ≤ 1`, `dyadicD r ^ shortExp ζ ≤ c` as soon as `2 r² ≤ c^(1/shortExp ζ)` (`dyadicD r < 2 r²`). -/
theorem dyadicD_pow_le_of_sq {r ζ c : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hζ0 : 0 < ζ) (hc0 : 0 < c)
    (hrc : 2 * r ^ 2 ≤ c ^ (1 / shortExp ζ)) : dyadicD r ^ shortExp ζ ≤ c := by
  have ha : 0 < shortExp ζ := by unfold shortExp; linarith
  have hd0 : 0 ≤ dyadicD r := (dyadicD_pos r).le
  have hlt : dyadicD r ≤ 2 * r ^ 2 := (dyadicD_lt_two_mul_sq hr0 hr1).le
  calc dyadicD r ^ shortExp ζ ≤ (2 * r ^ 2) ^ shortExp ζ := Real.rpow_le_rpow hd0 hlt ha.le
    _ ≤ (c ^ (1 / shortExp ζ)) ^ shortExp ζ :=
        Real.rpow_le_rpow (by positivity) hrc ha.le
    _ = c := by rw [← Real.rpow_mul hc0.le, one_div_mul_cancel ha.ne', Real.rpow_one]

/-- The amplitude choice: for `c, qmax > 0` there is `0 < q0 ≤ qmax` with `rAmp q0 ζ ≤ R₀ := √(c^(1/shortExp ζ)/2)`.
`rAmp q0 ζ = min 1 ((q0/200 ζ²/(16 log 2))^(2/ζ))` is increasing in `q0`, so the producer may take `q0` small. -/
theorem exists_q0_rAmp_le {ζ c qmax : ℝ} (hζ0 : 0 < ζ) (hc0 : 0 < c) (hqmax : 0 < qmax) :
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ qmax ∧
      Lemma68Cutoff.rAmp q0 ζ ≤ Real.sqrt (c ^ (1 / shortExp ζ) / 2) := by
  have ha : 0 < shortExp ζ := by unfold shortExp; linarith
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hζne : ζ ≠ 0 := hζ0.ne'
  set R0 := Real.sqrt (c ^ (1 / shortExp ζ) / 2) with hR0def
  have hR0 : 0 < R0 := Real.sqrt_pos.mpr (div_pos (Real.rpow_pos_of_pos hc0 _) two_pos)
  set Y := R0 ^ (ζ / 2) with hYdef
  have hY : 0 < Y := Real.rpow_pos_of_pos hR0 _
  set q0 := min qmax (3200 * Real.log 2 * Y / ζ ^ 2) with hq0def
  have hq0 : 0 < q0 := lt_min hqmax (div_pos (mul_pos (mul_pos (by norm_num) hlog) hY) (pow_pos hζ0 2))
  have hq0le : q0 ≤ 3200 * Real.log 2 * Y / ζ ^ 2 := min_le_right _ _
  refine ⟨q0, hq0, min_le_left _ _, ?_⟩
  have key : q0 * ζ ^ 2 ≤ 3200 * Real.log 2 * Y := by
    have h := mul_le_mul_of_nonneg_right hq0le (sq_nonneg ζ)
    rwa [div_mul_cancel₀ _ (pow_pos hζ0 2).ne'] at h
  have hX : q0 / 200 * ζ ^ 2 / (16 * Real.log 2) ≤ Y := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hlog)]
    have e : q0 / 200 * ζ ^ 2 = q0 * ζ ^ 2 / 200 := by ring
    rw [e, div_le_iff₀ (by norm_num : (0 : ℝ) < 200)]
    nlinarith [key]
  have hXpow : (q0 / 200 * ζ ^ 2 / (16 * Real.log 2)) ^ (2 / ζ) ≤ Y ^ (2 / ζ) :=
    Real.rpow_le_rpow (div_nonneg (mul_nonneg (div_nonneg hq0.le (by norm_num))
      (sq_nonneg ζ)) (mul_nonneg (by norm_num) hlog.le)) hX (div_nonneg (by norm_num) hζ0.le)
  have hYR : Y ^ (2 / ζ) = R0 := by
    rw [hYdef, ← Real.rpow_mul hR0.le, show ζ / 2 * (2 / ζ) = 1 by field_simp, Real.rpow_one]
  unfold Lemma68Cutoff.rAmp
  exact (min_le_right _ _).trans (hXpow.trans hYR.le)

/-- The gap and the radius bound at the producer's `q0`: for `0 < r ≤ rAmp q0 ζ` with `rAmp q0 ζ ≤ √(c^(1/shortExp ζ)/2)`,
`c = (rhoCell68 ρ - ρ)/4`, the gap `hgapShell` holds at `ρmesh = rhoCell68 ρ`. -/
theorem hgapShell_of_rAmp_le {ρ ζ q0 r : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr0 : 0 < r)
    (hrA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (hq : Lemma68Cutoff.rAmp q0 ζ ≤ Real.sqrt ((((Lemma68HoneCellGood.rhoCell68 ρ - ρ) / 4)) ^ (1 / shortExp ζ) / 2)) :
    2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
  have hdef : Lemma68HoneCellGood.rhoCell68 ρ - ρ = (1 - ρ) / 2 := by
    unfold Lemma68HoneCellGood.rhoCell68; ring
  have hc0 : 0 < (Lemma68HoneCellGood.rhoCell68 ρ - ρ) / 4 := by rw [hdef]; linarith
  have hr1 : r ≤ 1 := by
    unfold Lemma68Cutoff.rAmp at hrA
    exact hrA.trans (min_le_left _ _)
  have hrR0 : r ≤ Real.sqrt ((((Lemma68HoneCellGood.rhoCell68 ρ - ρ) / 4)) ^ (1 / shortExp ζ) / 2) := hrA.trans hq
  have hsq : r ^ 2 ≤ ((((Lemma68HoneCellGood.rhoCell68 ρ - ρ) / 4)) ^ (1 / shortExp ζ) / 2) := by
    have h2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((((Lemma68HoneCellGood.rhoCell68 ρ - ρ) / 4)) ^ (1 / shortExp ζ) / 2))
    nlinarith [hrR0, hr0]
  have hpow := dyadicD_pow_le_of_sq hr0 hr1 hζ0 hc0 (by linarith)
  exact hgapShell_of_pow_le hζ0 hζ1 (dyadicD_pos r) (dyadicD_le_one r) hpow

/-! ### The CG-R pointwise producer

`shellOneTestPointwiseCGR_of_goodEnv_loc_g` proves `ShellOneTestPointwiseCGRStmt` from `shellOneTest_at_of_goodEnv_loc_g`
(B1Assembly68.lean:1216, fb32a38) at `K = shellKCG`. Every binder of that lemma is one of: (a) a deterministic fact of the
parameters, discharged here; (b) `hmesh`, `hcap`, `hCellGood`, `hfull`, discharged here from the Stmt's ω-level premises;
(c) one of the twelve residual binders `ShellCGRes…` below, quantified over all parameters and assumed as named hypotheses
of the producer, each to be supplied by its owner. -/

/-- `shellC0 CG = exp(-2CG)/32 ≤ 1` for `CG > 0`. -/
theorem shellC0_le_one_cg {CG : ℝ} (hCG : 0 < CG) : shellC0 CG ≤ 1 := by
  unfold shellC0
  have h : Real.exp (-(2 * CG)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-- **The cell-diameter bound on `B(0, rhoCell68 ρ)` from the cell-size clause of `meshEventR`** (the binder `hmesh` of
`shellOneTest_at_of_goodEnv_loc_g`). A copy of `cellDiamLe_ball_of_meshEvent` (HoneSetupAdapt68.lean:78) at the ball radius
`(1 + ρ)/2 = rhoCell68 ρ`, reading the cell clause of `meshEventR` (`cellSizeEvent68 … ((1+ρ)/2)`). -/
theorem cellDiamLe_rhoCell_of_meshEventR {γ ω₀ ρ CG ζ α CE : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ε c0 r : ℝ} (ω : Ω) (hω : ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε) (hε : 0 < ε)
    (hρ1 : ρ < 1) (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hc0 : c0 ≤ 1)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ c0 * r ^ 2 / 100) :
    CellDiamLe ε (S.η ω) (dyadicD r / 100) (ball 0 (Lemma68HoneCellGood.rhoCell68 ρ)) := by
  have hcell : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
      ε ^ (2 / (2 - γ) ^ 2 + ζ) ≤ diam (cell ε (S.η ω) k) ∧
        diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) :=
    fun k hk => hω.1.2 k hk
  have hr1 : r ≤ 1 := by linarith
  have hbdd : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
      Bornology.IsBounded (cell ε (S.η ω) k) := by
    intro k hk
    by_contra hnb
    have hlow := (hcell k hk).1
    rw [diam_eq_zero_of_unbounded hnb] at hlow
    exact absurd hlow (not_le.mpr (Real.rpow_pos_of_pos hε _))
  have hbound : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ dyadicD r / 100 := by
    have hsq : r ^ 2 ≤ dyadicD r := sq_le_dyadicD hr hr1
    have hc : c0 * r ^ 2 ≤ r ^ 2 := mul_le_of_le_one_left (sq_nonneg r) hc0
    linarith
  unfold CellDiamLe
  intro k hk p hp q hq
  calc dist p q ≤ diam (cell ε (S.η ω) k) := Metric.dist_le_diam_of_mem (hbdd k hk) hp hq
    _ ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) := (hcell k hk).2
    _ ≤ dyadicD r / 100 := hbound

/-- The premises of `ShellOneTestPointwiseCGRStmt` at one scale `ε`, one radius `r` with `10 ε^ω₀ ≤ r ≤ R`, and one
environment `ω`: the Stmt's own premises, the `r`-level facts of its conclusion (`hgap`: the order gap at `rhoCell68 ρ`), and
the full support `hfs` of `S.μ ω`. The residual binders below may use all of them. -/
def ShellPtPremCG (𝒮 : SpaceFillingSLEModel) (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (Ew : ℝ → Set Ω) (ω : Ω) : Prop :=
  0 < γ ∧ γ < 2 ∧ 0 < ω₀ ∧ ω₀ < α ∧ 0 < α ∧ ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧
    2 * ω₀ * chosenBetaMinus γ < α ∧ 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧
    0 < CG ∧ 0 < CE ∧ 0 < β ∧ 0 < ζ ∧ ζ < 1 / 2 ∧ 0 < ρ ∧ ρ < 1 ∧ 0 < C ∧
    0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG) ∧
    0 < R ∧ R ≤ ρ / 4 ∧ R ≤ Lemma68Cutoff.rAmp q0 ζ ∧
    (∀ r' : ℝ, 0 < r' → r' ≤ R → (dyadicD r') ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) ∧
    0 < s₀ ∧ s₀ < 1 ∧ S.IsValid 𝒮 γ ∧ 0 < ε ∧ ε ≤ shellEps0ZCG γ α ω₀ ζ CG ∧
    10 * ε ^ ω₀ ≤ r ∧ r ≤ R ∧ ω ∈ Ew (dyadicD r) ∧ ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε ∧
    2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ ∧
    Lemma68Inputs.CurveEscapesBothEnds (S.η ω) ∧
    (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) ∧
    Continuous (S.η ω) ∧ (∀ v : ℂ, S.μ ω {v} = 0) ∧ IsFiniteMeasureOnCompacts (S.μ ω) ∧
    (∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤) ∧
    (∀ u v : ℤ, S.mult ε ω u v ≠ 0 → (closure (cell ε (S.η ω) u) ∩ closure (cell ε (S.η ω) v)).Nonempty) ∧
    (∀ ε' : ℝ, 0 < ε' → ∀ u v : ℤ, S.mult ε' ω u v ≠ 0 → (cell ε' (S.η ω) u ∩ cell ε' (S.η ω) v).Nonempty) ∧
    (∃ t : ℝ, 0 < t ∧ ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ)) ∧
    (∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C ((1 / 2 : ℝ) ^ k))

/-! #### The twelve residual binders. Each is a binder of `shellOneTest_at_of_goodEnv_loc_g`
with `c0W := shellC0 CG`, `s1 := shellS1CG γ CG`, `K.c0 := shellC0 CG`, `K.βm := (2+γ)^2/2+1`, `K.C := CG`, `K.ω := ω₀`,
quantified over all parameters and assuming `ShellPtPremCG`. -/

/-- Residual `hShellLoc` (ShellOrderLoc68 pointwise form at `hmesh`). -/
def ShellCGResLoc (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)) →
      Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
        Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
          (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- Residual `hEl` (`hEl_fixedOmega_g`): the leaf centres are eligible. -/
def ShellCGResEl (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ)

/-- Residual `hstopFin`: the shell exit lands in a finite set. -/
def ShellCGResStopFin (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∃ F : Set ℤ, F.Finite ∧
        ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k x < ⊤ →
            x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k x).toNat ∈ F

/-- Residual `hRr` (`hRr_fixedOmega_loc_g`): the window lies in `[r², 1]` on the leaf. -/
def ShellCGResRr (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          r ^ 2 ≤ (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1

/-- Residual `hVolC` (`hVolC_pw_g`): the ball-volume lower bound at the leaf centres (`K.c0 = shellC0 CG`, `K.βm`). -/
def ShellCGResVolC (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          ENNReal.ofReal ((shellC0 CG * (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) ^
                ((2 + γ) ^ 2 / 2 + 1))
            ≤ S.μ ω (ball (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)) k x).toNat))
              (shellC0 CG * (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
                (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)))

/-- Residual `hVolY` (`hVolY_pw_g`): the ball-volume lower bound on the annuli around the leaf centres. -/
def ShellCGResVolY (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          ∀ y ∈ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ - (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4),
            ENNReal.ofReal (((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
                (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4) ^
                ((2 + γ) ^ 2 / 2 + 1))
              ≤ S.μ ω (ball y ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
                (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4))

/-- Residual `hGreen` (free Green exponent; `K.C = CG`; `K.ω = ω₀`). -/
def ShellCGResGreen (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₀)), ∀ r' : ℝ, ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          CG⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
            ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b

/-- Residual `hCountGood`: the counting lower bound on the cells of a set `D ⊆ B(0,ρ)`. -/
def ShellCGResCountGood (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
        ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ)

/-- Residual `hsel` (`hsel_fixedOmega_g`): the eligible centres carry good annulus events (`K.c0 = shellC0 CG`). -/
def ShellCGResSel (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
        IsGoodAnnulusEvent (S.μ ω) (shellC0 CG) CG
          ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) z) z

/-- Residual `hx1` (HoneX1Loc68): the leaf exit lies in the cell-size ball. -/
def ShellCGResX1 (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)) k x).toNat)‖
            < Lemma68HoneCellGood.rhoCell68 ρ - (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4

/-- Residual `hmomS` (HoneMomSPw68): the exit-time moments on the sets `D ⊆ B(0, rhoCell68 ρ)`. -/
def ShellCGResMomS (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 (Lemma68HoneCellGood.rhoCell68 ρ) →
          ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
            exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
              ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
                (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                  ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N

/-- Residual `hWalk` (split form at the exponent `2/(2+γ)² - ζ`; `K.ω = ω₀`). -/
def ShellCGResWalk (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)) k x).toNat ∈
              cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₀)) ∧
            ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)) k x).toNat))
                (sphere 0 ρ)

/-- **Temporary positivity residual `hPos`.** The ball positivity `0 < S.μ ω (ball w τ)` that
`shellOneTest_at_of_goodEnv_loc_g` takes as `hfull` (the `hωFull` binder of `_g2`, B1GoodEnvLoc68.lean:167). It is stated
at the `FullAdmAt` point, under `ShellPtPremCG`, exactly as the binder. Deleted when the narrow hωFull-free `_g2`
(annulus positivity from `Lemma68Cutoff239.pos_iInf_of_cutoff`, HVolCutoff239_68.lean:278). -/
def ShellCGResPos (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ w : ℂ, ∀ t : ℝ, 0 < t → 0 < S.μ ω (ball w t)

/-- **The CG-R pointwise producer.** `ShellOneTestPointwiseCGRStmt` from `shellOneTest_at_of_goodEnv_loc_g` at `K = shellKCG`,
with the twelve residual binders as named hypotheses. The ∃ `q0` is chosen with `rAmp q0 ζ ≤ √(((rhoCell68 ρ - ρ)/4)^(1/a)/2)`
(`exists_q0_rAmp_le`), which gives the order gap `hgap`; `hcutR` is `cut_of_hRcut`; `hmesh` is
`cellDiamLe_rhoCell_of_meshEventR`; `hCellGood` is the cell clause of `meshEventR`; `hcap` is `hcap_of_continuous_g`;
`hfull` is the Stmt's full-support premise. -/
theorem shellOneTestPointwiseCGR_of_goodEnv_loc_g {𝒮 : SpaceFillingSLEModel}
    (hShellLoc : ShellCGResLoc 𝒮) (hEl : ShellCGResEl 𝒮) (hstopFin : ShellCGResStopFin 𝒮)
    (hRr : ShellCGResRr 𝒮) (hVolC : ShellCGResVolC 𝒮) (hVolY : ShellCGResVolY 𝒮)
    (hGreen : ShellCGResGreen 𝒮) (hCountGood : ShellCGResCountGood 𝒮) (hsel : ShellCGResSel 𝒮)
    (hx1 : ShellCGResX1 𝒮) (hmomS : ShellCGResMomS 𝒮) (hWalk : ShellCGResWalk 𝒮)
    (hPos : ShellCGResPos 𝒮) :
    ShellOneTestPointwiseCGRStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC _hC' _hP
  obtain ⟨q0, hq0, hq0A, hq0B, hq⟩ : ∃ q0 : ℝ, 0 < q0 ∧
      q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG) ∧
      Lemma68Cutoff.rAmp q0 ζ ≤ Real.sqrt ((((Lemma68HoneCellGood.rhoCell68 ρ - ρ) / 4)) ^ (1 / shortExp ζ) / 2) := by
    have h1 := one_le_shellChone68 CE C
    have h2 := one_le_shellChone68 CE CG
    have hA : (0 : ℝ) < (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) := div_pos (by norm_num) (by linarith)
    have hB : (0 : ℝ) < (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG) := div_pos (by norm_num) (by linarith)
    have hc0 : 0 < (Lemma68HoneCellGood.rhoCell68 ρ - ρ) / 4 := by
      unfold Lemma68HoneCellGood.rhoCell68; linarith
    obtain ⟨q0, hq0, hqm, hr⟩ := exists_q0_rAmp_le hζ0 hc0 (lt_min hA hB)
    exact ⟨q0, hq0, le_trans hqm (min_le_left _ _), le_trans hqm (min_le_right _ _), hr⟩
  refine ⟨q0, hq0, hq0A, ?_⟩
  intro R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp hCntp Ew hEwm hEwp ε hε hεe ω hmeshω hcurve hmult
    hcont hμN hμF hdeg hadj hadjAll hcutA hav r hr10 hrR hωE i hadm
  have hr0 : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hε _)) hr10
  have hr1 : r ≤ 1 := by linarith
  have hrA : r ≤ Lemma68Cutoff.rAmp q0 ζ := le_trans hrR hRA
  have hrρ : r ≤ ρ / 4 := le_trans hrR hRρ
  obtain ⟨hεc, hε1, hεs⟩ := shellKCG_eps_le (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) ω₀ α ζ CG
    hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG rfl hεe
  have hεcell := shellKCG_eps_cell (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) ω₀ α ζ CG
    hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG rfl hω2ζ hε hεe hr10
  obtain ⟨hκ2, hα, hrε⟩ := shellKCG_leaf_ineqs (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) ω₀ α ζ CG
    hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG rfl hω2ζ hωβ hr10
  have hcutR := cut_of_hRcut hRcut hr0 hrR
  have hgap := hgapShell_of_rAmp_le hρ1 hζ0 hζ1 hr0 hrA hq
  have hrz := MatedCRT.Lemma68HoneSetupAdapt.hrz_of_rAmp hq0 hq0B hζ0 hζ1 hrA
  have hmesh := cellDiamLe_rhoCell_of_meshEventR (c0 := shellC0 CG) S ω hmeshω.1 hε hρ1 hr0 hrρ
    (shellC0_le_one_cg hCG) hεcell
  have hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω :=
    ⟨meshEventR_sub_meshEvent S (by linarith : ρ ≤ (1 + ρ) / 2) hmeshω.1, hcurve, hmult, hcont, hμN, hμF,
      hdeg, hadj, hadjAll⟩
  have hpre : ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω :=
    ⟨hγ0, hγ2, hω₀, hωα, hα0, hωζ, hωβ, hω2ζ, hCG, hCE, hβ, hζ0, hζ1, hρ0, hρ1, hC, hq0, hq0A, hq0B,
      hR0, hRρ, hRA, hRcut, hs₀, hs₁, hS, hε, hεe, hr10, hrR, hωE, hmeshω, hgap, hcurve, hmult, hcont,
      hμN, hμF, hdeg, hadj, hadjAll, hcutA, hav⟩
  obtain ⟨Rf, h1, h2⟩ := shellOneTest_at_of_goodEnv_loc_g hγ0 hγ2 (shellC0 CG) S hρ0 hρ1 hζ0 hζ1 hCG hq0 hq0B
    hε hs₀ hr0 hrρ hrz hrA ω₀ hω₀ (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) rfl ω hreg i
    hεc hεcell hκ2 hα hεs hrε hε1 hmesh
    (hShellLoc γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    hadm
    (hEl γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hstopFin γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hRr γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (MatedCRT.Lemma68HoneSetupAdapt.hcap_of_continuous_g (s1 := shellS1CG γ CG) S ω hcont hε hr0 i)
    (hVolC γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hVolY γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hGreen γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hCountGood γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (fun _ k' hk => (hmeshω.1.1.2 k' hk).2)
    hcutR
    (hx1 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hmomS γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hWalk γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hsel γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hPos γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
  exact ⟨Rf, h1, h2⟩

#print axioms MatedCRT.Lemma68ShellCoreCG.shellOneTestPointwiseCGR_of_goodEnv_loc_g

end Lemma68ShellCoreCG
end MatedCRT

#print axioms MatedCRT.Lemma68ShellCoreCG.shellKCG_eps_le
#print axioms MatedCRT.Lemma68ShellCoreCG.shellKCG_eps_cell
#print axioms MatedCRT.Lemma68ShellCoreCG.meshEventR_sub_meshEvent
#print axioms MatedCRT.Lemma68ShellCoreCG.shellKCG_leaf_ineqs
#print axioms MatedCRT.Lemma68ShellCoreCG.hgapShell_of_rAmp_le
#print axioms MatedCRT.Lemma68ShellCoreCG.exists_q0_rAmp_le

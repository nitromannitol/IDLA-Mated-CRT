import MatedCRT.FirstPass.S6r.OneTest.Count
import MatedCRT.FirstPass.S6r.Prevalence

/-!
# Second moment of the one-test occupation count (PRO step 8 `one_test_from_boundary`; Lemma 6.8 redesign)

Setting (PRO step 8; open-parts B5 (B17)): `b` a start vertex in `V^ε(∂B_{4R/3}(z))`, `x = η(εb)`, `D = B_{R/4}(x)`,
`D₀ = B_{3c₀R}(x)`, `ID = interiorCellVertices ε η D` (the discrete interior of `D`), `σ_D(w) = (vExitTime ID w).toNat`,
`V_occ = occCount A σ_D`. Claim: `E_b[V_occ²] ≤ C₂ ε⁻² (1 + log(1/R))² μ(D₀)²`, with
`C₂ = 32 C_exit² ((1 + N log 4) C_good)²`.

Chain. `V_occ ≤ σ_D` pointwise, so `E[V_occ²] ≤ E[τ_D²] = exitTimeMoment ID b 2`. The second-moment conjunct of
Lemma 2.18 (first conjunct of `ExitTimeUpperBoundStmt`, Draft/Section2.lean) bounds this by `2 C_exit² ε⁻² S_D²`, where
`S_D = sup_{z∈D} ∫_{B_{ε^α}(D)} (log(1/|z-w|)+1) dμ`. Step 2: `S_D ≤ L_R(z) ≤ (1 + N log 4) C_good (1 + |log 4R|) μ(D₀)`
on the good annulus, through `printedL_le_of_event` after the [C5] bridge `scaleCovGoodAnnulusEvent_of_isGoodAnnulusEvent`.

Named inputs (each is a pointwise slice of a Stmt, or a side condition, all listed in the theorem):
* `hmom`: the first conjunct of `ExitTimeUpperBoundStmt` (Lemma 2.18) at `ω`, for all Borel `D ⊆ B_ρ`. The ball form
  `ExitTimeUpperBoundBallStmt` (chat 184) replaces only the expected-exit-time conjunct, so it cannot supply `N = 2`.
* `hvol`: the lower half of `VolumeGrowthStmt` (Lemma 2.7) at `ω`, radius `R/4`, centres in `B_{1-R/4}`.
* `hgood`: the [C5] good-annulus event `IsGoodAnnulusEvent`, with the covering, positivity, atomlessness and finiteness
  side conditions of the bridge `scaleCovGoodAnnulusEvent_of_isGoodAnnulusEvent`.
* `hcell`: every pair of points of the cell of `b` is within `h ≤ R/100` (cell size, IDLA 2.8, pointwise at `ω`).
-/

open MeasureTheory Metric HarmonicBalls

namespace MatedCRT
namespace Lemma68Window

/-- Lower-integral comparison for a nonnegative real function with a finite bound `M`: `∫ f ≤ M.toReal`. No
measurability is needed, since a non-integrable `f` has Bochner integral `0`. -/
lemma integral_le_toReal_of_lintegral_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ}
    (hf : ∀ ω, 0 ≤ f ω) {M : ENNReal} (hM : M ≠ ⊤) (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ M) :
    ∫ ω, f ω ∂P ≤ M.toReal := by
  by_cases hint : Integrable f P
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf) hint.aestronglyMeasurable]
    exact ENNReal.toReal_mono hM h
  · rw [integral_undef hint]
    exact ENNReal.toReal_nonneg

/-- The occupation count is nonnegative and at most `σ` (each summand is an indicator of at most `1`). -/
lemma occCount_nonneg_le_card {E : Type*} (A : Set E) (σ : (ℕ → E) → ℕ) (w : ℕ → E) :
    0 ≤ occCount A σ w ∧ occCount A σ w ≤ (σ w : ℝ) := by
  unfold occCount
  refine ⟨Finset.sum_nonneg fun n _ => ?_, ?_⟩
  · unfold Set.indicator; split_ifs <;> norm_num
  · calc ∑ n ∈ Finset.range (σ w), Aᶜ.indicator (fun _ => (1 : ℝ)) (w n)
        ≤ ∑ _n ∈ Finset.range (σ w), (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => by unfold Set.indicator; split_ifs <;> norm_num
      _ = (σ w : ℝ) := by simp

/-- `ofReal ((τ.toNat)²) ≤ (τ)²` in `[0, ∞]`; on `τ = ∞` the left side is `0`. -/
lemma ofReal_sq_toNat_le (τ : ℕ∞) :
    ENNReal.ofReal ((τ.toNat : ℝ) ^ 2) ≤ (τ : ENNReal) ^ 2 := by
  induction τ using ENat.recTopCoe with
  | top => simp
  | coe n => simp [ENNReal.ofReal_pow, ENNReal.ofReal_natCast]

/-- Walk-level second moment: `E_b[V_occ²] ≤ E_b[τ_ID²] = exitTimeMoment ID b 2` (B5 (B17), first inequality). -/
lemma lintegral_occCount_sq_le (m : ℤ → ℤ → ℕ) (A ID : Set ℤ) (b : ℤ) :
    ∫⁻ w, ENNReal.ofReal (occCount A (fun w => (vExitTime ID w).toNat) w ^ 2) ∂(srwLaw m b)
      ≤ exitTimeMoment m ID b 2 := by
  unfold exitTimeMoment
  refine lintegral_mono fun w => ?_
  obtain ⟨h0, h1⟩ := occCount_nonneg_le_card A (fun w => (vExitTime ID w).toNat) w
  calc ENNReal.ofReal (occCount A (fun w => (vExitTime ID w).toNat) w ^ 2)
      ≤ ENNReal.ofReal (((vExitTime ID w).toNat : ℝ) ^ 2) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ h0 h1 2)
    _ ≤ ((vExitTime ID w : ℕ∞) : ENNReal) ^ 2 := ofReal_sq_toNat_le _

/-- Geometry (PRO step 8: `B_{R/4+δ}(x) ⊆ 𝔸_{R,2R}(z)`): if `|x - z| ∈ [4R/3 - R/100, 4R/3 + R/100]` and `0 ≤ δ ≤ R/100`,
then `B_{R/4+δ}(x) ⊆ annulus z R (2R)`. -/
lemma ball_add_subset_annulus {z x : ℂ} {R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R / 100)
    (hxz : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100) :
    ball x (R / 4 + δ) ⊆ annulus z R (2 * R) := by
  intro u hu
  rw [mem_ball, dist_eq_norm] at hu
  rw [mem_annulus_iff]
  have h1 : ‖u - z‖ ≤ ‖u - x‖ + ‖x - z‖ := by
    have := norm_add_le (u - x) (x - z)
    rwa [sub_add_sub_cancel] at this
  have h2 : ‖x - z‖ - ‖u - x‖ ≤ ‖u - z‖ := by
    have := norm_sub_norm_le (x - z) (x - u)
    rwa [show (x - z) - (x - u) = u - z by ring, norm_sub_rev x u] at this
  constructor <;> linarith [hxz.1, hxz.2]

/-- The thickening `B_{δ}`-neighbourhood of `D = B_{R/4}(x)` lies in `𝔸_{R,2R}(z)` (`thickening_ball`). -/
lemma thickening_ball_subset_annulus {z x : ℂ} {R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R / 100)
    (hxz : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100) :
    Metric.thickening δ (ball x (R / 4)) ⊆ annulus z R (2 * R) := by
  intro u hu
  have hu' := Metric.thickening_ball x δ (R / 4) hu
  rw [add_comm] at hu'
  exact ball_add_subset_annulus hR hδ hxz hu'

/-- The bump mass is at most the mass of the ball of radius `c R` (the bump `bumpPhi` vanishes for `‖x‖ ≥ 3/4`). -/
lemma bumpMass_le_mass_ball {c R : ℝ} (hc : 0 < c) (hR : 0 < R) (μ : Measure ℂ) (w : ℂ) :
    bumpMass c R μ w ≤ μ (ball w (c * R)) := by
  have hcR : 0 < c * R := mul_pos hc hR
  unfold bumpMass
  calc ∫⁻ u, ENNReal.ofReal (bumpPhi ((u - w) / ((c * R : ℝ) : ℂ))) ∂μ
      ≤ ∫⁻ u, (ball w (c * R)).indicator (fun _ => (1 : ENNReal)) u ∂μ := by
        refine lintegral_mono fun u => ?_
        by_cases hu : u ∈ ball w (c * R)
        · rw [Set.indicator_of_mem hu]
          exact ENNReal.ofReal_le_one.2 (bumpPhi_le_one _)
        · rw [Set.indicator_of_notMem hu]
          have hn : c * R ≤ ‖u - w‖ := by
            simp only [mem_ball, dist_eq_norm, not_lt] at hu; exact hu
          have hq : 3 / 4 ≤ ‖(u - w) / ((c * R : ℝ) : ℂ)‖ := by
            rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hcR.le, le_div_iff₀ hcR]
            linarith
          rw [bumpPhi_eq_zero hq, ENNReal.ofReal_zero]
    _ = μ (ball w (c * R)) := by
        rw [lintegral_indicator_const measurableSet_ball, one_mul]

/-- The sup of the exit-moment potential over `D = B_{R/4}(x)` is at most the printed `L_R(z)` (the kernel
`log(1/|u-v|)+1` is dominated by `printedKernel`, and `D ⊆ 𝔸_{R,2R}(z)` with the thickening inside `𝔸`). -/
lemma sup_log_le_printedL {z x : ℂ} {R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R / 100)
    (hxz : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100) (μ : Measure ℂ) :
    (⨆ v ∈ ball x (R / 4), ∫⁻ w in Metric.thickening δ (ball x (R / 4)),
        ENNReal.ofReal (Real.log (1 / ‖v - w‖) + 1) ∂μ) ≤ printedL R z μ := by
  refine iSup₂_le fun v hv => ?_
  have hDA : ball x (R / 4) ⊆ annulus z R (2 * R) := by
    simpa using ball_add_subset_annulus (δ := 0) hR (by linarith) hxz
  have hvA : v ∈ closure (annulus z R (2 * R)) := subset_closure (hDA hv)
  calc ∫⁻ w in Metric.thickening δ (ball x (R / 4)), ENNReal.ofReal (Real.log (1 / ‖v - w‖) + 1) ∂μ
      ≤ ∫⁻ w in Metric.thickening δ (ball x (R / 4)), printedKernel v w ∂μ := by
        refine lintegral_mono fun w => ?_
        unfold printedKernel
        split_ifs with h
        · exact le_top
        · rw [norm_sub_rev]
    _ ≤ ∫⁻ w in annulus z R (2 * R), printedKernel v w ∂μ :=
        lintegral_mono_set (thickening_ball_subset_annulus hR hδ hxz)
    _ ≤ printedL R z μ :=
        le_iSup₂ (f := fun v (_ : v ∈ closure (annulus z R (2 * R))) =>
          ∫⁻ w in annulus z R (2 * R), printedKernel v w ∂μ) v hvA

/-- **Second moment of the one-test count** (PRO step 8; B5 (B17)). For `ID = interiorCellVertices ε η (B_{R/4}(x))`,
`x = η(εb)` (the cell of `b` contains `x`), `D₀ = B_{3c₀R}(x)`, `σ_D = (vExitTime ID ·).toNat`, `V_occ = occCount A σ_D`:
`E_b[V_occ²] ≤ 32 C_exit² ((1 + N log 4) C_good)² ε⁻² (1 + log(1/R))² μ(D₀)²`.
Named inputs: `hmom` (first conjunct of `ExitTimeUpperBoundStmt`, Lemma 2.18, at `ω`), `hvol` (Lemma 2.7 lower half at `ω`),
`hgood` (`IsGoodAnnulusEvent`, the [C5] event, through `scaleCovGoodAnnulusEvent_of_isGoodAnnulusEvent`), `hcell` (cell
size), and the side conditions of the bridge (`hN` covering, `hpos`, `hfin`, `hatom`) and `hfinD` (finiteness of `μ(D₀)`). -/
theorem secondMoment_occCount (m : ℤ → ℤ → ℕ) (μ : Measure ℂ) (η : ℝ → ℂ) (ID A : Set ℤ)
    (ε R α ρ C_exit c₀ C_good βm h : ℝ) (N_cov : ℕ) (z x : ℂ) (b : ℤ)
    (hID : ID = interiorCellVertices ε η (ball x (R / 4)))
    (hε : 0 < ε) (hR : 0 < R) (hR1 : R ≤ 1) (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 5) (hCg : 0 ≤ C_good)
    (hεα : ε ^ α ≤ R / 100) (hεmass : ε ^ α ≤ (R / 4) ^ βm)
    (hb : b ∈ cellVertices ε η (sphere z (4 * R / 3)))
    (hx : x = η (ε * b))
    (hcell : ∀ p ∈ cell ε η b, ∀ q ∈ cell ε η b, dist p q ≤ h) (hh : h ≤ R / 100)
    (hx1 : ‖x‖ < 1 - R / 4)
    (hvol : ∀ y ∈ ball (0 : ℂ) (1 - R / 4), ENNReal.ofReal ((R / 4) ^ βm) ≤ μ (ball y (R / 4)))
    (hρ : ball x (R / 4) ⊆ ball 0 ρ)
    (hmom : ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : IsGoodAnnulusEvent μ c₀ C_good R z)
    (hN : ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
      (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : 0 < ⨅ w ∈ annulus z R (2 * R), μ (ball w (c₀ * R)))
    (hfin : μ (ball z (3 * R)) ≠ ⊤)
    (hatom : ∀ v ∈ annulus z R (2 * R), μ {v} = 0)
    (hfinD : μ (ball x (3 * c₀ * R)) ≠ ⊤) :
    ∫ w, occCount A (fun w => (vExitTime ID w).toNat) w ^ 2 ∂(srwLaw m b)
      ≤ 32 * C_exit ^ 2 * ((1 + N_cov * Real.log 4) * C_good) ^ 2 * (ε⁻¹) ^ 2
          * (1 + Real.log (1 / R)) ^ 2 * (μ (ball x (3 * c₀ * R))).toReal ^ 2 := by
  subst hID
  have hxcell : x ∈ cell ε η b := by
    rw [hx]
    exact ⟨ε * b, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  have hxz : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100 := by
    obtain ⟨p, hp1, hp2⟩ := hb
    have hpz : ‖p - z‖ = 4 * R / 3 := by
      rw [← dist_eq_norm]; exact mem_sphere.1 hp2
    have hd : dist x p ≤ h := hcell x hxcell p hp1
    have h3 : |‖x - z‖ - ‖p - z‖| ≤ dist x p := by
      rw [dist_eq_norm]
      have := abs_norm_sub_norm_le (x - z) (p - z)
      rwa [show (x - z) - (p - z) = x - p by ring] at this
    rw [hpz] at h3
    have h5 := abs_le.1 (h3.trans (hd.trans hh))
    constructor <;> linarith [h5.1, h5.2]
  have hxA : x ∈ annulus z R (2 * R) := by
    rw [mem_annulus_iff]; constructor <;> linarith [hxz.1, hxz.2]
  have hδ0 : 0 ≤ ε ^ α := Real.rpow_nonneg hε.le α
  have hEA : Metric.thickening (ε ^ α) (ball x (R / 4)) ⊆ annulus z R (2 * R) :=
    thickening_ball_subset_annulus hR hεα hxz
  have hxball : x ∈ ball (0 : ℂ) (1 - R / 4) := by
    rw [mem_ball, dist_zero_right]; exact hx1
  have hmassD : ENNReal.ofReal (ε ^ α) ≤ μ (ball x (R / 4)) :=
    (ENNReal.ofReal_le_ofReal hεmass).trans (hvol x hxball)
  have hxID : b ∈ cellVertices ε η (ball x (R / 4)) :=
    ⟨x, hxcell, mem_ball_self (by linarith)⟩
  have hM := hmom (ball x (R / 4)) measurableSet_ball hρ hmassD b hxID 2
  -- step 2 (PRO step 8; B5 (B15)): the potential is bounded by the printed L_R(z) on the good annulus
  set D0 := ball x (3 * c₀ * R) with hD0
  set Cg := (1 + N_cov * Real.log 4) * C_good with hCg_def
  have hlog4pos : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hCg0 : 0 ≤ Cg :=
    mul_nonneg (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hlog4pos)) hCg
  have hgoodS : ScaleCovGoodAnnulusEvent (3 * c₀) Cg R z μ :=
    scaleCovGoodAnnulusEvent_of_isGoodAnnulusEvent hN hc₀ hc₀' hR hgood hpos hfin hatom
  have hPL : printedL R z μ ≤ ENNReal.ofReal (Cg * (1 + |Real.log (4 * R)|)) * μ D0 := by
    refine (printedL_le_of_event hR hCg0 hgoodS).trans ?_
    refine mul_le_mul' le_rfl ?_
    refine (iInf₂_le x (subset_closure hxA)).trans ?_
    exact bumpMass_le_mass_ball (by linarith) hR μ x
  have hS := (sup_log_le_printedL hR hεα hxz μ).trans hPL
  -- real arithmetic
  set t := (μ D0).toReal with ht
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hμt : μ D0 = ENNReal.ofReal t := (ENNReal.ofReal_toReal hfinD).symm
  set a := Cg * (1 + |Real.log (4 * R)|) with ha
  have ha0 : 0 ≤ a := mul_nonneg hCg0 (by positivity)
  have hSb : (⨆ z' ∈ ball x (R / 4), ∫⁻ w in Metric.thickening (ε ^ α) (ball x (R / 4)),
      ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ≤ ENNReal.ofReal (a * t) := by
    refine hS.trans (le_of_eq ?_)
    rw [hμt, ENNReal.ofReal_mul ha0]
  have hpow : (⨆ z' ∈ ball x (R / 4), ∫⁻ w in Metric.thickening (ε ^ α) (ball x (R / 4)),
      ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ 2 ≤ ENNReal.ofReal ((a * t) ^ 2) := by
    rw [ENNReal.ofReal_pow (mul_nonneg ha0 ht0)]
    exact pow_le_pow_left₀ zero_le hSb 2
  have hF0 : 0 ≤ ((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ)) := by
    have : 0 < ε ^ (-((2 : ℕ) : ℝ)) := Real.rpow_pos_of_pos hε _
    positivity
  have hMQ : exitTimeMoment m (interiorCellVertices ε η (ball x (R / 4))) b 2
      ≤ ENNReal.ofReal (((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ)) * (a * t) ^ 2) := by
    calc exitTimeMoment m (interiorCellVertices ε η (ball x (R / 4))) b 2
        ≤ ENNReal.ofReal (((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ))) *
            (⨆ z' ∈ ball x (R / 4), ∫⁻ w in Metric.thickening (ε ^ α) (ball x (R / 4)),
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ 2 := hM
      _ ≤ ENNReal.ofReal (((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ))) *
            ENNReal.ofReal ((a * t) ^ 2) := mul_le_mul' le_rfl hpow
      _ = ENNReal.ofReal (((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ)) * (a * t) ^ 2) := by
          rw [ENNReal.ofReal_mul hF0]
  have hint := integral_le_toReal_of_lintegral_le (srwLaw m b) (fun w => sq_nonneg _) ENNReal.ofReal_ne_top
    ((lintegral_occCount_sq_le m A (interiorCellVertices ε η (ball x (R / 4))) b).trans hMQ)
  rw [ENNReal.toReal_ofReal (mul_nonneg hF0 (sq_nonneg _))] at hint
  -- the constant: 1 + |log 4R| ≤ 4 (1 + log(1/R)) and ε^(-2) = (ε⁻¹)^2
  have hL0 : 0 ≤ Real.log (1 / R) := Real.log_nonneg (one_le_one_div hR hR1)
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have hlogR : Real.log (4 * R) = Real.log 4 - Real.log (1 / R) := by
    rw [Real.log_mul (by norm_num) hR.ne', one_div, Real.log_inv]; ring
  have hlog : 1 + |Real.log (4 * R)| ≤ 4 * (1 + Real.log (1 / R)) := by
    rw [hlogR]
    have : |Real.log 4 - Real.log (1 / R)| ≤ 3 + Real.log (1 / R) :=
      abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hab : a ≤ Cg * (4 * (1 + Real.log (1 / R))) := mul_le_mul_of_nonneg_left hlog hCg0
  have hεpow : ε ^ (-((2 : ℕ) : ℝ)) = ε⁻¹ ^ 2 := by
    rw [Nat.cast_ofNat, Real.rpow_neg hε.le, Real.rpow_two, inv_pow]
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  have hat : a * t ≤ Cg * (4 * (1 + Real.log (1 / R))) * t := mul_le_mul_of_nonneg_right hab ht0
  calc ∫ w, occCount A (fun w => (vExitTime (interiorCellVertices ε η (ball x (R / 4))) w).toNat) w ^ 2
        ∂(srwLaw m b)
      ≤ ((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ)) * (a * t) ^ 2 := hint
    _ ≤ ((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ)) *
          (Cg * (4 * (1 + Real.log (1 / R))) * t) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg ha0 ht0) hat 2) hF0
    _ = 32 * C_exit ^ 2 * Cg ^ 2 * (ε⁻¹) ^ 2 * (1 + Real.log (1 / R)) ^ 2 * t ^ 2 := by
        rw [hεpow, hfac]; ring
    _ = 32 * C_exit ^ 2 * ((1 + N_cov * Real.log 4) * C_good) ^ 2 * (ε⁻¹) ^ 2
          * (1 + Real.log (1 / R)) ^ 2 * (μ (ball x (3 * c₀ * R))).toReal ^ 2 := by
        rw [hCg_def]

end Lemma68Window
end MatedCRT

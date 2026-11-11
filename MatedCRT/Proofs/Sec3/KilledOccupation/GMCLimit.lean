import MatedCRT.Proofs.Sec3.KilledOccupation.CircleAverageRepAgree
import MatedCRT.Proofs.Measurability.VagueMeasurable
import MatedCRT.LPStaging.Prob.VagueLimitMeasurable
import MatedCRT.Defs.Setting

/-!
# The γ-LQG measure on a cut-off disc as a vague limit of circle-average approximations

Let `χ = gmcCutoff ρ ρ₂` be a continuous radial cut-off, equal to `1` on `closedBall 0 ρ` and to `0`
off `ball 0 ρ₂`, with `ρ < ρ₂ < 1`. For a continuous circle-average representative `ψ` on the index set
`UnitDiskCircleIndex`, the measures `gmcApproxCut γ ρ ρ₂ k ψ = χ(x) ε_k^{γ²/2} exp (γ ψ̃(ε_k, x)) dx`,
with `ε_k = 2^{-k}`, are the cut-off approximations of the γ-Liouville quantum gravity measure
(Duplantier–Sheffield 2011, Prop. 1.1, along the full dyadic sequence). Their vague limit is the
γ-LQG measure restricted to the cut-off, `(μ ω).withDensity χ`, almost surely.

The limit is taken through the measurable choice of vague limits
`MatedCRT.VagueWholePlane.exists_measurable_vagueLimit`, so `gmcLimit γ ρ ρ₂` is a measurable map on
the canonical space `UnitDiskCircleIndex → ℝ`. The cut-off is continuous, so the limit does not depend on a
boundary convention at `∂B_ρ`, which an indicator of the disc would require (the approximations would
then fail vague convergence at the boundary unless the boundary is `μ`-null).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The continuous radial cut-off `χ_{ρ,ρ₂}(x) = min 1 (max 0 ((ρ₂ - ‖x‖) / (ρ₂ - ρ)))`: it equals `1`
on `closedBall 0 ρ`, vanishes off `ball 0 ρ₂`, and is affine in `‖x‖` in between (for `ρ < ρ₂`). -/
def gmcCutoff (ρ ρ₂ : ℝ) (x : ℂ) : ℝ :=
  min 1 (max 0 ((ρ₂ - ‖x‖) / (ρ₂ - ρ)))

/-- The cut-off circle-average density `χ(x) · ε^{γ²/2} exp (γ ψ̃(ε, x))` at the dyadic scale
`ε = 2^{-k}`, where `ψ̃` is the continuous representative `circleAverageRep`. -/
def gmcCutDensity (γ ρ ρ₂ : ℝ) (k : ℕ) (ψ : UnitDiskCircleIndex → ℝ) (x : ℂ) : ℝ :=
  gmcCutoff ρ ρ₂ x * (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ (dyadicScale k) x))

/-- The cut-off approximation `gmcApproxCut γ ρ ρ₂ k ψ = gmcCutDensity γ ρ ρ₂ k ψ · dx` of the γ-LQG
measure on `ℂ`. -/
def gmcApproxCut (γ ρ ρ₂ : ℝ) (k : ℕ) (ψ : UnitDiskCircleIndex → ℝ) : Measure ℂ :=
  (volume : Measure ℂ).withDensity fun x => ENNReal.ofReal (gmcCutDensity γ ρ ρ₂ k ψ x)

lemma continuous_gmcCutoff (ρ ρ₂ : ℝ) : Continuous (gmcCutoff ρ ρ₂) := by
  unfold gmcCutoff
  exact continuous_const.min (continuous_const.max ((continuous_const.sub continuous_norm).div_const _))

lemma gmcCutoff_nonneg (ρ ρ₂ : ℝ) (x : ℂ) : 0 ≤ gmcCutoff ρ ρ₂ x :=
  le_min zero_le_one (le_max_left _ _)

lemma gmcCutoff_le_one (ρ ρ₂ : ℝ) (x : ℂ) : gmcCutoff ρ ρ₂ x ≤ 1 :=
  min_le_left _ _

lemma gmcCutoff_eq_one {ρ ρ₂ : ℝ} (hρ : ρ < ρ₂) {x : ℂ} (hx : ‖x‖ ≤ ρ) :
    gmcCutoff ρ ρ₂ x = 1 := by
  have h1 : 1 ≤ (ρ₂ - ‖x‖) / (ρ₂ - ρ) := by
    rw [le_div_iff₀ (sub_pos.2 hρ)]
    linarith
  exact min_eq_left (le_max_of_le_right h1)

lemma gmcCutoff_eq_zero {ρ ρ₂ : ℝ} (hρ : ρ < ρ₂) {x : ℂ} (hx : ρ₂ ≤ ‖x‖) :
    gmcCutoff ρ ρ₂ x = 0 := by
  have h1 : (ρ₂ - ‖x‖) / (ρ₂ - ρ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.2 hρ).le
  unfold gmcCutoff
  rw [max_eq_left h1]
  exact min_eq_right zero_le_one

lemma gmcCutoff_hasCompactSupport {ρ ρ₂ : ℝ} (hρ : ρ < ρ₂) :
    HasCompactSupport (gmcCutoff ρ ρ₂) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ρ₂) fun x hx =>
    gmcCutoff_eq_zero (x := x) hρ (le_of_lt (not_le.1 fun h => hx (mem_closedBall_zero_iff.2 h)))

lemma gmcCutDensity_nonneg (γ ρ ρ₂ : ℝ) (k : ℕ) (ψ : UnitDiskCircleIndex → ℝ) (x : ℂ) :
    0 ≤ gmcCutDensity γ ρ ρ₂ k ψ x :=
  mul_nonneg (gmcCutoff_nonneg ρ ρ₂ x)
    (mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le)

/-- Joint measurability of the cut-off density in the field and the point. -/
lemma measurable_uncurry_gmcCutDensity (γ ρ ρ₂ : ℝ) (k : ℕ) :
    Measurable (Function.uncurry (gmcCutDensity γ ρ ρ₂ k)) := by
  have h1 : Measurable fun p : (UnitDiskCircleIndex → ℝ) × ℂ => gmcCutoff ρ ρ₂ p.2 :=
    (continuous_gmcCutoff ρ ρ₂).measurable.comp measurable_snd
  have h2 : Measurable fun p : (UnitDiskCircleIndex → ℝ) × ℂ =>
      dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep p.1 (dyadicScale k) p.2) :=
    measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_circleAverageRep (dyadicScale k))))
  exact h1.mul h2

lemma measurable_gmcApproxCut (γ ρ ρ₂ : ℝ) (k : ℕ) : Measurable (gmcApproxCut γ ρ ρ₂ k) := by
  unfold gmcApproxCut
  exact measurable_withDensity
    (f := fun ψ x => ENNReal.ofReal (gmcCutDensity γ ρ ρ₂ k ψ x))
    (ENNReal.measurable_ofReal.comp (measurable_uncurry_gmcCutDensity γ ρ ρ₂ k))

lemma measurable_integral_gmcApproxCut (γ ρ ρ₂ : ℝ) (k : ℕ) {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable fun ψ => ∫ z, f z ∂(gmcApproxCut γ ρ ρ₂ k ψ) :=
  (LatticeProb.measurable_integral_measure hf).comp (measurable_gmcApproxCut γ ρ ρ₂ k)

/-- A measurable choice of the vague limit of the cut-off approximations along the full dyadic sequence,
on the canonical space `UnitDiskCircleIndex → ℝ` (`MatedCRT.VagueWholePlane.exists_measurable_vagueLimit`). -/
lemma exists_gmcLimit (γ ρ ρ₂ : ℝ) :
    ∃ μ' : (UnitDiskCircleIndex → ℝ) → Measure ℂ, Measurable μ' ∧
      ∀ ψ m, (∀ K, IsCompact K → ∀ᶠ k in atTop, gmcApproxCut γ ρ ρ₂ k ψ K < ∞) →
        QuantumZipper.IsVagueLimitOn univ (fun k => gmcApproxCut γ ρ ρ₂ k ψ) m → μ' ψ = m :=
  MatedCRT.VagueWholePlane.exists_measurable_vagueLimit (fun k => gmcApproxCut γ ρ ρ₂ k)
    (measurable_gmcApproxCut γ ρ ρ₂)
    fun k _f hf _ => measurable_integral_gmcApproxCut γ ρ ρ₂ k hf.measurable

/-- The γ-LQG measure on the cut-off disc: the vague limit of `gmcApproxCut γ ρ ρ₂ k` along the full
dyadic sequence `k ↦ 2^{-k}`, chosen measurably (`exists_gmcLimit`). Off the convergence set its value is
unspecified; no consumer uses it there. -/
def gmcLimit (γ ρ ρ₂ : ℝ) : (UnitDiskCircleIndex → ℝ) → Measure ℂ :=
  Classical.choose (exists_gmcLimit γ ρ ρ₂)

lemma measurable_gmcLimit (γ ρ ρ₂ : ℝ) : Measurable (gmcLimit γ ρ ρ₂) :=
  (Classical.choose_spec (exists_gmcLimit γ ρ ρ₂)).1

lemma gmcLimit_eq {γ ρ ρ₂ : ℝ} {ψ : UnitDiskCircleIndex → ℝ} {m : Measure ℂ}
    (hfin : ∀ K, IsCompact K → ∀ᶠ k in atTop, gmcApproxCut γ ρ ρ₂ k ψ K < ∞)
    (hlim : QuantumZipper.IsVagueLimitOn univ (fun k => gmcApproxCut γ ρ ρ₂ k ψ) m) :
    gmcLimit γ ρ ρ₂ ψ = m :=
  (Classical.choose_spec (exists_gmcLimit γ ρ ρ₂)).2 ψ m hfin hlim

/-- Integration against a density `ENNReal.ofReal r` with `r ≥ 0` measurable. -/
lemma integral_withDensity_ofReal_eq {μ : Measure ℂ} {r : ℂ → ℝ} (hr : ∀ z, 0 ≤ r z)
    (hm : Measurable r) (g : ℂ → ℝ) :
    ∫ z, g z ∂(μ.withDensity fun z => ENNReal.ofReal (r z)) = ∫ z, r z * g z ∂μ := by
  have hf : Measurable fun z => (r z).toNNReal := hm.real_toNNReal
  have hdens : (fun z => ENNReal.ofReal (r z)) = fun z => (((r z).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hdens, integral_withDensity_eq_integral_smul hf]
  congr 1
  funext z
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hr z)]

lemma mem_unitDiskCircleIndex_of_lt {ρ₂ ε : ℝ} {x : ℂ} (hε : 0 < ε) (hεle : ε ≤ 1 - ρ₂)
    (hx : ‖x‖ < ρ₂) : (ε, x) ∈ UnitDiskCircleIndex := by
  show 0 < ε ∧ closedBall x ε ⊆ ball (0 : ℂ) 1
  refine ⟨hε, fun y hy => ?_⟩
  rw [mem_closedBall, dist_eq_norm] at hy
  rw [mem_ball_zero_iff]
  have h1 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
  linarith

/-- For `‖x‖ < ρ₂` and `ε ≤ 1 - ρ₂`, the circle average representative at `(ε, x)` is the value of the
continuous field there (the index circle lies in the unit disc). -/
lemma circleAverageRep_eq_of_lt {ρ₂ ε : ℝ} {x : ℂ} {H : ℝ → ℂ → ℝ} {ψ : UnitDiskCircleIndex → ℝ}
    (hψ : Continuous ψ) (hH : ∀ q : UnitDiskCircleIndex, ψ q = H q.1.1 q.1.2)
    (hε : 0 < ε) (hεle : ε ≤ 1 - ρ₂) (hx : ‖x‖ < ρ₂) :
    circleAverageRep ψ ε x = H ε x := by
  have h := mem_unitDiskCircleIndex_of_lt hε hεle hx
  rw [circleAverageRep_eq_of_continuous hψ h]
  exact hH ⟨(ε, x), h⟩

/-- The cut-off density at a dyadic scale below `1 - ρ₂` is the cut-off times the field's own density. -/
lemma gmcCutDensity_eq_of_lt {γ ρ ρ₂ : ℝ} (hρ : ρ < ρ₂) {H : ℝ → ℂ → ℝ} {ψ : UnitDiskCircleIndex → ℝ}
    (hψ : Continuous ψ) (hH : ∀ q : UnitDiskCircleIndex, ψ q = H q.1.1 q.1.2) {k : ℕ}
    (hk : dyadicScale k ≤ 1 - ρ₂) (x : ℂ) :
    gmcCutDensity γ ρ ρ₂ k ψ x =
      gmcCutoff ρ ρ₂ x * (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicScale k) x)) := by
  unfold gmcCutDensity
  by_cases hx : ‖x‖ < ρ₂
  · rw [circleAverageRep_eq_of_lt hψ hH (dyadicScale_pos k) hk hx]
  · simp [gmcCutoff_eq_zero hρ (not_lt.1 hx)]

/-- **Cut-off GMC limit as the cut-off LQG measure.** If the field `H` has continuous circle averages on
`(0, ∞) × ℂ`-restrictions to the index set `ψ`, and `μ` is its LQG measure (vague limit along the dyadic
scales), then the measurable limit `gmcLimit γ ρ ρ₂ ψ` equals `μ.withDensity χ`. Steps B1–B6 of
MQ-li-16 (3). -/
theorem gmcLimit_eq_withDensity_of_continuous {γ ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1)
    {H : ℝ → ℂ → ℝ} {ψ : UnitDiskCircleIndex → ℝ} (hψ : Continuous ψ)
    (hH : ∀ q : UnitDiskCircleIndex, ψ q = H q.1.1 q.1.2) {μ : Measure ℂ} (hL : IsLQGLimit γ H μ)
    (hHc : ∀ ε : ℝ, 0 < ε → Continuous fun x => H ε x) :
    gmcLimit γ ρ ρ₂ ψ = μ.withDensity fun x => ENNReal.ofReal (gmcCutoff ρ ρ₂ x) := by
  have := hL.isLocallyFiniteMeasure
  -- B2: for all large `k`, the dyadic scale is below `1 - ρ₂`, and the density is the field's density.
  have ht : Tendsto (fun k : ℕ => dyadicScale k) atTop (𝓝 0) := by
    unfold dyadicScale
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hk₀ : ∀ᶠ k in atTop, dyadicScale k ≤ 1 - ρ₂ :=
    ht.eventually (Iic_mem_nhds (by linarith : (0 : ℝ) < 1 - ρ₂))
  have hstar : ∀ᶠ k in atTop, ∀ x, gmcCutDensity γ ρ ρ₂ k ψ x =
      gmcCutoff ρ ρ₂ x * (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicScale k) x)) :=
    hk₀.mono fun k hk x => gmcCutDensity_eq_of_lt hρρ₂ hψ hH hk x
  -- B3: integrals against the approximations agree with the LQG approximations weighted by the cut-off.
  have hB3 : ∀ f : ℂ → ℝ, ∀ᶠ k in atTop,
      ∫ z, f z ∂(gmcApproxCut γ ρ ρ₂ k ψ) =
        ∫ z, f z * gmcCutoff ρ ρ₂ z ∂(volume.withDensity fun z =>
          ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicScale k) z))) := by
    intro f
    filter_upwards [hstar] with k hk
    have hm1 : Measurable (gmcCutDensity γ ρ ρ₂ k ψ) :=
      (measurable_uncurry_gmcCutDensity γ ρ ρ₂ k).comp (measurable_const.prodMk measurable_id)
    have hm2 : Measurable fun z => dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicScale k) z) :=
      (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul (hHc _ (dyadicScale_pos k))))).measurable
    have hr2 : ∀ z, 0 ≤ dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicScale k) z) :=
      fun z => mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le
    unfold gmcApproxCut
    rw [integral_withDensity_ofReal_eq (μ := volume) (gmcCutDensity_nonneg γ ρ ρ₂ k ψ) hm1 f,
      integral_withDensity_ofReal_eq (μ := volume) hr2 hm2 (fun z => f z * gmcCutoff ρ ρ₂ z)]
    congr 1
    funext z
    rw [hk z]
    ring
  have hχ : Measurable (gmcCutoff ρ ρ₂) := (continuous_gmcCutoff ρ ρ₂).measurable
  -- B4: the vague limit property of the cut-off LQG measure.
  have hlim : QuantumZipper.IsVagueLimitOn univ (fun k => gmcApproxCut γ ρ ρ₂ k ψ)
      (μ.withDensity fun x => ENNReal.ofReal (gmcCutoff ρ ρ₂ x)) := by
    refine ⟨by rw [compl_univ, measure_empty], ?_, ?_⟩
    · intro K hK _
      rw [withDensity_apply _ hK.measurableSet]
      calc ∫⁻ x in K, ENNReal.ofReal (gmcCutoff ρ ρ₂ x) ∂μ ≤ ∫⁻ _ in K, 1 ∂μ :=
            lintegral_mono fun x => ENNReal.ofReal_le_one.2 (gmcCutoff_le_one ρ ρ₂ x)
        _ = μ K := by simp
        _ < ⊤ := hK.measure_lt_top
    · intro f hf hcs _
      have hfχ : Continuous fun z => f z * gmcCutoff ρ ρ₂ z := hf.mul (continuous_gmcCutoff ρ ρ₂)
      have hfχcs : HasCompactSupport fun z => f z * gmcCutoff ρ ρ₂ z :=
        hcs.mul_right (f' := gmcCutoff ρ ρ₂)
      have hlimL := hL.tendsto_integral (fun z => f z * gmcCutoff ρ ρ₂ z) hfχ hfχcs
      have hmeq : ∫ z, f z ∂(μ.withDensity fun x => ENNReal.ofReal (gmcCutoff ρ ρ₂ x)) =
          ∫ z, f z * gmcCutoff ρ ρ₂ z ∂μ := by
        rw [integral_withDensity_ofReal_eq (μ := μ) (gmcCutoff_nonneg ρ ρ₂) hχ f]
        congr 1
        funext z
        ring
      rw [hmeq]
      exact Tendsto.congr' ((hB3 f).mono fun k hk => hk.symm) hlimL
  -- B5: the approximations are finite on compact sets for large `k`.
  have hfin : ∀ K, IsCompact K → ∀ᶠ k in atTop, gmcApproxCut γ ρ ρ₂ k ψ K < ∞ := by
    intro K hK
    filter_upwards [hstar] with k hk
    have hg : Continuous fun x => gmcCutoff ρ ρ₂ x *
        (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicScale k) x)) :=
      (continuous_gmcCutoff ρ ρ₂).mul (continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul (hHc _ (dyadicScale_pos k)))))
    have heq : gmcApproxCut γ ρ ρ₂ k ψ = (volume : Measure ℂ).withDensity fun x =>
        ENNReal.ofReal (gmcCutoff ρ ρ₂ x *
          (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicScale k) x))) := by
      unfold gmcApproxCut
      congr 1
      funext x
      rw [hk x]
    rw [heq, withDensity_apply _ hK.measurableSet]
    exact (hg.continuousOn.integrableOn_compact hK).lintegral_lt_top
  -- B6
  exact gmcLimit_eq hfin hlim

/-- **BRIDGE.** Let `μ` be the γ-LQG measure of a random field `hε` (`IsLQGMeasure`) whose circle averages are
almost surely continuous on `(0, ∞) × ℂ`. Then, almost surely, the measurable cut-off limit
`gmcLimit γ ρ ρ₂` of the circle averages equals the cut-off LQG measure `(μ ω).withDensity χ`. -/
theorem ae_gmcLimit_eq_withDensity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hε : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hμ : IsLQGMeasure P γ hε μ)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hε ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) :
    ∀ᵐ ω ∂P, gmcLimit γ ρ ρ₂ (fun q : UnitDiskCircleIndex => hε ω q.1.1 q.1.2) =
      (μ ω).withDensity fun x => ENNReal.ofReal (gmcCutoff ρ ρ₂ x) := by
  filter_upwards [hμ, hcont] with ω hL hc
  -- B1: the restriction of the field to the index set is continuous.
  have hψc : Continuous (fun q : UnitDiskCircleIndex => hε ω q.1.1 q.1.2) :=
    hc.comp_continuous continuous_subtype_val (fun q => ⟨q.2.1, Set.mem_univ _⟩)
  exact gmcLimit_eq_withDensity_of_continuous hρρ₂ hρ₂ hψc (fun _ => rfl) hL
    (fun ε hε => hc.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨hε, Set.mem_univ _⟩))

/-- **Restriction to a disc inside the cut-off.** Almost surely, the cut-off GMC limit restricted to a
measurable set `D ⊆ closedBall 0 ρ` equals the restriction of the LQG measure `μ ω`. -/
theorem ae_gmcLimit_restrict_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hε : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hμ : IsLQGMeasure P γ hε μ)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hε ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) {D : Set ℂ} (hD : MeasurableSet D)
    (hDρ : D ⊆ closedBall 0 ρ) :
    ∀ᵐ ω ∂P, (gmcLimit γ ρ ρ₂ (fun q : UnitDiskCircleIndex => hε ω q.1.1 q.1.2)).restrict D =
      (μ ω).restrict D := by
  filter_upwards [ae_gmcLimit_eq_withDensity hμ hcont hρρ₂ hρ₂] with ω hω
  have hχ1 : ∀ᵐ x ∂((μ ω).restrict D), ENNReal.ofReal (gmcCutoff ρ ρ₂ x) = 1 :=
    ae_restrict_of_forall_mem hD fun x hx => by
      rw [gmcCutoff_eq_one hρρ₂ (mem_closedBall_zero_iff.1 (hDρ hx))]
      simp
  rw [hω, restrict_withDensity hD, withDensity_congr_ae hχ1]
  exact withDensity_one

/-- **Cone instance.** For the γ-quantum cone environment `S` (`S.IsValid 𝒮 γ`), the circle averages
`S.hcirc` have a.s. continuous representatives on `(0, ∞) × ℂ` (`IsQuantumCone.ae_continuousOn_circle`), so the
cut-off GMC limit of `S.hcirc` equals the cut-off of `S.μ`. Only `ρ < 1` is needed; `ρ₂ = (1 + ρ) / 2`. -/
theorem ae_gmcLimit_cone_eq_withDensity {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (𝒮 : SpaceFillingSLEModel) (γ : ℝ) (hS : S.IsValid 𝒮 γ) {ρ : ℝ} (hρ : ρ < 1) :
    ∀ᵐ ω ∂S.P, gmcLimit γ ρ ((1 + ρ) / 2) (fun q : UnitDiskCircleIndex => S.hcirc ω q.1.1 q.1.2) =
      (S.μ ω).withDensity fun x => ENNReal.ofReal (gmcCutoff ρ ((1 + ρ) / 2) x) :=
  ae_gmcLimit_eq_withDensity hS.isLQGMeasure hS.isQuantumCone.ae_continuousOn_circle
    (by linarith) (by linarith)

end MatedCRT.KilledOccupation

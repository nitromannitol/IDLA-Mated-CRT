import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd
import MatedCRT.FirstPass.Derived.CurveMultOuterTransfer
import MatedCRT.FirstPass.Derived.CellSumOfLocalizedIntegral
import MatedCRT.FirstPass.SLERef.Reference
import LatticeProb.LQG.Prop210BallSource

/-!
# The single-ball cell sum bound (GMS19, Proposition 2.9) in every valid environment

Gwynne–Miller–Sheffield (2019), Propositions 2.9 and 2.10, as used in Berestycki–Gwynne (2020), Lemma 5.3, Step 3.
Fix `γ ∈ (0, 2)`. With exponents `β₀, α₀ > 0` chosen before the radius `ρ' ∈ (0, 1)` and a threshold `A` depending
on `ρ'` only, in every valid environment `S` every ball `B_r(z) ⊆ B_{ρ'}(0)` of radius `r ≥ ε^{β₀}` has cell sum
`∑_{k ∈ T} deg(k) diam(H_k)² ≤ A r²` over the vertices `T ⊆ V^ε(B_r(z))`, except on an event of outer probability
at most `C ε^{α₀}`.

* `exists_cellDiam_le_rpow_uniform`: the upper half of the cell size estimate (GMS19 Lemma 2.7) with the exponents
  `q, p` depending on `γ` only: every cell meeting `B_ρ(0)` has diameter at most `ε^q`, except on an event of
  probability at most `C ε^p`, with `C` depending on `ρ` and the environment.
* `hsingle_of_reference`: the single-ball bound in every valid environment of a model with normalized space-filling
  SLE law `ν` and valid reference environments on `ℝ`, on a one-sided mating-rigid set `G` that is full for every
  correlated Brownian law.

Route. In the reference environment `S'` on the standard Borel space `ℝ`, the mating-of-trees coupling of `S'` gives
the source-order Proposition 2.10 (`MatedCRTHarmonic.GMSMain.epsA_prop210Source`), hence the bound on the balls with
the test function one (`MatedCRTHarmonic.GMSMain.exists_epsAProp210Bad_ball_one_source`): off the failure event the
curve cells form a cellular embedding of the mated-CRT map with `∫_D u^ε ≤ A area(D) + ε^α`. For `r ≤ (1 - ρ')/4`
take `D = B_{2r}(z)`; the cells of `V^ε(B_r(z))` have diameter at most `ε^q ≤ r` and lie in `D`, so the cell sum is
at most `4 π A r² + ε^α ≤ (4 π A + 1) r²` when `r ≥ ε^{α/2}` (`sum_mdeg_mul_diam_sq_le_of_ball`). For larger `r`
take `D = B_{ρ''}(0)`, `ρ'' = (1 + ρ')/2`, once. The cell sum is a function of the curve and the edge
multiplicities, so its failure event in `S` has outer probability at most that in `S'`
(`measure_eta_mult_preimage_le_of_valid`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **The upper half of the cell size estimate with exponents depending on `γ` only** (GMS19 Lemma 2.7,
BG20 Lemma 2.4). For `γ ∈ (0, 2)` there are `q, p > 0` such that for every `ρ ∈ (0, 1)` and every valid environment
`S` there is `C ≥ 0` with: every cell `H^ε_k` meeting `B_ρ(0)` has `diam(H^ε_k) ≤ ε^q`, except on an event of
probability at most `C ε^p`, for every `ε ∈ (0, 1)`. -/
theorem exists_cellDiam_le_rpow_uniform (𝒮 : SpaceFillingSLEModel) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ q p : ℝ, 0 < q ∧ 0 < p ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∃ C : ℝ, 0 ≤ C ∧
        ∀ ε ∈ Ioo (0 : ℝ) 1, S.P {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
          diam (cell ε (S.η ω) k) ≤ ε ^ q}ᶜ ≤ ENNReal.ofReal (C * ε ^ p) := by
  have hsq : 0 < (2 + γ) ^ 2 := by positivity
  set q₀ : ℝ := 1 / (2 + γ) ^ 2
  have hq₀0 : 0 < q₀ := by positivity
  have hq₀' : q₀ < 2 / (2 + γ) ^ 2 := (div_lt_div_iff_of_pos_right hsq).mpr (by norm_num)
  have hα := MatedCRTHarmonic.GMSLemma27.lemma27Exponent_pos hγ hq₀0 hq₀'
  refine ⟨q₀, MatedCRTHarmonic.GMSLemma27.lemma27Exponent q₀ γ / 2, hq₀0, half_pos hα,
    fun ρ hρ hρ1 Ω _ S hS => ?_⟩
  have hdomM := areaDominates_prodRight_toCellModel hγ hγ2 hS
  obtain ⟨C, hC⟩ := lemma27_segments_of_prodRight (S.toCellModel hS) (brownianMotion 0)
    (MatedCRT.segmentsContainBalls_toCellModel hS) (MatedCRTHarmonic.GMCFacts.gmcLowerTail_holds hγ hγ2) hdomM hγ
    hq₀0 hq₀' hρ hρ1 (half_lt_self hα)
  refine ⟨max C 0, le_max_right _ _, fun ε hε => ?_⟩
  have hmono : ENNReal.ofReal (C * ε ^ (MatedCRTHarmonic.GMSLemma27.lemma27Exponent q₀ γ / 2)) ≤
      ENNReal.ofReal (max C 0 * ε ^ (MatedCRTHarmonic.GMSLemma27.lemma27Exponent q₀ γ / 2)) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.1.le _))
  refine le_trans (measure_mono ?_) ((hC ε hε).trans hmono)
  refine compl_subset_compl.mpr fun ω hω k hk => ?_
  exact hω _ _ (le_of_eq (by ring)) hk

/-- **GMS19 Proposition 2.9 for one ball, in every valid environment** (the single-ball input of the grid union
bound `MatedCRT.hball_of_pointwise`). Let `ν` be a normalized space-filling SLE law of the model `𝒮`, which has valid
reference environments on `ℝ`, and `G` a one-sided mating-rigid set that is full for every `γ`-correlated two-sided
Brownian law. For `γ ∈ (0, 2)` there are `β₀, α₀ > 0` such that for every `ρ' ∈ (0, 1)` there is `A > 0` with: in
every valid environment `S` there is `C` such that for every `ε ∈ (0, 1)` and every ball `B_r(z) ⊆ B_{ρ'}(0)` with
`r ≥ ε^{β₀}`, the event that some finite `T ⊆ V^ε(B_r(z))` has `∑_{k ∈ T} deg(k) diam(H_k)² > A r²` has outer
probability at most `C ε^{α₀}`. -/
theorem hsingle_of_reference {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2,
      MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ → μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ A : ℝ, 0 < A ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ (z : ℂ) (r : ℝ), ε ^ β₀ ≤ r → ball z r ⊆ ball 0 ρ' →
          S.P {ω | ¬ ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω) (ball z r)) →
            ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) * diam (cell ε (S.η ω) k) ^ 2 ≤ A * r ^ 2} ≤
              ENNReal.ofReal (C * ε ^ α₀) := by
  intro γ hγ hγ2
  -- the reference environment, its mating-of-trees coupling and the source-order Proposition 2.10
  obtain ⟨S', hS'⟩ := href γ hγ hγ2
  obtain ⟨_, _, _, _, _, _, _, _, _, η', _, hMoT, hae⟩ := hS'.matingOfTrees
  have hη'ae : ∀ᵐ ω ∂S'.P, ⇑(η' ω) = S'.η ω := hae.mono fun ω h => h.1
  have hN : S'.P {ω | ¬ ⇑(η' ω) = S'.η ω} = 0 := ae_iff.1 hη'ae
  obtain ⟨α, hα, hball⟩ := MatedCRTHarmonic.GMSMain.exists_epsAProp210Bad_ball_one_source
    (MatedCRTHarmonic.GMSMain.epsA_prop210Source hMoT inferInstance ⟨hγ, hγ2⟩)
  obtain ⟨q, p, hq, hp, hcell⟩ := exists_cellDiam_le_rpow_uniform 𝒮 hγ hγ2
  refine ⟨min (α / 2) q, min α p, lt_min (half_pos hα) hq, lt_min hα hp, fun ρ' hρ' hρ'1 => ?_⟩
  set β₀ : ℝ := min (α / 2) q
  set α₀ : ℝ := min α p
  set ρ'' : ℝ := (1 + ρ') / 2 with hρ''
  set d : ℝ := (1 - ρ') / 4 with hd_def
  have hρ''0 : 0 < ρ'' := by rw [hρ'']; linarith
  have hρ''1 : ρ'' < 1 := by rw [hρ'']; linarith
  have hd : 0 < d := by rw [hd_def]; linarith
  obtain ⟨A, hA, Cfail, hCfail, hbad⟩ := hball ρ'' hρ''0 hρ''1
  obtain ⟨Ccell, hCcell, hcellS'⟩ := hcell ρ' hρ' hρ'1 ℝ S' hS'
  have hπA : 0 < A * Real.pi := mul_pos hA Real.pi_pos
  set A' : ℝ := max (4 * Real.pi * A + 1) ((A * Real.pi + 1) / d ^ 2)
  have hA'1 : 4 * Real.pi * A + 1 ≤ A' := le_max_left _ _
  have hA'2 : (A * Real.pi + 1) / d ^ 2 ≤ A' := le_max_right _ _
  have hA'0 : 0 < A' := lt_of_lt_of_le (by linarith) hA'1
  refine ⟨A', hA'0, fun Ω _ S hS => ?_⟩
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  -- below the mesh `ε₁ = d^{1/q}` the cells have diameter `< d`; above it the bound is trivial
  set ε₁ : ℝ := d ^ q⁻¹
  have hε₁0 : 0 < ε₁ := Real.rpow_pos_of_pos hd _
  have hε₁q : ε₁ ^ q = d := Real.rpow_inv_rpow hd.le hq.ne'
  set K : ℝ := (ε₁ ^ α₀)⁻¹
  have hε₁α₀ : 0 < ε₁ ^ α₀ := Real.rpow_pos_of_pos hε₁0 _
  have hK0 : 0 ≤ K := (inv_pos.2 hε₁α₀).le
  refine ⟨Cfail + Ccell + K, fun ε hε0 hε1 z r hr hsub => ?_⟩
  have hεα₀ : 0 ≤ ε ^ α₀ := Real.rpow_nonneg hε0.le _
  by_cases hεε₁ : ε₁ ≤ ε
  · -- trivial range of meshes
    refine (prob_le_one).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ε₁ ^ α₀ ≤ ε ^ α₀ := Real.rpow_le_rpow hε₁0.le hεε₁ (lt_min hα hp).le
    have h2 : K * ε₁ ^ α₀ = 1 := inv_mul_cancel₀ hε₁α₀.ne'
    have h3 : K * ε₁ ^ α₀ ≤ K * ε ^ α₀ := mul_le_mul_of_nonneg_left h1 hK0
    have h4 : 0 ≤ Cfail * ε ^ α₀ := mul_nonneg hCfail hεα₀
    have h5 : 0 ≤ Ccell * ε ^ α₀ := mul_nonneg hCcell hεα₀
    linarith
  have hεε₁' : ε < ε₁ := not_le.1 hεε₁
  have hεq : ε ^ q < d := by
    rw [← hε₁q]
    exact Real.rpow_lt_rpow hε0.le hεε₁' hq
  have hr0 : 0 < r := (Real.rpow_pos_of_pos hε0 β₀).trans_le hr
  have hqr : ε ^ q ≤ r :=
    (Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (min_le_right _ _)).trans hr
  have htol0 : 0 ≤ ε ^ α := Real.rpow_nonneg hε0.le _
  have hzρ : dist z 0 < ρ' := mem_ball.1 (hsub (mem_ball_self hr0))
  -- the failure event of the cell size estimate in the reference environment
  set CellFail : Set ℝ := {ω | ∀ k : ℤ, (cell ε (S'.η ω) k ∩ ball 0 ρ').Nonempty →
    diam (cell ε (S'.η ω) k) ≤ ε ^ q}ᶜ
  -- the deterministic step: off the failure event of Proposition 2.10 at a suitable domain, off the failure
  -- event of the cell size estimate and on the full event `η' = S'.η`, the cell sum is at most `A' r²`
  have key : ∃ Bad : Set ℝ, S'.P Bad ≤ ENNReal.ofReal (Cfail * ε ^ α) ∧
      ∀ ω, ω ∉ Bad → ω ∉ CellFail → ⇑(η' ω) = S'.η ω → ∀ T : Finset ℤ,
        (∀ k ∈ T, k ∈ cellVertices ε (S'.η ω) (ball z r)) →
          ∑ k ∈ T, (mdeg (S'.mult ε ω) k : ℝ) * diam (cell ε (S'.η ω) k) ^ 2 ≤ A' * r ^ 2 := by
    have hcl' : ∀ ω, ω ∉ CellFail → ∀ k : ℤ, (cell ε (S'.η ω) k ∩ ball 0 ρ').Nonempty →
        diam (cell ε (S'.η ω) k) ≤ ε ^ q := fun ω hcl k hk => by
      by_contra h
      exact hcl (fun hall => h (hall k hk))
    by_cases hrd : r ≤ d
    · -- small balls: the domain `B_{2r}(z)`
      have hsub2 : ball z (2 * r) ⊆ ball 0 ρ'' := by
        intro w hw
        rw [mem_ball] at hw ⊢
        have := dist_triangle w z 0
        rw [hρ'']
        linarith
      refine ⟨_, hbad ε ⟨hε0, hε1⟩ z (2 * r) (by linarith) hsub2, fun ω hb hcl hn T hT => ?_⟩
      have h := MatedCRTHarmonic.GMSMain.lintegral_uDens_ball_le_of_not_mem_epsAProp210Bad hb
      obtain ⟨hlf, H, hHc⟩ := h.1
      have hP := h.2 hlf H hHc
      have hH : ∀ x : ℤ, H.cell x = cell ε (S'.η ω) x := fun x => by
        rw [hHc x, hn]
        try rfl
      have hη : Continuous (S'.η ω) := by
        rw [← hn]
        exact (η' ω).continuous
      have hdeg : ∀ x : ℤ, (MatedCRTHarmonic.MatedCRT.graph ε (S'.bm ω) hlf).deg x =
          mdeg (S'.mult ε ω) x := fun x => S'.deg_graph_eq hε0.le hlf x
      have hsz : ∀ k ∈ T, diam (cell ε (S'.η ω) k) ≤ r := fun k hk => by
        obtain ⟨y, hyc, hyb⟩ := hT k hk
        exact (hcl' ω hcl k ⟨y, hyc, hsub hyb⟩).trans hqr
      have hsum := sum_mdeg_mul_diam_sq_le_of_ball H hdeg hH hη T hr0 hT hsz hA.le htol0 hP
      have h2 : ε ^ (α / 2) ≤ r :=
        (Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (min_le_left _ _)).trans hr
      have hhalf : ε ^ α = ε ^ (α / 2) * ε ^ (α / 2) := by
        rw [← Real.rpow_add hε0, add_halves]
      have htolr : ε ^ α ≤ r ^ 2 := by
        rw [hhalf, sq]
        exact mul_le_mul h2 h2 (Real.rpow_nonneg hε0.le _) hr0.le
      have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
      have h3 : (4 * Real.pi * A + 1) * r ^ 2 ≤ A' * r ^ 2 := mul_le_mul_of_nonneg_right hA'1 hr2
      linarith
    · -- large balls: the domain `B_{ρ''}(0)`
      have hrd' : d < r := not_le.1 hrd
      refine ⟨_, hbad ε ⟨hε0, hε1⟩ 0 ρ'' hρ''0 Subset.rfl, fun ω hb hcl hn T hT => ?_⟩
      have h := MatedCRTHarmonic.GMSMain.lintegral_uDens_ball_le_of_not_mem_epsAProp210Bad hb
      obtain ⟨hlf, H, hHc⟩ := h.1
      have hP := h.2 hlf H hHc
      have hH : ∀ x : ℤ, H.cell x = cell ε (S'.η ω) x := fun x => by
        rw [hHc x, hn]
        try rfl
      have hη : Continuous (S'.η ω) := by
        rw [← hn]
        exact (η' ω).continuous
      have hdeg : ∀ x : ℤ, (MatedCRTHarmonic.MatedCRT.graph ε (S'.bm ω) hlf).deg x =
          mdeg (S'.mult ε ω) x := fun x => S'.deg_graph_eq hε0.le hlf x
      have hsubT : ∀ k ∈ T, cell ε (S'.η ω) k ⊆ ball 0 ρ'' := by
        intro k hk w hw
        obtain ⟨y, hyc, hyb⟩ := hT k hk
        have hdiam := hcl' ω hcl k ⟨y, hyc, hsub hyb⟩
        have hbdd : Bornology.IsBounded (cell ε (S'.η ω) k) := (isCompact_Icc.image hη).isBounded
        have h1 : dist w y ≤ diam (cell ε (S'.η ω) k) := dist_le_diam_of_mem hbdd hw hyc
        have h2 : dist y 0 < ρ' := mem_ball.1 (hsub hyb)
        have h3 := dist_triangle w y 0
        rw [mem_ball, hρ'']
        rw [hd_def] at hεq
        linarith
      have hsum := sum_mdeg_mul_diam_sq_le_of_lintegral_bound H hdeg hH T isBounded_ball hsubT hA.le htol0 hP
      have hv : (volume (ball (0 : ℂ) ρ'')).toReal = Real.pi * ρ'' ^ 2 := by
        rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal hρ''0.le, ENNReal.coe_toReal, NNReal.coe_real_pi]
        ring
      rw [hv] at hsum
      have hρ''sq : ρ'' ^ 2 ≤ 1 := by
        have h4 := mul_le_mul hρ''1.le hρ''1.le hρ''0.le zero_le_one
        rw [sq]
        linarith
      have hpiA : A * (Real.pi * ρ'' ^ 2) ≤ A * Real.pi := by
        have h4 : Real.pi * ρ'' ^ 2 ≤ Real.pi * 1 := mul_le_mul_of_nonneg_left hρ''sq Real.pi_pos.le
        rw [mul_one] at h4
        exact mul_le_mul_of_nonneg_left h4 hA.le
      have htol1 : ε ^ α ≤ 1 := Real.rpow_le_one hε0.le hε1.le hα.le
      have hd2 : d ^ 2 ≤ r ^ 2 := by
        rw [sq, sq]
        exact mul_le_mul hrd'.le hrd'.le hd.le hr0.le
      have hlarge : A * Real.pi + 1 ≤ (A * Real.pi + 1) / d ^ 2 * r ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hd 2)]
        exact mul_le_mul_of_nonneg_left hd2 (by linarith)
      have h3 : (A * Real.pi + 1) / d ^ 2 * r ^ 2 ≤ A' * r ^ 2 :=
        mul_le_mul_of_nonneg_right hA'2 (sq_nonneg r)
      linarith
  obtain ⟨Bad, hBad, hgood⟩ := key
  -- the transfer to `S` and the union bound in the reference environment
  have htrans := measure_eta_mult_preimage_le_of_valid hν hν hγ hγ2 hS hS' (hGnull γ hγ hγ2) hG ε
    {pr : (ℝ → ℂ) × (ℤ → ℤ → ℕ) | ¬ ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε pr.1 (ball z r)) →
      ∑ k ∈ T, (mdeg pr.2 k : ℝ) * diam (cell ε pr.1 k) ^ 2 ≤ A' * r ^ 2}
  have hsubU : {ω | (S'.η ω, S'.mult ε ω) ∈ {pr : (ℝ → ℂ) × (ℤ → ℤ → ℕ) | ¬ ∀ T : Finset ℤ,
      (∀ k ∈ T, k ∈ cellVertices ε pr.1 (ball z r)) →
        ∑ k ∈ T, (mdeg pr.2 k : ℝ) * diam (cell ε pr.1 k) ^ 2 ≤ A' * r ^ 2}} ⊆
      (Bad ∪ CellFail) ∪ {ω | ¬ ⇑(η' ω) = S'.η ω} := by
    intro ω hω
    by_contra hc
    simp only [mem_union, not_or, mem_ofPred_eq, not_not] at hc
    obtain ⟨⟨hb, hcl⟩, hn⟩ := hc
    exact hω (hgood ω hb hcl hn)
  have hCF : S'.P CellFail ≤ ENNReal.ofReal (Ccell * ε ^ p) := hcellS' ε ⟨hε0, hε1⟩
  have hfin : Cfail * ε ^ α + Ccell * ε ^ p ≤ (Cfail + Ccell + K) * ε ^ α₀ := by
    have h1 : ε ^ α ≤ ε ^ α₀ := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (min_le_left _ _)
    have h2 : ε ^ p ≤ ε ^ α₀ := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (min_le_right _ _)
    have h3 : Cfail * ε ^ α ≤ Cfail * ε ^ α₀ := mul_le_mul_of_nonneg_left h1 hCfail
    have h4 : Ccell * ε ^ p ≤ Ccell * ε ^ α₀ := mul_le_mul_of_nonneg_left h2 hCcell
    have h5 : 0 ≤ K * ε ^ α₀ := mul_nonneg hK0 hεα₀
    linarith
  calc S.P {ω | ¬ ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω) (ball z r)) →
        ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) * diam (cell ε (S.η ω) k) ^ 2 ≤ A' * r ^ 2}
      ≤ S'.P {ω | (S'.η ω, S'.mult ε ω) ∈ {pr : (ℝ → ℂ) × (ℤ → ℤ → ℕ) | ¬ ∀ T : Finset ℤ,
          (∀ k ∈ T, k ∈ cellVertices ε pr.1 (ball z r)) →
            ∑ k ∈ T, (mdeg pr.2 k : ℝ) * diam (cell ε pr.1 k) ^ 2 ≤ A' * r ^ 2}} := htrans
    _ ≤ S'.P ((Bad ∪ CellFail) ∪ {ω | ¬ ⇑(η' ω) = S'.η ω}) := measure_mono hsubU
    _ ≤ S'.P Bad + S'.P CellFail + S'.P {ω | ¬ ⇑(η' ω) = S'.η ω} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (Cfail * ε ^ α) + ENNReal.ofReal (Ccell * ε ^ p) + 0 := by
        rw [hN]
        exact add_le_add (add_le_add hBad hCF) le_rfl
    _ = ENNReal.ofReal (Cfail * ε ^ α + Ccell * ε ^ p) := by
        rw [add_zero, ENNReal.ofReal_add (mul_nonneg hCfail htol0)
          (mul_nonneg hCcell (Real.rpow_nonneg hε0.le _))]
    _ ≤ ENNReal.ofReal ((Cfail + Ccell + K) * ε ^ α₀) := ENNReal.ofReal_le_ofReal hfin

end MatedCRT.FirstPass.Derived

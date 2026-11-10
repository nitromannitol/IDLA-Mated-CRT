import MatedCRT.FirstPass.S5f.Deterministic
import MatedCRT.FirstPass.S5f.Steps
import MatedCRT.FirstPass.S5d.StoppedExitInput
import MatedCRT.Draft.Section3
import MatedCRT.Draft.Section4
import MatedCRT.External.SLE

/-!
# First pass: the surplus maximum outside the killing set, `StoppedMaxOutsideStep` (task fp-S5f-5-1-max-outside, z10)

**Theorem `stoppedMaxOutside_of_steps`.** `StoppedMaxOutsideStep 𝒮` (the open input `ε M^ε → 0` in probability on `{t < T}` of
Proposition 5.1, corrected tex 2355-2372, [C21]; defined in FirstPass/S5d/StoppedExitInput.lean) follows from:

* Draft Theorem 4.1 `ConvergenceDivisibleStmt 𝒮` (uniform convergence of the rescaled least supersolution on `B_ρ`);
* Draft Lemma 3.3 `UniformConvergenceGreenKernelStmt 𝒮` (convergence of the rescaled discrete Green function off the pole);
* External `MepsScalingInput 𝒮` (`m_ε ≍ ε⁻¹`, eq:meps-scaling);
* External, already frozen: `MatedCRT.FrozenGreenDiscPole` (continuity of the disc Green function off the pole; used only for
  openness of the cluster, `isOpen_cluster_of_stopped`);
* NEW steps (paper-owned, taken as hypotheses, FirstPass/S5f/Steps.lean): `StoppedCellRepresentativeStep`,
  `StoppedPoleCellStep`, `StoppedOriginRadiusStep`.

Proof route (written source: tex 2360 and notes/fp-gaps/CHATGPT-idla-C20-C21-referee.md 177-202). For `ε` small, on the
event `{t < T}`, a vertex `b` outside the killing set with `u^ε(b) > κ/(2ε)` has a cell disjoint from `Λ_t` and positive
surplus, so a point `x ∈ B_ρ \ Λ_t` with `a^ε_x = b` exists. There `v + tG` vanishes (`odometer_eq_zero_of_notMem_stopped_Lambda`),
and the two rescaled convergences give `|R u(x)| ≤ δ (1 + t)`, while `R u(x) = m_ε⁻¹ u(b) > κ / (2C)`; with `δ = κ/(2C(1+t))`
this is a contradiction. The probabilities of the two convergence failures and of the random radius (`Λ_t ⊇ B_s(0)`) tend
to `0` (the last one up to `η/2`), which gives `P[t < T, (E ε)ᶜ] → 0`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- **Proposition 5.1, ceiling input (reduced).** `StoppedMaxOutsideStep 𝒮` from the paper's convergence inputs (Theorem
4.1, Lemma 3.3), the mesh scaling `MepsScalingInput`, the frozen pole continuity `FrozenGreenDiscPole`, and the three NEW steps
`StoppedCellRepresentativeStep`, `StoppedPoleCellStep`, `StoppedOriginRadiusStep`. -/
theorem stoppedMaxOutside_of_steps (𝒮 : SpaceFillingSLEModel)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮)
    (hM : MepsScalingInput 𝒮) (hG : MatedCRT.FrozenGreenDiscPole)
    (hcell : StoppedCellRepresentativeStep 𝒮) (hpole : StoppedPoleCellStep 𝒮)
    (hrad : StoppedOriginRadiusStep 𝒮) :
    StoppedMaxOutsideStep 𝒮 := by
  intro γ hγ0 hγ2 ρ hρ0 hρ1 Ω _ S hS Λ hfam t ht κ hκ
  obtain ⟨C, hC1, hMC⟩ := hM γ hγ0 hγ2
  obtain ⟨ε₀, hε₀, hMε⟩ := hMC Ω S hS
  have hCpos : 0 < C := by linarith
  have hCne : C ≠ 0 := hCpos.ne'
  have h1t : (1 + t) ≠ 0 := by linarith
  -- the threshold δ of the two rescaled convergences
  set δ : ℝ := κ / (2 * C * (1 + t)) with hδdef
  have hδ : 0 < δ := div_pos hκ (mul_pos (mul_pos two_pos hCpos) (by linarith))
  have hδ1 : δ * (1 + t) = κ / (2 * C) := by
    rw [hδdef]; field_simp
  -- the input convergences
  have hconvδ := hconv γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS Λ hfam t ht δ hδ
  have hrad' := hrad γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS Λ hfam t ht
  have hpole' := hpole γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS
  have hfamNull : S.P {ω | ¬ IsConeHarmonicBallFamily (S.μ ω) (Λ ω)} = 0 := ae_iff.1 hfam
  unfold TendsToOneOn
  refine ENNReal.tendsto_nhds_zero.2 fun η hη => ?_
  -- the random radius: a deterministic s with small failure probability
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      S.P {ω | t < clusterExitTime (Λ ω) ρ ∧ ¬ ball (0 : ℂ) s ⊆ Λ ω t} ≤ η / 2 :=
    ENNReal.tendsto_nhds_zero.1 hrad' (η / 2) (ENNReal.half_pos hη.ne')
  have hIoo : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 ρ := Ioo_mem_nhdsGT hρ0
  obtain ⟨s, hsP, hsI⟩ := (hev.and hIoo).exists
  have hs0 : 0 < s := hsI.1
  have hsρ : s < ρ := hsI.2
  -- the Green event off the pole on O = closedBall 0 ρ \ ball 0 s
  set O : Set ℂ := closedBall (0 : ℂ) ρ \ ball (0 : ℂ) s with hO
  have hOsub : O ⊆ closedBall (0 : ℂ) ρ \ {0} := by
    intro x hx
    refine ⟨hx.1, fun h0 => hx.2 ?_⟩
    rw [mem_singleton_iff.1 h0]
    exact mem_ball_self hs0
  have hOne : O.Nonempty := ⟨(ρ : ℂ), by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
    · rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
      exact not_lt.2 hsρ.le⟩
  have hsinf : s ≤ infDist (0 : ℂ) O := (Metric.le_infDist hOne).2 fun y hy => by
    have h := hy.2
    rw [mem_ball, not_lt] at h
    rw [dist_comm]
    exact h
  have hOinf : 0 < infDist (0 : ℂ) O := lt_of_lt_of_le hs0 hsinf
  have hgreenδ := hgreen γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS ρ 0 0 hρ0 subset_rfl (mem_ball_self hρ0) δ hδ O hOsub hOinf
  -- the probabilities of the two convergence failures tend to zero
  have hsum' := hconvδ.add hgreenδ
  rw [add_zero] at hsum'
  have hsmall := ENNReal.tendsto_nhds_zero.1 hsum' (η / 2) (ENNReal.half_pos hη.ne')
  filter_upwards [hsmall, (eventually_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioi (0 : ℝ)),
    Ioo_mem_nhdsGT hε₀, hpole'] with ε hsm hεpos hεlt hpolε
  have hε : 0 < ε := hεpos
  have hεlt' : ε < ε₀ := hεlt.2
  have hεne : ε ≠ 0 := hε.ne'
  -- the bad sets (null sets and failure events)
  set Nc : Set Ω := {ω | ¬ ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball (0 : ℂ) ρ).Nonempty →
      ∃ x ∈ cell ε (S.η ω) k ∩ ball (0 : ℂ) ρ, vertexOf ε (S.η ω) x = k} with hNc
  set Np : Set Ω := {ω | ¬ vertexOf ε (S.η ω) 0 = 0} with hNp
  set Nf : Set Ω := {ω | ¬ IsConeHarmonicBallFamily (S.μ ω) (Λ ω)} with hNf
  set Bc : Set Ω := {ω | t < clusterExitTime (Λ ω) ρ ∧ ∃ x ∈ ball (0 : ℂ) ρ,
      δ < |rescaledMatedLeastSupersolution S ρ t ε ω x - S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x|} with hBc
  set Bg : Set Ω := {ω | ∀ x ∈ O, |rescale (S.mε ε) ε (S.η ω)
      (fun a => ε⁻¹ * greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ))
        (vertexOf ε (S.η ω) 0) a) x - S.c₀ / 6 * greenFunction (ball (0 : ℂ) ρ) 0 x| ≤ δ}ᶜ with hBg
  set Rs : Set Ω := {ω | t < clusterExitTime (Λ ω) ρ ∧ ¬ ball (0 : ℂ) s ⊆ Λ ω t} with hRs
  have hcellNull : S.P Nc = 0 := ae_iff.1 (hcell γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS ε hε)
  have hpoleNull : S.P Np = 0 := ae_iff.1 hpolε
  have hfamNull' : S.P Nf = 0 := hfamNull
  -- inclusion: outside the bad sets, the killing-set ceiling holds
  have hincl : {ω | t < clusterExitTime (Λ ω) ρ} ∩ {ω | ∀ b ∉ stoppedKillSet S Λ ρ t ε ω,
      stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b ≤ κ / (2 * ε)}ᶜ ⊆
      ((((Nc ∪ Np) ∪ Nf) ∪ Bc) ∪ Bg) ∪ Rs := by
    rintro ω ⟨hF, hE⟩
    by_contra hbad
    apply hE
    simp only [hNc, hNp, hNf, hBc, hBg, hRs, Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff,
      not_or, not_not] at hbad
    obtain ⟨⟨⟨⟨⟨hcellω, hpoleω⟩, hfamω⟩, hconvω'⟩, hgreenω⟩, hradω⟩ := hbad
    have hF' : t < clusterExitTime (Λ ω) ρ := hF
    have hsub : ball (0 : ℂ) s ⊆ Λ ω t := by
      by_contra hn
      exact hradω ⟨hF', hn⟩
    have hconvω : ∀ x ∈ ball (0 : ℂ) ρ, |rescaledMatedLeastSupersolution S ρ t ε ω x
        - S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x| ≤ δ := by
      intro x hx
      by_contra hlt
      exact hconvω' ⟨hF', x, hx, not_le.1 hlt⟩
    rw [Set.mem_ofPred_eq]
    intro b hb
    by_contra hlt
    rw [not_le] at hlt
    have hκε : 0 < κ / (2 * ε) := div_pos hκ (mul_pos two_pos hε)
    have hpos : 0 < stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b := lt_trans hκε hlt
    have hbW : b ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ) :=
      cell_meets_ball_of_stoppedOdometer_pos hε ht hpos
    have hbcl := MatedCRT.Sec7.mem_matedDiscreteCluster_of_stoppedOdometer_pos hε ht hpos
    have hbΛ : b ∉ cellVertices ε (S.η ω) (Λ ω t) := fun h =>
      hb (by unfold stoppedKillSet; exact ⟨hF', hbcl, h⟩)
    obtain ⟨x, ⟨hxcell, hxball⟩, hxk⟩ := hcellω b hbW
    have hxΛ : x ∉ Λ ω t := fun hx => hbΛ ⟨x, hxcell, hx⟩
    have hodo0 := odometer_eq_zero_of_notMem_stopped_Lambda hG hfamω hρ0 ht hF' hxball hxΛ
    have hbc : vertexOf ε (S.η ω) x ∈ cellVertices ε (S.η ω) (closedBall (0 : ℂ) ρ) := by
      rw [hxk]
      exact ⟨x, hxcell, ball_subset_closedBall hxball⟩
    have hRu := rescale_stoppedOdometer_eq (S.mult ε ω) (S.mε ε) ε t ρ (S.η ω) x hbc
    have hRu' : rescale (S.mε ε) ε (S.η ω) (stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t) x
        = (S.mε ε)⁻¹ * stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b := by
      unfold rescale
      rw [hxk]
    have hxO : x ∈ O := by
      rw [hO]
      exact ⟨ball_subset_closedBall hxball, fun hxs => hxΛ (hsub hxs)⟩
    have hc1 := hconvω x hxball
    have hg1 := hgreenω x hxO
    rw [hpoleω] at hg1
    unfold odometer at hodo0
    -- the scale of the mesh
    have hm := hMε ε hε hεlt'
    have hmpos : 0 < S.mε ε := lt_of_lt_of_le (mul_pos (inv_pos.2 hCpos) (inv_pos.2 hε)) hm.1
    have hmi_pos : 0 < (S.mε ε)⁻¹ := inv_pos.2 hmpos
    have hmi_lb : ε / C ≤ (S.mε ε)⁻¹ := by
      have h := inv_anti₀ hmpos hm.2
      have e : (C * ε⁻¹)⁻¹ = ε / C := by field_simp
      rw [e] at h
      exact h
    have hlow : κ / (2 * C) ≤ (S.mε ε)⁻¹ * (κ / (2 * ε)) := by
      have h1 : ε / C * (κ / (2 * ε)) ≤ (S.mε ε)⁻¹ * (κ / (2 * ε)) :=
        mul_le_mul_of_nonneg_right hmi_lb hκε.le
      have e : ε / C * (κ / (2 * ε)) = κ / (2 * C) := by field_simp
      linarith
    have hgt : (S.mε ε)⁻¹ * (κ / (2 * ε))
        < (S.mε ε)⁻¹ * stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b :=
      mul_lt_mul_of_pos_left hlt hmi_pos
    -- the identity on the cell: the surplus at x is `R w̃ + t R g`, and `v + t G = 0` at x
    have hid : (S.mε ε)⁻¹ * stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b =
        (rescale (S.mε ε) ε (S.η ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) x
          - S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) +
        t * ((S.mε ε)⁻¹ * (ε⁻¹ * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0
            (vertexOf ε (S.η ω) x)) - S.c₀ / 6 * greenFunction (ball (0 : ℂ) ρ) 0 x) := by
      have h := hRu'.symm.trans hRu
      linear_combination h + (S.c₀ / 6) * hodo0
    have hb1 : |rescale (S.mε ε) ε (S.η ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) x
        - S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x| ≤ δ := hc1
    have hg1' : |(S.mε ε)⁻¹ * (ε⁻¹ * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0
        (vertexOf ε (S.η ω) x)) - S.c₀ / 6 * greenFunction (ball (0 : ℂ) ρ) 0 x| ≤ δ := hg1
    have hb2 : |t * ((S.mε ε)⁻¹ * (ε⁻¹ * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0
        (vertexOf ε (S.η ω) x)) - S.c₀ / 6 * greenFunction (ball (0 : ℂ) ρ) 0 x)| ≤ t * δ := by
      rw [abs_mul, abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left hg1' ht.le
    have hup : (S.mε ε)⁻¹ * stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b ≤ δ + t * δ := by
      rw [hid]
      have h1 := (abs_le.1 hb1).2
      have h2 := (abs_le.1 hb2).2
      linarith
    have hδeq : δ + t * δ = κ / (2 * C) := by
      rw [← hδ1]
      ring
    linarith
  -- the measure bound
  refine (measure_mono hincl).trans ?_
  have hNall : S.P ((Nc ∪ Np) ∪ Nf) = 0 :=
    measure_union_null (measure_union_null hcellNull hpoleNull) hfamNull'
  have e1 : S.P (((Nc ∪ Np) ∪ Nf) ∪ Bc) ≤ S.P Bc :=
    (measure_union_le _ _).trans (by rw [hNall, zero_add])
  have e2 : S.P ((((Nc ∪ Np) ∪ Nf) ∪ Bc) ∪ Bg) ≤ S.P Bc + S.P Bg :=
    (measure_union_le _ _).trans (add_le_add e1 le_rfl)
  have e3 : S.P (((((Nc ∪ Np) ∪ Nf) ∪ Bc) ∪ Bg) ∪ Rs) ≤ S.P Bc + S.P Bg + S.P Rs :=
    (measure_union_le _ _).trans (add_le_add e2 le_rfl)
  have hsm' : S.P Bc + S.P Bg ≤ η / 2 := hsm
  calc S.P (((((Nc ∪ Np) ∪ Nf) ∪ Bc) ∪ Bg) ∪ Rs) ≤ S.P Bc + S.P Bg + S.P Rs := e3
    _ ≤ η / 2 + η / 2 := add_le_add hsm' hsP
    _ = η := ENNReal.add_halves η

end MatedCRT

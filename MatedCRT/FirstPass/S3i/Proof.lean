import MatedCRT.FirstPass.S3i.Statement
import MatedCRT.FirstPass.S3i.Frozen
import MatedCRT.FirstPass.S3e
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkContinuity

/-!
# Corrected Lemma 3.6, annealed clause: the eight steps

Status of the steps (PRO numbering):
* Step 1 (common good event): NAMED in `QuenchedLensStep` (the good set `G ε`, its complement `O(ε^κ)`, the
  start-inside and finite-exit clause). Its Lemma 2.8 / Lemma 2.18 inputs are not yet wired.
* Step 2 (first boundary cell) and Step 3 (geometry at `v`), Step 4 (lens domain), Step 6 (same-walk relation of `F` to
  the discrepancy): NAMED in `QuenchedLensStep`. Missing claims: the coupling of the killed and unrestricted walks
  through `σ` and the strong Markov property at `σ` (PRO l.343-400, 401-421: "must be formalized carefully").
* Step 5 (apply (BE)): NAMED, through the hypothesis `hLens : FrozenOneSidedBoundaryContinuity 𝒮 → QuenchedLensStep 𝒮`.
  The exponent algebra `(t/d)^{-ν} ≤ (cK)^ν ε^{νb/2}` is PROVED (`boundary_power_le_fp36`).
* Step 7 (Hölder datum): PROVED (`holder_disc_le_fp36`, `sameWalk_disc_le_of_near_fp36`). The exit point lies in the
  closed disc on the good branch by `sameWalkExitPoint_mem_closedBall_fp36` (continuity of the interpolated walk,
  `pathExitPosition_mem_closedBall_fp36`; PRO l.422-457 "on the finite-exit branch, Z, P ∈ closed D").
* Step 8 (annealed split): PROVED (`sectionwiseOuterProb_le_of_good_fp36`).

Terminology: quenched and annealed laws (Armstrong-Kuusi-Mourrat); same-walk coupling and one-sided boundary estimate
(Gwynne-Miller-Sheffield, arXiv:1807.07511, Thm 3.9, eq. (3.31)).
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- The good branch of the same-walk comparison (PRO Step 7): the interpolated walk starts in `B_r(z)` and leaves it. -/
def SameWalkGood {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ) (ε : ℝ) (ω : Ω)
    (x : ℕ → ℤ) : Prop :=
  interpolatedWalk ε (S.η ω) (S.mε ε) x 0 ∈ ball z r ∧
    HarmonicBalls.pathExitTime (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x) < ⊤

/-- The exit point `Z` of the unrestricted interpolated walk from `B_r(z)`. -/
noncomputable def sameWalkExitPoint {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ)
    (ε : ℝ) (ω : Ω) (x : ℕ → ℤ) : ℂ :=
  pathExitPosition (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x)

/-- The projected exit point `P = B̄_r(z)`-retraction of the first exit vertex of the killed walk (PRO Step 2). -/
noncomputable def sameWalkProjected {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ)
    (ε : ℝ) (ω : Ω) (x : ℕ → ℤ) : ℂ :=
  ballRetraction z r (vertexPoint ε (S.η ω) (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))

/-- **Step 5 (exponent algebra).** If `t ≥ ε^{b/2}/c` and `d ≤ K ε^b`, then `(t/d)^{-ν} ≤ (cK)^ν ε^{νb/2}`. This is
the scaling `(s_ε/δ_ε)^{-ν} = (δ_ε/s_ε)^ν = ε^{νb/2}` of PRO l.380-390. -/
lemma boundary_power_le_fp36 {ε b ν c K t d : ℝ} (hε : 0 < ε) (hν : 0 < ν) (hc : 0 < c)
    (hK : 0 < K) (hd : 0 < d) (hdK : d ≤ K * ε ^ b) (ht : ε ^ (b / 2) / c ≤ t) :
    (t / d) ^ (-ν) ≤ (c * K) ^ ν * ε ^ (ν * b / 2) := by
  have hupos : 0 < ε ^ (b / 2) := Real.rpow_pos_of_pos hε _
  have hεb : ε ^ b = (ε ^ (b / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    congr 1
    push_cast
    ring
  have hLpos : 0 < (ε ^ (b / 2))⁻¹ / (c * K) := by positivity
  have hLle : (ε ^ (b / 2))⁻¹ / (c * K) ≤ t / d := by
    rw [le_div_iff₀ hd]
    have h1 : (ε ^ (b / 2))⁻¹ / (c * K) * d ≤ (ε ^ (b / 2))⁻¹ / (c * K) * (K * ε ^ b) :=
      mul_le_mul_of_nonneg_left hdK hLpos.le
    have h2 : (ε ^ (b / 2))⁻¹ / (c * K) * (K * ε ^ b) = ε ^ (b / 2) / c := by
      rw [hεb]
      field_simp
    have h3 : ε ^ (b / 2) / c ≤ t := ht
    linarith
  have hneg : (t / d) ^ (-ν) ≤ ((ε ^ (b / 2))⁻¹ / (c * K)) ^ (-ν) :=
    Real.rpow_le_rpow_of_nonpos hLpos hLle (by linarith)
  have hinv : ((ε ^ (b / 2))⁻¹ / (c * K)) ^ (-ν) = (c * K) ^ ν * (ε ^ (b / 2)) ^ ν := by
    rw [Real.rpow_neg hLpos.le, ← Real.inv_rpow hLpos.le]
    have e : ((ε ^ (b / 2))⁻¹ / (c * K))⁻¹ = c * K * ε ^ (b / 2) := by
      field_simp
    rw [e, Real.mul_rpow (by positivity) hupos.le]
  have hpow : (ε ^ (b / 2)) ^ ν = ε ^ (ν * b / 2) := by
    rw [← Real.rpow_mul hε.le]
    congr 1
    ring
  rw [hinv, hpow] at hneg
  exact hneg

/-- The closed disc contains the Euclidean retraction of every point onto `B̄_r(z)`. -/
lemma ballRetraction_mem_closedBall_fp36 {z : ℂ} {r : ℝ} (hr : 0 < r) (x : ℂ) :
    ballRetraction z r x ∈ closedBall z r := by
  unfold ballRetraction
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have hmax : 0 < max r (dist x z) := lt_max_of_lt_left hr
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hr.le hmax.le), ← dist_eq_norm,
    div_mul_eq_mul_div, div_le_iff₀ hmax]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hr.le

/-- **Exit position of a continuous path (PRO Step 7, good branch).** If a continuous path starts in the open disc
`B_r(z)` and its first exit time from it is finite, the exit position `pathExitPosition` lies in the closed disc
`B̄_r(z)`: the path stays in `B_r(z)` before the exit time `τ`, and `τ` lies in the closure of `[0, τ)`. -/
lemma pathExitPosition_mem_closedBall_fp36 {z : ℂ} {r : ℝ} {f : ℝ≥0 → ℂ} (hf : Continuous f)
    (h0 : f 0 ∈ ball z r) (hfin : HarmonicBalls.pathExitTime (ball z r) f < ⊤) :
    pathExitPosition (ball z r) f ∈ closedBall z r := by
  have hcl : IsClosed {t : ℝ≥0 | f t ∉ ball z r} := (isOpen_ball.isClosed_compl).preimage hf
  have hne : {t : ℝ≥0 | f t ∉ ball z r}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have htop : HarmonicBalls.pathExitTime (ball z r) f = ⊤ := by
      unfold HarmonicBalls.pathExitTime
      rw [sInf_eq_top]
      rintro x ⟨t, rfl, ht⟩
      have hmem : t ∈ ({t : ℝ≥0 | f t ∉ ball z r} : Set ℝ≥0) := ht
      rw [hne] at hmem
      exact hmem.elim
    exact hfin.ne htop
  have hval : HarmonicBalls.pathExitTime (ball z r) f =
      ((sInf {t : ℝ≥0 | f t ∉ ball z r} : ℝ≥0) : ℝ≥0∞) := by
    unfold HarmonicBalls.pathExitTime
    apply le_antisymm
    · apply sInf_le
      exact ⟨sInf {t : ℝ≥0 | f t ∉ ball z r}, rfl, hcl.csInf_mem hne (OrderBot.bddBelow _)⟩
    · refine le_sInf ?_
      rintro x ⟨t, rfl, ht⟩
      exact ENNReal.coe_le_coe.2 (csInf_le (OrderBot.bddBelow _) ht)
  set τ : ℝ≥0 := sInf {t : ℝ≥0 | f t ∉ ball z r} with hτdef
  have hout : f τ ∉ ball z r := hcl.csInf_mem hne (OrderBot.bddBelow _)
  have hbefore : ∀ t : ℝ≥0, t < τ → f t ∈ ball z r := by
    intro t ht
    by_contra hnot
    have hle : HarmonicBalls.pathExitTime (ball z r) f ≤ (t : ℝ≥0∞) := by
      unfold HarmonicBalls.pathExitTime
      exact sInf_le ⟨t, rfl, hnot⟩
    rw [hval] at hle
    exact absurd ht (not_lt.2 (ENNReal.coe_le_coe.1 hle))
  have hτ0 : τ ≠ 0 := by
    intro h0'
    exact hout (by rw [h0']; exact h0)
  have hpe : pathExitPosition (ball z r) f = f τ := by
    unfold pathExitPosition
    rw [hval]
    rfl
  rw [hpe]
  have hτcl : τ ∈ closure (Set.Ico (0 : ℝ≥0) τ) := by
    rw [closure_Ico hτ0.symm]
    exact ⟨zero_le, le_rfl⟩
  have hsub : f '' Set.Ico (0 : ℝ≥0) τ ⊆ ball z r := by
    rintro _ ⟨t, ht, rfl⟩
    exact hbefore t ht.2
  have himg : f τ ∈ closure (f '' Set.Ico (0 : ℝ≥0) τ) :=
    image_closure_subset_closure_image hf ⟨τ, hτcl, rfl⟩
  exact closure_ball_subset_closedBall (closure_mono hsub himg)

/-- **Good-branch exit point (PRO Step 7 hypothesis `hZ`).** On the good branch the exit point `Z` of the unrestricted
interpolated walk lies in `B̄_r(z)`: the interpolated walk is continuous (`continuous_interpolatedWalk`). -/
lemma sameWalkExitPoint_mem_closedBall_fp36 {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {r : ℝ} {z : ℂ}
    {ε : ℝ} {ω : Ω} {x : ℕ → ℤ} (hgood : SameWalkGood S r z ε ω x) :
    sameWalkExitPoint S r z ε ω x ∈ closedBall z r :=
  pathExitPosition_mem_closedBall_fp36 (continuous_interpolatedWalk ε (S.mε ε) (S.η ω) x) hgood.1 hgood.2

/-- **Step 7 (Hölder datum, real form).** If `ψ` is `χ`-Hölder with constant `H` on the closed disc, `Z, P ∈ B̄_r(z)`
and `|Z - P| ≤ s/2`, then `|ψ(Z) - ψ(P)| ≤ H s^χ` (PRO l.422-441). -/
lemma holder_disc_le_fp36 {z : ℂ} {r : ℝ} {ψ : ℂ → ℝ} {H χ : ℝ≥0} {Z P : ℂ} {s : ℝ}
    (hψ : HolderOnWith H χ ψ (closedBall z r)) (hZ : Z ∈ closedBall z r) (hP : P ∈ closedBall z r)
    (hs : 0 ≤ s) (hZP : dist Z P ≤ s / 2) :
    |ψ Z - ψ P| ≤ (H : ℝ) * s ^ (χ : ℝ) := by
  have h := hψ Z hZ P hP
  have hχ0 : (0 : ℝ) ≤ (χ : ℝ) := χ.2
  have hd : dist (ψ Z) (ψ P) ≤ (H : ℝ) * dist Z P ^ (χ : ℝ) := by
    have key : (H : ℝ≥0∞) * ENNReal.ofReal (dist Z P) ^ (χ : ℝ)
        = ENNReal.ofReal ((H : ℝ) * dist Z P ^ (χ : ℝ)) := by
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg H), ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hχ0,
        ENNReal.ofReal_coe_nnreal]
    have h2 : ENNReal.ofReal (dist (ψ Z) (ψ P)) ≤ ENNReal.ofReal ((H : ℝ) * dist Z P ^ (χ : ℝ)) := by
      rw [← key, ← edist_dist, ← edist_dist]
      exact h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (NNReal.coe_nonneg H) (Real.rpow_nonneg dist_nonneg _))).1 h2
  have hmono : dist Z P ^ (χ : ℝ) ≤ s ^ (χ : ℝ) := by
    calc dist Z P ^ (χ : ℝ) ≤ (s / 2) ^ (χ : ℝ) :=
          Real.rpow_le_rpow dist_nonneg hZP hχ0
      _ ≤ s ^ (χ : ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) hχ0
  rw [Real.dist_eq] at hd
  exact hd.trans (mul_le_mul_of_nonneg_left hmono (by positivity))

/-- **Step 7 (pathwise).** On the good branch, if the exit point lies within `s/2` of the projected point, then the
same-walk discrepancy is at most `H s^χ` (PRO l.422-441). -/
lemma sameWalk_disc_le_of_near_fp36 {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {r : ℝ} {z : ℂ}
    {ψ : ℂ → ℝ} {H χ : ℝ≥0} {ε : ℝ} {ω : Ω} {x : ℕ → ℤ} {s : ℝ} (hr : 0 < r)
    (hψ : HolderOnWith H χ ψ (closedBall z r)) (hs : 0 ≤ s) (hgood : SameWalkGood S r z ε ω x)
    (hZ : sameWalkExitPoint S r z ε ω x ∈ closedBall z r)
    (hnear : dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x) ≤ s / 2) :
    sameWalkExitDiscrepancy S r z ψ ε ω x ≤ (H : ℝ) * s ^ (χ : ℝ) := by
  have hg : interpolatedWalk ε (S.η ω) (S.mε ε) x 0 ∈ ball z r ∧
      HarmonicBalls.pathExitTime (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x) < ⊤ := hgood
  unfold sameWalkExitDiscrepancy finiteDiscExitValue
  split_ifs
  exact holder_disc_le_fp36 hψ hZ (ballRetraction_mem_closedBall_fp36 hr _) hs hnear

/-- **Step 8 (annealed split, abstract form).** If the quenched probabilities of the sections are at most `q` on a set
`G` of environments, then the outer annealed probability is at most `P(Gᶜ) + q`. The proof uses the measurable hull
`toMeasurable P Gᶜ` in the infimum defining `outerLIntegral`, which needs no measurability of `G`. -/
lemma sectionwiseOuterProb_le_of_good_fp36 {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Ω → Measure X) (hκ : ∀ ω, IsProbabilityMeasure (κ ω))
    (E : Set (Ω × X)) (G : Set Ω) (q : ℝ≥0∞) (hG : ∀ ω ∈ G, κ ω (Prod.mk ω ⁻¹' E) ≤ q) :
    sectionwiseOuterProb P κ E ≤ P Gᶜ + q := by
  unfold sectionwiseOuterProb outerLIntegral
  set N := toMeasurable P Gᶜ with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable P Gᶜ
  have hGN : Gᶜ ⊆ N := subset_toMeasurable P Gᶜ
  have hPN : P N = P Gᶜ := measure_toMeasurable Gᶜ
  set g : Ω → ℝ≥0∞ := N.indicator (fun _ => (1 : ℝ≥0∞)) + Nᶜ.indicator (fun _ => q) with hg
  have hgm : Measurable g :=
    (measurable_const.indicator hNm).add (measurable_const.indicator hNm.compl)
  have hfg : (fun ω => κ ω (Prod.mk ω ⁻¹' E)) ≤ g := by
    intro ω
    by_cases hω : ω ∈ N
    · have h1 : g ω = 1 := by simp [hg, hω]
      rw [h1]
      have := hκ ω
      exact prob_le_one
    · have hωG : ω ∈ G := by
        by_contra h
        exact hω (hGN h)
      have h1 : g ω = q := by simp [hg, hω]
      rw [h1]
      exact hG ω hωG
  have hint : ∫⁻ ω, g ω ∂P = P N + q * P Nᶜ := by
    rw [hg]
    simp only [Pi.add_apply]
    rw [lintegral_add_left (measurable_const.indicator hNm), lintegral_indicator_const hNm,
      lintegral_indicator_const hNm.compl, one_mul]
  refine (iInf_le _ g).trans ((iInf_le _ hgm).trans ((iInf_le _ hfg).trans ?_))
  rw [hint, hPN]
  exact add_le_add le_rfl (mul_le_of_le_one_right zero_le prob_le_one)

/-- **Steps 1-6 as one named input (PRO sameWalk §2.4).** The quenched estimate on a good set `G ε` of environments:
`P(G ε)ᶜ = O(ε^κ)`; on `G ε` the walk started at `vertexOf ε η y`
* (Step 1) the start lies in the disc and the walk exits, except on a set of quenched mass `O(ε^{νb/2})`, and
  (Step 3) the exit point of the interpolated walk lies in the closed disc on the good branch;
* (Steps 2, 4, 5, 6) the quenched probability of a far exit point `|Z - P| > ε^{b/2}/2` on the good branch is at most
  `O(ε^{νb/2})`.
Steps 2-4 and 6 (the first boundary cell, the lens domain `U = D⁺ ∩ B_{s/4}(P)`, the harmonic function `F`, the
strong Markov coupling of the killed and unrestricted walks) are NOT formalized: PRO l.343-421 sketches them, the
coupling "must be formalized carefully". Step 5 applies the boundary estimate `(BE)` to `F`, which is why the input
is an implication from `FrozenOneSidedBoundaryContinuity 𝒮`. The exact missing claims are reported in the report. -/
def QuenchedLensStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ b : ℝ, 0 < b ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ (ψ : ℂ → ℝ) (H χ : ℝ≥0) (y : ℂ), AdmissibleHolderDataAndStart r z ψ H χ y →
  ∃ κ ν C ε₀ : ℝ, 0 < κ ∧ 0 < ν ∧ 0 ≤ C ∧ 0 < ε₀ ∧
  ∃ (G : ℝ → Set Ω) (C₁ : ℝ), 0 ≤ C₁ ∧
  ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    S.P (G ε)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ κ) ∧
    ∀ ω ∈ G ε,
      srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) {x | ¬ SameWalkGood S r z ε ω x}
        ≤ ENNReal.ofReal (C * ε ^ (ν * b / 2)) ∧
      srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
        {x | SameWalkGood S r z ε ω x ∧
          ε ^ (b / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)}
        ≤ ENNReal.ofReal (C * ε ^ (ν * b / 2))

/-- **Corrected Lemma 3.6, with the annealed same-walk clause.** The convergence conjunct is
`firstPass_3_6_convergence_corrected` (S3e.lean:44). The annealed clause follows from the boundary estimate `hBE` (GMS
(3.31), frozen) through the named Steps 1-6 `hLens`, by Step 7 (`sameWalk_disc_le_of_near_fp36`) and Step 8
(`sectionwiseOuterProb_le_of_good_fp36`). -/
theorem firstPass_3_6_annealed {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hBE : FrozenOneSidedBoundaryContinuity 𝒮)
    (hLens : FrozenOneSidedBoundaryContinuity 𝒮 → QuenchedLensStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 := by
  refine ⟨firstPass_3_6_convergence_corrected h211 h28 hm hexc h32, ?_⟩
  intro γ hγ0 hγ2
  obtain ⟨b, hb, hlens⟩ := hLens hBE γ hγ0 hγ2
  refine ⟨b, hb, fun ρ hρ0 hρ1 Ω _ S hS r z hr hball ψ H χ y hadm => ?_⟩
  obtain ⟨κ, ν, C, ε₀, hκ, hν, hC, hε₀, G, C₁, hC₁, hG⟩ :=
    hlens ρ hρ0 hρ1 Ω S hS r z hr hball ψ H χ y hadm
  obtain ⟨-, -, hψ, -⟩ := hadm
  refine ⟨κ, ν, C₁ + 2 * C, ε₀, hκ, hν, by linarith, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨hPG, hω⟩ := hG ε hε hεε₀
  have := hS.isProbabilityMeasure
  have hper : ∀ ω ∈ G ε,
      srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
        (Prod.mk ω ⁻¹' {p : Ω × (ℕ → ℤ) |
          (1 + (H : ℝ)) * ε ^ (b * (χ : ℝ) / 2) < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2})
        ≤ ENNReal.ofReal (2 * C * ε ^ (ν * b / 2)) := by
    intro ω hωG
    obtain ⟨hbad, hfar⟩ := hω ω hωG
    have hincl : Prod.mk ω ⁻¹' {p : Ω × (ℕ → ℤ) |
          (1 + (H : ℝ)) * ε ^ (b * (χ : ℝ) / 2) < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2}
        ⊆ {x | ¬ SameWalkGood S r z ε ω x} ∪
          {x | SameWalkGood S r z ε ω x ∧
            ε ^ (b / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)} := by
      intro x hx
      by_cases hg : SameWalkGood S r z ε ω x
      · right
        refine ⟨hg, ?_⟩
        by_contra hnf
        have hnear : dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)
            ≤ ε ^ (b / 2) / 2 := not_lt.1 hnf
        have hd := sameWalk_disc_le_of_near_fp36 hr hψ (Real.rpow_nonneg hε.le _) hg (sameWalkExitPoint_mem_closedBall_fp36 hg) hnear
        have e : (ε ^ (b / 2)) ^ (χ : ℝ) = ε ^ (b * (χ : ℝ) / 2) := by
          rw [← Real.rpow_mul hε.le]
          ring_nf
        rw [e] at hd
        have hX : 0 ≤ ε ^ (b * (χ : ℝ) / 2) := Real.rpow_nonneg hε.le _
        have hx' : (1 + (H : ℝ)) * ε ^ (b * (χ : ℝ) / 2) < sameWalkExitDiscrepancy S r z ψ ε ω x := hx
        nlinarith [NNReal.coe_nonneg H]
      · left
        exact hg
    have hsum : ENNReal.ofReal (C * ε ^ (ν * b / 2)) + ENNReal.ofReal (C * ε ^ (ν * b / 2))
        = ENNReal.ofReal (2 * C * ε ^ (ν * b / 2)) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hC (Real.rpow_nonneg hε.le _))
        (mul_nonneg hC (Real.rpow_nonneg hε.le _))]
      congr 1
      ring
    exact (measure_mono hincl).trans ((measure_union_le _ _).trans ((add_le_add hbad hfar).trans hsum.le))
  have hsplit := sectionwiseOuterProb_le_of_good_fp36 S.P (fun ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
    (fun ω => isProbabilityMeasure_srwLaw _ _)
    {p : Ω × (ℕ → ℤ) | (1 + (H : ℝ)) * ε ^ (b * (χ : ℝ) / 2) < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2}
    (G ε) (ENNReal.ofReal (2 * C * ε ^ (ν * b / 2))) hper
  refine hsplit.trans ?_
  calc S.P (G ε)ᶜ + ENNReal.ofReal (2 * C * ε ^ (ν * b / 2))
      ≤ ENNReal.ofReal (C₁ * ε ^ κ) + ENNReal.ofReal (2 * C * ε ^ (ν * b / 2)) := add_le_add hPG le_rfl
    _ = ENNReal.ofReal (C₁ * ε ^ κ + 2 * C * ε ^ (ν * b / 2)) :=
        (ENNReal.ofReal_add (mul_nonneg hC₁ (Real.rpow_nonneg hε.le _))
          (mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg hε.le _))).symm
    _ ≤ ENNReal.ofReal ((C₁ + 2 * C) * (ε ^ κ + ε ^ (ν * b / 2))) :=
        ENNReal.ofReal_le_ofReal (by
          nlinarith [mul_nonneg hC₁ (Real.rpow_nonneg hε.le (ν * b / 2)),
            mul_nonneg hC (Real.rpow_nonneg hε.le κ), Real.rpow_nonneg hε.le κ,
            Real.rpow_nonneg hε.le (ν * b / 2)])

end FirstPass36
end MatedCRT

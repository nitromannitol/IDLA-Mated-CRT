import MatedCRT.Proofs.Sec4.SubsequentialProperties.ClusterContainment

/-!
# Lemma 4.8, item 3 (equality): `Δw̄*_t = (c₀/6) μ_h` on the non-coincidence set

Step 3 of the proof of Lemma 4.8 (paper/idla_mated_crt-corrected.tex, l.1892-1915). Let
`W = {x ∈ B_ρ : x = 0 ∨ w(x) > -t (c₀/6) G_{B_ρ}(0, x)}`.

* `isOpen_noncoincidence`: `W` is open (`G_{B_ρ}(0, ·)` is continuous off the pole and large near it);
* `laplacianGE_zero_of_laplacianLE_neg`: `Δ(-f) ≤ 0` weakly gives `Δf ≥ 0` weakly;
* `odometer_hasLaplacian_noncoincidence`: pathwise, on discs in `W` the discrete function `w̃^ε_t + q^ε_{B_ρ}` is
  eventually discrete harmonic (its discs lie in the discrete cluster, `eventually_interiorCellVertices_subset_cluster`,
  where `Δ^ε w̃^ε_t = (deg^ε)⁻¹` by the corrected Lemma 4.4), so `w + q̄` is subharmonic on `W`; with the upper bound
  `Δ(w + q̄) ≤ 0` (`odometer_integral_mul_laplacian_le`) it is weakly harmonic on `W`
  (`hasLaplacianOfLaplacianLEGEStep_holds`), and `Δq̄ = -(c₀/6) μ_h` gives `Δw = (c₀/6) μ_h` on `W`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls Real Laplacian
open scoped ENNReal

/-- **The non-coincidence set is open.** -/
theorem isOpen_noncoincidence {ρ t c : ℝ} (hρ : 0 < ρ) (htc : 0 < t * c) {w : ℂ → ℝ}
    (hwc : ContinuousOn w (closedBall 0 ρ)) :
    IsOpen {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * c * greenFunction (ball 0 ρ) 0 x < w x} := by
  obtain ⟨b₀, hb₀⟩ := (isCompact_closedBall (0 : ℂ) ρ).bddBelow_image hwc
  have hwB : ∀ x ∈ closedBall (0 : ℂ) ρ, b₀ ≤ w x := fun x hx => hb₀ ⟨x, hx, rfl⟩
  have hzero : {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * c * greenFunction (ball 0 ρ) 0 x < w x} ∈ 𝓝 (0 : ℂ) := by
    obtain ⟨r₁, hr₁, hr₁ρ, hG⟩ := exists_radius_le_greenFunction hρ htc (-b₀ + 1)
    refine Metric.mem_nhds_iff.2 ⟨r₁, hr₁, fun y hy => ?_⟩
    rw [mem_ball, dist_zero_right] at hy
    have hyB : y ∈ ball (0 : ℂ) ρ := by rw [mem_ball, dist_zero_right]; linarith
    refine ⟨hyB, ?_⟩
    by_cases hy0 : y = 0
    · exact Or.inl hy0
    · right
      have h1 := hG y (norm_pos_iff.2 hy0) (by linarith)
      have h2 := hwB y (ball_subset_closedBall hyB)
      have e : -t * c * greenFunction (ball 0 ρ) 0 y = -(t * c * greenFunction (ball 0 ρ) 0 y) := by ring
      linarith
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hxB, hx⟩
  by_cases hx0 : x = 0
  · rw [hx0]; exact hzero
  · rcases hx with hx | hx
    · exact absurd hx hx0
    have hcw : ContinuousAt w x :=
      hwc.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hxB) ball_subset_closedBall)
    have hcG : ContinuousAt (greenFunction (ball 0 ρ) 0) x :=
      (continuousOn_greenFunction_ball (mem_ball_self hρ)).continuousAt (isOpen_compl_singleton.mem_nhds hx0)
    have hcont : ContinuousAt (fun y => w y + t * c * greenFunction (ball 0 ρ) 0 y) x :=
      hcw.add (continuousAt_const.mul hcG)
    have hpos : 0 < w x + t * c * greenFunction (ball 0 ρ) 0 x := by linarith
    filter_upwards [isOpen_ball.mem_nhds hxB, hcont.eventually (lt_mem_nhds hpos)] with y hyB hy
    have hy' : 0 < w y + t * c * greenFunction (ball 0 ρ) 0 y := hy
    exact ⟨hyB, Or.inr (by linarith)⟩

/-- A weak upper bound `Δ(-f) ≤ 0` gives the weak lower bound `Δf ≥ 0`. -/
theorem laplacianGE_zero_of_laplacianLE_neg {f : ℂ → ℝ} {U : Set ℂ} (hle : LaplacianLE (-f) 0 U) :
    LaplacianGE f 0 U := by
  refine ⟨by simpa using hle.1.neg, fun φ hφ hφ0 => ⟨integrable_zero_measure, ?_⟩⟩
  have h := hle.2 φ hφ hφ0 integrable_zero_measure
  simp only [integral_zero_measure, Pi.neg_apply, neg_mul, integral_neg] at h ⊢
  linarith

/-- **Lemma 4.8, item 3 (equality), pathwise.** -/
theorem odometer_hasLaplacian_noncoincidence {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {ρ : ℝ} (hρ : 0 < ρ)
    (harea : IsAreaParametrized (S.μ ω) (S.η ω)) (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hlf : ∀ ε, 0 < ε → IsLocallyFiniteMult (S.mult ε ω))
    (hcells : ∀ ε, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmax : ∀ ε, 0 < ε → ∀ A : Set ℤ, A.Nonempty → A.Finite → ∀ u : ℤ → ℝ, IsSubharmonicOn (S.mult ε ω) u A →
      ∀ a ∈ A, ∃ b ∈ vBoundary (S.mult ε ω) A, u a ≤ u b)
    {εk : ℕ → ℝ} (hεk : ∀ k, 0 < εk k) (hεk0 : Tendsto εk atTop (𝓝 0))
    (hdir : ∀ (q₁ q₂ s : ℚ) (n : ℕ) (j l : ℤ), (0 : ℝ) < s → ‖ratPoint q₁ q₂‖ + s < ρ →
      Tendsto (fun k => hatDirichletAtCentre S (ratPoint q₁ q₂) s n j l (εk k) ω) atTop
        (𝓝 (circleAverage (hat n j l) (ratPoint q₁ q₂) s)))
    (hv0 : ∀ ε, 0 < ε → vertexOf ε (S.η ω) 0 = 0)
    (hg : ∀ j : ℕ, ∀ᶠ k in atTop, ∀ x ∈ closedBall (0 : ℂ) ρ \ ball 0 (ρ / ((j : ℝ) + 2)),
      |rescaledGreenKernel S ρ (εk k) ω x - S.c₀ / 6 * greenFunction (ball 0 ρ) 0 x| ≤ 1 / ((j : ℝ) + 1))
    (hc : 0 < S.c₀ / 6) {t : ℝ} (ht : 0 < t)
    (hclust : ∀ ε, 0 < ε → ∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
      matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a =
        ((matedDeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹)
    (hupper : ∀ ε, 0 < ε → ∀ a ∈ ballInterior ε (S.η ω) ρ,
      matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a ≤
        ((matedDeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹)
    {qbar : ℂ → ℝ} (hqc : ContinuousOn qbar (closedBall 0 ρ))
    (hqlap : HasLaplacian qbar 0 (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) (ball 0 ρ))
    (hqconv : TendstoUniformlyOn (fun k => rescale (S.mε (εk k)) (εk k) (S.η ω)
      (normExitTime (S.mult (εk k) ω) (interiorCellVertices (εk k) (S.η ω) (ball 0 ρ)))) qbar atTop
      (closedBall 0 ρ))
    {w : ℂ → ℝ} (hwc : ContinuousOn w (closedBall 0 ρ))
    (hconv : TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (εk k) ω) w atTop
      (closedBall 0 ρ)) :
    ∀ f : ℂ → ℝ, IsTestFunction
        {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x < w x} f →
      Integrable f (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) ∧
      ∫ x, w x * Δ f x = ∫ x, f x ∂(ENNReal.ofReal (S.c₀ / 6) • S.μ ω) := by
  set W := {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x < w x}
  have hWo : IsOpen W := isOpen_noncoincidence hρ (mul_pos ht hc) hwc
  have hWB : W ⊆ ball 0 ρ := fun x hx => hx.1
  -- `Δ(w + q̄) ≤ 0` on `B_ρ`
  have hle := (odometer_integral_mul_laplacian_le S ω hρ harea hp hlf hcells hmax hεk hεk0 hdir hupper hqc
    hqlap hqconv hwc hconv).1
  have hleW : LaplacianLE (w + qbar) 0 W :=
    ⟨hle.1.mono_set hWB, fun φ hφ hφ0 hφi => hle.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hWB⟩ hφ0 hφi⟩
  -- `w + q̄` is subharmonic on `W`
  have hconvU : TendstoUniformlyOn (fun k x => (S.mε (εk k))⁻¹ *
      (fun a => matedLeastSupersolution (S.mult (εk k) ω) (εk k) (S.η ω) ρ t a +
        normExitTime (S.mult (εk k) ω) (interiorCellVertices (εk k) (S.η ω) (ball 0 ρ)) a)
        (vertexOf (εk k) (S.η ω) x)) (w + qbar) atTop (closedBall 0 ρ) := by
    refine (hconv.add hqconv).congr (Eventually.of_forall fun k x _ => ?_)
    simp only [Pi.add_apply, rescaledMatedLeastSupersolution, rescale]
    ring
  have hsup := isSuperharmonicOn_neg_of_discrete S ω harea hp hlf hcells hmax hεk hεk0 hdir
    (U := fun k a => matedLeastSupersolution (S.mult (εk k) ω) (εk k) (S.η ω) ρ t a +
        normExitTime (S.mult (εk k) ω) (interiorCellVertices (εk k) (S.η ω) (ball 0 ρ)) a)
    (hwc.add hqc) hconvU hWo hWB (by
      intro q₁ q₂ s hs hdisc
      filter_upwards [eventually_interiorCellVertices_subset_cluster S ω hρ harea hp hlf hcells hmax hεk hεk0
        hv0 hg hc ht hwc hconv hs hdisc] with k hk a ha
      have ha' : a ∈ ballInterior (εk k) (S.η ω) ρ :=
        interiorCellVertices_subset_of_ball_subset harea.1 hs hρ
          (ball_subset_closedBall.trans (hdisc.trans hWB)) ha
      have hA : (interiorCellVertices (εk k) (S.η ω) (ball 0 ρ)).Finite :=
        (Tightness.cellVertices_finite harea.1 hp (hεk k) isBounded_ball).subset fun b hb => hb.1
      rw [mLaplacian_add_of_locallyFinite (hlf _ (hεk k))]
      have h1 : mLaplacian (S.mult (εk k) ω) (matedLeastSupersolution (S.mult (εk k) ω) (εk k) (S.η ω) ρ t) a =
          ((mdeg (S.mult (εk k) ω) a : ℕ) : ℝ)⁻¹ := hclust (εk k) (hεk k) a (hk ha)
      rw [h1, normExitTimeLaplacianStep (S.mult (εk k) ω) _ (S.mult_symm _ ω) (hlf _ (hεk k))
        (fun i => S.mult_succ_ne_zero (hεk k).le ω i) hA a ha']
      simp)
  have hgeW : LaplacianGE (w + qbar) 0 W := laplacianGE_zero_of_laplacianLE_neg
    (laplacianLEOfSuperharmonicStep_holds W _ hWo ((hwc.add hqc).mono (hWB.trans ball_subset_closedBall)).neg hsup)
  have hharm := hasLaplacianOfLaplacianLEGEStep_holds W _ hWo hleW hgeW
  intro f hf
  have hfB : IsTestFunction (ball 0 ρ) f := ⟨hf.1, hf.2.1, hf.2.2.trans hWB⟩
  obtain ⟨-, hfμ, h2⟩ := hqlap.2 f hfB
  refine ⟨hfμ, ?_⟩
  obtain ⟨-, -, h3⟩ := hharm.2 f hf
  have hwint := integrable_mul_laplacian
    ((hwc.mono ball_subset_closedBall).locallyIntegrableOn measurableSet_ball) hfB
  have hqint := integrable_mul_laplacian hqlap.1 hfB
  have hfun : (fun x => (w + qbar) x * Δ f x) = fun x => w x * Δ f x + qbar x * Δ f x :=
    funext fun x => by rw [Pi.add_apply]; ring
  rw [hfun, integral_add hwint hqint, h2] at h3
  simp only [integral_zero_measure, sub_zero, zero_sub] at h3
  linarith

end MatedCRT

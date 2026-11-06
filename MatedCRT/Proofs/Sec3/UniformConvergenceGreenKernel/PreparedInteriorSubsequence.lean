import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.InteriorSubsequence
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.PreparedRandomCompactnessAE
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.PreparedFinal

/-! Prepared subsequences in the proof of Lemma 3.3. -/

namespace MatedCRT.GreenEnvironment

open Set Metric Topology MeasureTheory Filter _root_.HarmonicBalls
open scoped ENNReal

/-- **Lemma 3.3 along subsequences.** -/
theorem exists_prepared_subseq_greenKernel_uniform (𝒮 : SpaceFillingSLEModel)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r r' d : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hr' : r' < r) (hd : 0 < d)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ (∀ n, 0 < ε (ψ n)) ∧
      ∀ I : Ω → ℕ → ℕ, (∀ n, Measurable[S.envSigma] fun ω => I ω n) → (∀ ω n, n ≤ I ω n) →
      ∀ᵐ ω ∂S.P, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformlyOn (fun k => rescaledBallGreenKernel S r z y (ε (ψ (I ω (φ k)))) ω)
          (fun x => S.c₀ / 6 * greenFunction (ball z r) y x) atTop
          (closedBall z r' \ ball y d) := by
  classical
  have hyz : dist y z < r := hy
  -- the domain `D = B_{r₂}(z) \ cl(B_s(y))`
  set s : ℝ := min (d / 2) ((r - dist y z) / 2) with hsdef
  have hs0 : 0 < s := lt_min (by linarith) (by linarith)
  have hsd : s ≤ d / 2 := min_le_left _ _
  have hsr : s ≤ (r - dist y z) / 2 := min_le_right _ _
  set L : ℝ := max r' (dist y z + s) with hLdef
  have hL1 : r' ≤ L := le_max_left _ _
  have hL2 : dist y z + s ≤ L := le_max_right _ _
  have hLr : L < r := max_lt hr' (by linarith)
  set r₂ : ℝ := (L + r) / 2 with hr₂def
  have hLr₂ : L < r₂ := by rw [hr₂def]; linarith
  have hr₂r : r₂ < r := by rw [hr₂def]; linarith
  set d₁ : ℝ := min (s / 4) ((r - r₂) / 2) with hd₁def
  have hd₁0 : 0 < d₁ := lt_min (by linarith) (by linarith)
  have hd₁s : d₁ ≤ s / 4 := min_le_left _ _
  have hd₁r : d₁ ≤ (r - r₂) / 2 := min_le_right _ _
  set D : Set ℂ := ball z r₂ \ closedBall y s with hDdef
  have hDo : IsOpen D := isOpen_ball.sdiff isClosed_closedBall
  have hDc : IsConnected D := isConnected_ball_diff_closedBall hs0.le (by linarith)
  have hDB : D ⊆ ball z r := fun x hx => ball_subset_ball hr₂r.le hx.1
  have hDρ : D ⊆ ball 0 ρ := hDB.trans hball
  have hDz : ∀ x ∈ D, dist x z + d₁ < r := by
    intro x hx
    have : dist x z < r₂ := hx.1
    linarith
  have hDsep : ∀ x ∈ D, 4 * d₁ ≤ dist y x := by
    intro x hx
    have h1 : ¬ dist x y ≤ s := hx.2
    rw [dist_comm]
    linarith
  have hyd₁ : dist y z + d₁ < r := by linarith
  have hDy : D ⊆ {y}ᶜ := by
    intro x hx hxy
    rw [mem_singleton_iff] at hxy
    apply hx.2
    rw [hxy]
    exact mem_closedBall_self hs0.le
  have hK₀c : IsCompact (closedBall z r' \ ball y d) := (isCompact_closedBall z r').diff isOpen_ball
  have hK₀D : closedBall z r' \ ball y d ⊆ D := by
    intro x hx
    refine ⟨?_, ?_⟩
    · have h1 : dist x z ≤ r' := hx.1
      show dist x z < r₂
      linarith
    · intro hxs
      have h1 : dist x y ≤ s := hxs
      have h2 : ¬ dist x y < d := hx.2
      linarith
  -- Step 1: dyadic scales
  obtain ⟨ψ₁, hψ₁, hψ₁ε⟩ := extraction_forall_of_eventually
    (P := fun n k => 0 < ε k ∧ ε k < (1 / 2) ^ n) fun n =>
      hε (Ioo_mem_nhdsGT (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n))
  have hε₁ : Tendsto (fun n => ε (ψ₁ n)) atTop (𝓝[>] 0) := hε.comp hψ₁.tendsto_atTop
  -- Step 2: local Green-kernel bounds and harmonicity on `D`
  obtain ⟨Kc, hKc, φ₂, hφ₂, hloc⟩ := local_greenKernel_estimates_ae_subsequence 𝒮 h214
    hγ hγ2 hρ hρ1 S hS hr hd₁0 hball hyd₁ hDz hDsep (fun n => ε (ψ₁ n)) hε₁
  -- Step 3: localizing tests, their cutoffs, and the Green-occupation integrals
  obtain ⟨f, hfs, hfc, hfn, hfloc⟩ := exists_countable_localizing_tests
  choose φc hφcs hφcc hφconv using fun i (h : tsupport (f i) ⊆ ball z r) =>
    exists_cutoff_for_integral_convergence (U := ball z r) isBounded_ball
      (hfs i).continuous (hfc i) h
  let T : ℕ → ℂ → ℝ := fun j => if j % 2 = 0 then f (j / 2) else
    if h : tsupport (f (j / 2)) ⊆ ball z r then φc (j / 2) h else fun _ => 0
  have hTs : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (T j) := by
    intro j
    simp only [T]
    split_ifs with h1 h2
    · exact hfs _
    · exact hφcs _ h2
    · exact contDiff_const
  have hTc : ∀ j, HasCompactSupport (T j) := by
    intro j
    simp only [T]
    split_ifs with h1 h2
    · exact hfc _
    · exact hφcc _ h2
    · exact HasCompactSupport.zero
  obtain ⟨φ₃, hφ₃, htests⟩ := exists_subseq_ae_of_countable_tendstoInProbability S.P
    (fun j ε sample => (S.mε ε)⁻¹ * ∑' x : cellVertices ε (S.η sample) (ball z r),
      greenFn (S.mult ε sample) (interiorCellVertices ε (S.η sample) (ball z r))
        (vertexOf ε (S.η sample) y) x * T j (vertexPoint ε (S.η sample) x))
    (fun j sample => S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * T j x ∂S.μ sample)
    (fun j => integralConvergenceGreenFunction_smooth_test 𝒮 h34 hγ hγ2 hρ hρ1 S hS hr hball hy
      (T j) (hTs j) (hTc j))
    (fun n => ε (ψ₁ (φ₂ n))) (hε₁.comp hφ₂.tendsto_atTop)
  -- Step 4: degree-measure integrals of a dense test family
  obtain ⟨F, hFc, hFd⟩ := VagueWholePlane.exists_denseTestFamilyC
  have hFne : F.Nonempty := by
    obtain ⟨_, _, _, ⟨φ, hφ, _⟩, _⟩ := hFd.2 0 ⟨continuous_const, HasCompactSupport.zero⟩
    exact ⟨φ, hφ⟩
  obtain ⟨gF, hgF⟩ := hFc.exists_eq_range hFne
  have hgFmem : ∀ j, gF j ∈ F := fun j => by rw [hgF]; exact mem_range_self j
  obtain ⟨φ₄, hφ₄, hdeg⟩ := exists_subseq_ae_of_countable_tendstoInProbability S.P
    (fun j ε ω => ∫ x, gF j x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω))
    (fun j ω => 6 * ∫ x, gF j x ∂S.μ ω)
    (fun j => h210 γ hγ hγ2 Ω S hS (gF j) (hFd.1 _ (hgFmem j)).1 (hFd.1 _ (hgFmem j)).2)
    (fun n => ε (ψ₁ (φ₂ (φ₃ n)))) ((hε₁.comp hφ₂.tendsto_atTop).comp hφ₃.tendsto_atTop)
  -- the deterministic subsequence
  have hχm : StrictMono fun n => φ₂ (φ₃ (φ₄ n)) := hφ₂.comp (hφ₃.comp hφ₄)
  have hdy : ∀ n, 0 < ε (ψ₁ (φ₂ (φ₃ (φ₄ n)))) ∧ ε (ψ₁ (φ₂ (φ₃ (φ₄ n)))) < (1 / 2) ^ n := by
    intro n
    refine ⟨(hψ₁ε _).1, (hψ₁ε _).2.trans_le ?_⟩
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hχm.id_le n)
  set e : ℕ → ℝ := fun n => ε (ψ₁ (φ₂ (φ₃ (φ₄ n)))) with he_def
  have he : IsPolySummableScales e := isPolySummableScales_of_lt_half_pow hdy
  have hepos : ∀ n, 0 < e n := fun n => (hdy n).1
  -- measurable versions of the Green kernels
  choose g hgm hg using fun n => hS.exists_envSigma_measurable_greenKernel_vertexOf (hepos n)
    (ball z r) (Or.inl isOpen_ball) y
  let u : Ω → ℕ → ℤ → ℝ := fun ω n a => (e n)⁻¹ * g n ω a
  have hum : ∀ n a, Measurable[S.envSigma] fun ω => u ω n a := fun n a =>
    measurable_const.mul (hgm n a)
  have hgall : ∀ᵐ ω ∂S.P, ∀ n b, g n ω b = greenKernel (S.mult (e n) ω)
      (interiorCellVertices (e n) (S.η ω) (ball z r)) (vertexOf (e n) (S.η ω) y) b :=
    ae_all_iff.2 hg
  have hu_eq : ∀ ω, (∀ n b, g n ω b = greenKernel (S.mult (e n) ω)
      (interiorCellVertices (e n) (S.η ω) (ball z r)) (vertexOf (e n) (S.η ω) y) b) →
      ∀ n, u ω n = fun a => (e n)⁻¹ * greenKernel (S.mult (e n) ω)
        (interiorCellVertices (e n) (S.η ω) (ball z r)) (vertexOf (e n) (S.η ω) y) a := by
    intro ω hω n
    funext a
    simp only [u, hω n a]
  have hgood : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) D,
        matedLaplacian (S.mult (e n) ω) (u ω n) a = 0) ∧
      (∀ a ∈ cellVertices (e n) (S.η ω) D, |u ω n a| ≤ Kc / e n) := by
    filter_upwards [hloc, hgall] with ω hω hgω
    filter_upwards [(hφ₃.comp hφ₄).tendsto_atTop.eventually hω] with n hn
    rw [hu_eq ω hgω n]
    exact ⟨fun a ha => (hn a ha.1).2, fun a ha => (hn a ha).1⟩
  obtain ⟨φ₅, hφ₅, hprep⟩ := prepared_compactness_of_eventual_estimates_random_ae
    𝒮 h31 hγ hγ2 hρ hρ1 S hS D hDρ hDo hDc e hepos he.tendsto_zero u hum Kc hKc hgood
  refine ⟨fun n => ψ₁ (φ₂ (φ₃ (φ₄ (φ₅ n)))), hψ₁.comp (hχm.comp hφ₅),
    fun n => (hψ₁ε _).1, ?_⟩
  intro I₀ hI₀m hI₀
  obtain ⟨Φ, -, hΦ⟩ := hprep I₀ hI₀m hI₀
  let I : Ω → ℕ → ℕ := fun ω n => φ₅ (I₀ ω n)
  have hI : ∀ ω n, n ≤ I ω n := fun ω n => (hI₀ ω n).trans (hφ₅.id_le _)

  -- pathwise identification of the limit
  filter_upwards [hΦ, hgall, htests, hdeg, hS.isAreaParametrized, hS.ae_tendsto_cocompact,
    hS.isLQGMeasure, hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮)]
    with ω hΦω hgω htω hdω harea hp hμ hlf
  obtain ⟨hmono, ubar, hubar, hconv⟩ := hΦω
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  let : (S.μ ω).IsOpenPosMeasure := harea.isOpenPosMeasure
  have hJt : Tendsto (fun k => I ω (Φ ω k)) atTop atTop :=
    (tendsto_atTop_mono (hI ω) tendsto_id).comp hmono.tendsto_atTop
  have hsk0 : Tendsto (fun k => e (I ω (Φ ω k))) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨he.tendsto_zero.comp hJt, Eventually.of_forall fun k => hepos _⟩
  have hunif : ∀ O, IsCompact O → O ⊆ D → TendstoUniformlyOn
      (fun k => rescaledBallGreenKernel S r z y (e (I ω (Φ ω k))) ω) ubar atTop O := by
    intro O hO hOD
    have h := hconv O hO (by rw [hO.isClosed.closure_eq]; exact hOD)
    refine h.congr (Eventually.of_forall fun k x _ => ?_)
    show rescale (S.mε (e (I ω (Φ ω k)))) (e (I ω (Φ ω k))) (S.η ω) (u ω (I ω (Φ ω k))) x =
      rescaledBallGreenKernel S r z y (e (I ω (Φ ω k))) ω x
    rw [hu_eq ω hgω]
    rfl
  have hfinν : ∀ K, IsCompact K → ∀ᶠ k in atTop,
      degreeWeightedMeasure (S.mult (e (I ω (Φ ω k))) ω) (e (I ω (Φ ω k))) (S.η ω) (S.μ ω) K
        < ⊤ := fun K hK =>
    Eventually.of_forall fun k => degreeWeightedMeasure_lt_top harea.1 hp (hepos _) _ hK
  have hid : EqOn ubar (fun x => S.c₀ / 6 * greenFunction (ball z r) y x) D := by
    refine eqOn_of_uniform_limit_and_tests (μ := S.μ ω) hDo hDB (greenFunction (ball z r) y)
      ((continuousOn_greenFunction_ball_compl hy).mono hDy) S.c₀ ubar hubar
      (fun k => rescaledBallGreenKernel S r z y (e (I ω (Φ ω k))) ω)
      (fun k => degreeWeightedMeasure (S.mult (e (I ω (Φ ω k))) ω) (e (I ω (Φ ω k)))
        (S.η ω) (S.μ ω)) hfinν ?_ hunif f (fun i => (hfs i).continuous) hfc hfn hfloc ?_ ?_
    · intro h hhc hhs
      have hconvF : ∀ g ∈ F, Tendsto (fun k => ∫ x, g x ∂degreeWeightedMeasure
          (S.mult (e (I ω (Φ ω k))) ω) (e (I ω (Φ ω k))) (S.η ω) (S.μ ω)) atTop
          (𝓝 (∫ x, g x ∂((6 : ℝ≥0∞) • S.μ ω))) := by
        intro g hg
        rw [hgF] at hg
        obtain ⟨j, rfl⟩ := hg
        rw [integral_smul_measure, ENNReal.toReal_ofNat, smul_eq_mul]
        exact (hdω j).comp hJt
      have h' := tendsto_integral_of_denseTestFamilyC hfinν
        (fun K hK => by
          rw [Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_lt_top ENNReal.ofNat_lt_top hK.measure_lt_top)
        hFd hconvF h ⟨hhc, hhs⟩
      rwa [integral_smul_measure, ENNReal.toReal_ofNat, smul_eq_mul] at h'
    · intro i _
      exact Eventually.of_forall fun k => integrable_mul_rescale_degreeWeightedMeasure harea hp
        (hepos _) _ _ _ (hfs i).continuous (hfc i)
    · intro i hi
      have hiB : tsupport (f i) ⊆ ball z r := hi.trans hDB
      have h2i : T (2 * i) = f i := by
        have h1 : 2 * i % 2 = 0 := by omega
        have h2 : 2 * i / 2 = i := by omega
        simp [T, h1, h2]
      have h2i1 : T (2 * i + 1) = φc i hiB := by
        have h1 : (2 * i + 1) % 2 = 1 := by omega
        have h2 : (2 * i + 1) / 2 = i := by omega
        have hφc : ∀ (j : ℕ) (_ : j = i) (h : tsupport (f j) ⊆ ball z r), φc j h = φc i hiB := by
          rintro j rfl h
          rfl
        simp only [T, h1, one_ne_zero, ↓reduceIte]
        split_ifs with hh
        · exact hφc _ h2 _
        · exact absurd (by rw [h2]; exact hiB) hh
      have hy' := (htω (2 * i)).comp (hφ₄.tendsto_atTop.comp hJt)
      have hc' := (htω (2 * i + 1)).comp (hφ₄.tendsto_atTop.comp hJt)
      rw [h2i] at hy'
      rw [h2i1] at hc'
      exact hφconv i hiB (S.μ ω) (S.η ω) harea hp (fun k => e (I ω (Φ ω k)))
        (fun k => S.mε (e (I ω (Φ ω k)))) (fun k => S.mult (e (I ω (Φ ω k))) ω)
        (fun k => interiorCellVertices (e (I ω (Φ ω k))) (S.η ω) (ball z r))
        (fun k => vertexOf (e (I ω (Φ ω k))) (S.η ω) y) hsk0
        (Eventually.of_forall fun k => ⟨medianOf_nonneg _, fun b _ =>
          (mdeg_pos_of_ne_zero (hlf _ (hepos _))
            (S.mult_succ_ne_zero (hepos _).le ω b)).ne'⟩) _ _ hy' hc'
  exact ⟨Φ ω, hmono, (hunif _ hK₀c hK₀D).congr_right (hid.mono hK₀D)⟩

end MatedCRT.GreenEnvironment

namespace MatedCRT

/-- The prepared subsequence argument uses the Green-occupation and degree-measure
convergence inputs, including their stated normalizations. -/
theorem greenKernelPreparedSubsequenceStep (𝒮 : SpaceFillingSLEModel) :
    GreenKernelPreparedSubsequenceStep 𝒮 := by
  intro h210 h34 h214 h31 γ ρ hγ hγ2 hρ hρ1 Ω _ S hS r r' d z y hr hball hy hr' hd ε hε
  exact GreenEnvironment.exists_prepared_subseq_greenKernel_uniform 𝒮 h210 h34 h214 h31
    hγ hγ2 hρ hρ1 S hS hr hball hy hr' hd ε hε

/-- Lemma 3.3 from prepared tightness and the stated degree, occupation,
Green-kernel, and cell-size inputs. -/
theorem uniformConvergenceGreenKernel_of_prepared_tightness
    (𝒮 : SpaceFillingSLEModel)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 :=
  uniformConvergenceGreenKernel_of_prepared_subsequence 𝒮 h210 h34 h214 h28 h31
    (greenKernelPreparedSubsequenceStep 𝒮)

end MatedCRT

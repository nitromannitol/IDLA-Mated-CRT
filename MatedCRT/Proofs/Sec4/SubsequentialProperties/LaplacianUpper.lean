import MatedCRT.Proofs.Sec4.SubsequentialProperties.Subharmonic
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.GreenMarkov

/-!
# Lemma 4.8, item 3 (upper bound): `Δw̄*_t ≤ (c₀/6) μ_h` on `B_ρ`

Step 3 of the proof of Lemma 4.8 (paper/idla_mated_crt-corrected.tex, l.1859-1890). The paper compares
`q^ε_{B_r(z)} + w̃^ε_t` on each disc; here a single normalized exit time `q^ε_{B_ρ}` is used: by the corrected
Lemma 4.4 and `Δ^ε q^ε_{B_ρ} = -(deg^ε)⁻¹` (`normExitTimeLaplacianStep`), `q^ε_{B_ρ} + w̃^ε_t` is discrete
superharmonic on `V^ε(B_ρ) \ V^ε(∂B_ρ)`, so a uniform limit `w + q̄` is superharmonic on `B_ρ`
(`isSuperharmonicOn_neg_of_discrete`), i.e. `Δ(w + q̄) ≤ 0` weakly; with `Δq̄ = -(c₀/6) μ_h` (Lemma 3.7) this is
`Δw ≤ (c₀/6) μ_h`.

* `exists_strictMono_ae_tendstoUniformlyOn`: uniform convergence in probability gives almost sure uniform convergence
  along a deterministic subsequence;
* `odometer_integral_mul_laplacian_le`: item 3 (upper bound), pathwise.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls Real Laplacian
open scoped ENNReal

/-- **Uniform convergence in probability gives almost sure uniform convergence along a deterministic
subsequence.** -/
theorem exists_strictMono_ae_tendstoUniformlyOn {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {u : ℝ → Ω → ℂ → ℝ} {v : Ω → ℂ → ℝ} {K : Set ℂ} (h : TendstoUniformlyOnInProbability P u v K)
    {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n) (hεs0 : Tendsto εs atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, TendstoUniformlyOn (fun k => u (εs (φ k)) ω) (v ω) atTop K := by
  let E : ℕ → ℝ → Set Ω := fun j ε => {ω | ∀ x ∈ K, |u ε ω x - v ω x| ≤ 1 / ((j : ℝ) + 1)}
  have hE : ∀ j, ProbTendsToOne P (E j) := by
    intro j
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h (1 / ((j : ℝ) + 1)) (by positivity))
      (fun _ => zero_le) (fun ε => measure_mono ?_)
    intro ω hω
    by_contra hne
    apply hω
    intro x hx
    by_contra hlt
    exact hne ⟨x, hx, lt_of_not_ge hlt⟩
  obtain ⟨φ, hφ, hae⟩ := exists_strictMono_ae_eventually_mem_all hE hεs hεs0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae] with ω hω
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  filter_upwards [hω j] with k hk x hx
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (hk x hx) hj

/-- `Δ(-(W + Q)) ≥ 0` where `ΔW ≤ d` and `ΔQ = -d`. -/
theorem mLaplacian_neg_add_nonneg {m : ℤ → ℤ → ℕ} (hlf : ∀ a, {b | m a b ≠ 0}.Finite) {W Q : ℤ → ℝ} {a : ℤ}
    {d : ℝ} (hW : mLaplacian m W a ≤ d) (hQ : mLaplacian m Q a = -d) :
    0 ≤ mLaplacian m (fun x => -(W x + Q x)) a := by
  have h := mLaplacian_const_mul (m := m) (-1) (fun x => W x + Q x) a
  rw [mLaplacian_add_of_locallyFinite hlf] at h
  rw [show (fun x => -(W x + Q x)) = fun x => (-1 : ℝ) * (W x + Q x) from funext fun x => by ring, h]
  linarith

/-- **Lemma 4.8, item 3 (upper bound), pathwise**: along a sequence on which the discrete Dirichlet problems with hat
data converge at the centres of the rational discs and `q̄^{ε_k}_{B_ρ} → q̄` uniformly on `cl(B_ρ)`, where
`Δq̄ = -(c₀/6) μ_h` weakly on `B_ρ` (Lemma 3.7), every uniform limit `w` of the rescaled odometers satisfies
`∫ w Δf ≤ ∫ f d((c₀/6) μ_h)` for test functions `f ≥ 0` on `B_ρ`. -/
theorem odometer_integral_mul_laplacian_le {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
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
    {t : ℝ} (hupper : ∀ ε, 0 < ε → ∀ a ∈ ballInterior ε (S.η ω) ρ,
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
    ∀ f : ℂ → ℝ, IsTestFunction (ball 0 ρ) f → 0 ≤ f →
      Integrable f (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) →
      ∫ x, w x * Δ f x ≤ ∫ x, f x ∂(ENNReal.ofReal (S.c₀ / 6) • S.μ ω) := by
  have hv : ContinuousOn (-(w + qbar)) (closedBall 0 ρ) := (hwc.add hqc).neg
  have hconvU : TendstoUniformlyOn (fun k x => (S.mε (εk k))⁻¹ *
      (fun a => -(matedLeastSupersolution (S.mult (εk k) ω) (εk k) (S.η ω) ρ t a +
        normExitTime (S.mult (εk k) ω) (interiorCellVertices (εk k) (S.η ω) (ball 0 ρ)) a))
        (vertexOf (εk k) (S.η ω) x)) (-(w + qbar)) atTop (closedBall 0 ρ) := by
    refine (hconv.add hqconv).neg.congr (Eventually.of_forall fun k x _ => ?_)
    simp only [Pi.neg_apply, Pi.add_apply, rescaledMatedLeastSupersolution, rescale]
    ring
  have hsup := isSuperharmonicOn_neg_of_discrete S ω harea hp hlf hcells hmax hεk hεk0 hdir
    (U := fun k a => -(matedLeastSupersolution (S.mult (εk k) ω) (εk k) (S.η ω) ρ t a +
        normExitTime (S.mult (εk k) ω) (interiorCellVertices (εk k) (S.η ω) (ball 0 ρ)) a))
    hv hconvU isOpen_ball subset_rfl (by
      intro q₁ q₂ s hs hdisc
      refine Eventually.of_forall fun k a ha => ?_
      have ha' : a ∈ ballInterior (εk k) (S.η ω) ρ :=
        interiorCellVertices_subset_of_ball_subset harea.1 hs hρ (ball_subset_closedBall.trans hdisc) ha
      have hA : (interiorCellVertices (εk k) (S.η ω) (ball 0 ρ)).Finite :=
        (Tightness.cellVertices_finite harea.1 hp (hεk k) isBounded_ball).subset fun b hb => hb.1
      exact mLaplacian_neg_add_nonneg (hlf _ (hεk k)) (hupper (εk k) (hεk k) a ha')
        (normExitTimeLaplacianStep (S.mult (εk k) ω) _ (S.mult_symm _ ω) (hlf _ (hεk k))
          (fun i => S.mult_succ_ne_zero (hεk k).le ω i) hA a ha'))
  rw [neg_neg] at hsup
  have hle := laplacianLEOfSuperharmonicStep_holds _ (w + qbar) isOpen_ball
    ((hwc.add hqc).mono ball_subset_closedBall) hsup
  intro f hf hf0 _
  have h1 := hle.2 f hf hf0 integrable_zero_measure
  obtain ⟨-, -, h2⟩ := hqlap.2 f hf
  have hwint := integrable_mul_laplacian
    ((hwc.mono ball_subset_closedBall).locallyIntegrableOn measurableSet_ball) hf
  have hqint := integrable_mul_laplacian hqlap.1 hf
  have hfun : (fun x => (w + qbar) x * Δ f x) = fun x => w x * Δ f x + qbar x * Δ f x :=
    funext fun x => by rw [Pi.add_apply]; ring
  rw [hfun, integral_add hwint hqint, h2] at h1
  simp only [integral_zero_measure, zero_sub] at h1
  linarith

end MatedCRT

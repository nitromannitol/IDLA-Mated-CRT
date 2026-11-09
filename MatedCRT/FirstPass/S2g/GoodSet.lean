import MatedCRT.FirstPass.S2f
import MatedCRT.FirstPass.Frozen.S2g
import MatedCRT.FirstPass.S1c.Moments

/-!
# Good set, deterministic part: contact sets of certificates (fp-S2g, q1)

Pure potential theory on `B_R` with pole `0` (Armitage-Gardiner notation; HB `supersolutions`, `leastSupersolution`,
`cluster`). Written argument: `notes/fp-gaps/CHATGPT-cone-good-set.md` Section 4.1; the minimum principle and the
pole behaviour of the disc Green function are the frozen EXTERNAL inputs of `Frozen/S2g.lean`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- The contact set of a candidate `w` at time `t` on `B_R` with pole `0`: the points `x ∈ B_R` with `x = 0` or
`-t G_{B_R}(0,x) < w x`. This is the HB `cluster` with the candidate `w` in place of the least supersolution. -/
def certCluster (R t : ℝ) (w : ℂ → ℝ) : Set ℂ :=
  {x ∈ ball (0 : ℂ) R | x = 0 ∨ -t * greenFunction (ball 0 R) 0 x < w x}

/-- The contact set of a candidate is open when `w` is continuous on the closed ball and `t > 0`: away from the pole
this is the continuity of the Green function and of `w`; at the pole `-t G → -∞` while `w` is bounded below. -/
theorem isOpen_certCluster (hpole : FrozenGreenDiscPole) {R t : ℝ} (hR : 0 < R) (ht : 0 < t)
    {w : ℂ → ℝ} (hw : ContinuousOn w (closedBall (0 : ℂ) R)) : IsOpen (certCluster R t w) := by
  obtain ⟨hGc, hGtop⟩ := hpole R hR
  have hclosed : ∀ y ∈ ball (0 : ℂ) R, closedBall (0 : ℂ) R ∈ 𝓝 y := fun y hy =>
    mem_of_superset (isOpen_ball.mem_nhds hy) ball_subset_closedBall
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨hxb, hxc⟩ := hx
  by_cases hx0 : x = 0
  · subst hx0
    have hA : Tendsto (fun y => -t * greenFunction (ball 0 R) 0 y) (𝓝[≠] 0) atBot := by
      have h' := tendsto_neg_atTop_atBot.comp (hGtop.const_mul_atTop ht)
      exact Tendsto.congr (fun y => by simp [Function.comp_apply, neg_mul]) h'
    have hwc : ContinuousAt w 0 := hw.continuousAt (hclosed 0 (mem_ball_self hR))
    have hev : ∀ᶠ y in 𝓝 (0 : ℂ), w 0 - 1 < w y :=
      hwc.tendsto.eventually (lt_mem_nhds (sub_one_lt (w 0)))
    have hev2 : ∀ᶠ y in 𝓝[≠] (0 : ℂ), -t * greenFunction (ball 0 R) 0 y < w y := by
      filter_upwards [hA.eventually (eventually_lt_atBot (w 0 - 1)),
        eventually_nhdsWithin_of_eventually_nhds hev] with y h1 h2
      linarith
    have hev3 := eventually_nhdsWithin_iff.mp hev2
    filter_upwards [hev3, isOpen_ball.mem_nhds hxb] with y hy1 hy2
    by_cases hy : y = 0
    · exact ⟨hy2, Or.inl hy⟩
    · exact ⟨hy2, Or.inr (hy1 hy)⟩
  · have hxlt : -t * greenFunction (ball 0 R) 0 x < w x := hxc.resolve_left hx0
    have hGx : ContinuousAt (greenFunction (ball 0 R) 0) x := by
      apply ContinuousOn.continuousAt hGc
      have h1 : closedBall (0 : ℂ) R ∈ 𝓝 x := hclosed x hxb
      have h2 : ({0} : Set ℂ)ᶜ ∈ 𝓝 x := isOpen_compl_singleton.mem_nhds hx0
      exact mem_of_superset (inter_mem h1 h2) (fun y hy => ⟨hy.1, hy.2⟩)
    have hwx : ContinuousAt w x := hw.continuousAt (hclosed x hxb)
    have hlt : ∀ᶠ y in 𝓝 x, -t * greenFunction (ball 0 R) 0 y < w y :=
      (continuousAt_const.mul hGx).eventually_lt hwx hxlt
    filter_upwards [hlt, isOpen_ball.mem_nhds hxb] with y hy1 hy2
    exact ⟨hy2, Or.inr hy1⟩

/-- Integrability of `w Δφ` for a test function `φ` on `B_R` and a function `w` continuous only on the closed ball: the
integrand vanishes outside `B̄_R`, so it is integrable on the compact closed ball (`integrable_mul_laplacian` of S1c
needs a global continuous `w`). -/
theorem integrable_mul_laplacian_of_contOn {R : ℝ} {w : ℂ → ℝ} (hw : ContinuousOn w (closedBall (0 : ℂ) R))
    {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) R) φ) :
    Integrable (fun x => w x * Laplacian.laplacian φ x) := by
  have hΔ := continuous_laplacian_of_contDiff (contDiff_two_of_isTestFunction hφ)
  have hsupp : Function.support (fun x => w x * Laplacian.laplacian φ x) ⊆ closedBall (0 : ℂ) R := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hc
    have hxU : x ∉ ball (0 : ℂ) R := fun h => hc (ball_subset_closedBall h)
    apply hx
    simp only [laplacian_eq_zero_of_not_mem_tsupport hφ.2.2 hxU, mul_zero]
  have hint : IntegrableOn (fun x => w x * Laplacian.laplacian φ x) (closedBall (0 : ℂ) R) :=
    (hw.mul hΔ.continuousOn).integrableOn_compact (isCompact_closedBall (0 : ℂ) R)
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hint

/-- **Deterministic comparison (written argument: `notes/fp-gaps/CHATGPT-cone-good-set.md` Section 4.1).** Let `w` be a
supersolution for the obstacle `-t G_{B_R}(0,·)` with zero boundary values, and suppose `Δw = μ|_A` in `B_R` for the
contact set `A = certCluster R t w` (condition C4). Then `w` lies below every supersolution `v` with the same obstacle.
The proof applies the minimum principle `FrozenSuperharmonicMinimumPrinciple` to `v - w` on the open set `A`. -/
theorem certificate_le_supersolution (hmin : FrozenSuperharmonicMinimumPrinciple) (hpole : FrozenGreenDiscPole)
    {μ : Measure ℂ} {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (hμ : μ (closedBall (0 : ℂ) R) < ⊤)
    {w : ℂ → ℝ} (hw : w ∈ supersolutions μ R 0 t) (hbd : ∀ x ∈ sphere (0 : ℂ) R, w x = 0)
    (hC4 : HasLaplacian w (μ.restrict (certCluster R t w)) 0 (ball (0 : ℂ) R)) :
    ∀ v ∈ supersolutions μ R 0 t, ∀ x ∈ closedBall (0 : ℂ) R, w x ≤ v x := by
  intro v hv x hx
  obtain ⟨hvc, hvL, hvob⟩ := hv
  obtain ⟨hwc, -, -⟩ := hw
  set A := certCluster R t w with hAdef
  have hAopen : IsOpen A := isOpen_certCluster hpole hR ht hwc
  have h0A : (0 : ℂ) ∈ A := ⟨mem_ball_self hR, Or.inl rfl⟩
  have hAball : A ⊆ ball (0 : ℂ) R := fun y hy => hy.1
  have hAcl : closure A ⊆ closedBall (0 : ℂ) R :=
    closure_minimal (hAball.trans ball_subset_closedBall) isClosed_closedBall
  -- off the contact set, `w` lies below the obstacle (on the sphere both sides vanish)
  have hoff : ∀ y ∈ closedBall (0 : ℂ) R, y ∉ A → w y ≤ -t * greenFunction (ball 0 R) 0 y := by
    intro y hy hyA
    by_cases hyb : y ∈ ball (0 : ℂ) R
    · exact not_lt.mp (fun h => hyA ⟨hyb, Or.inr h⟩)
    · have hd : dist y 0 = R :=
        le_antisymm (mem_closedBall.mp hy) (not_lt.mp (fun h => hyb (mem_ball.mpr h)))
      have hys : y ∈ sphere (0 : ℂ) R := mem_sphere.mpr hd
      simp [hbd y hys, greenFunction_of_notMem_right (show y ∉ ball (0 : ℂ) R from hyb)]
  have hfc : ContinuousOn (fun y => v y - w y) (closure A) :=
    (hvc.mono hAcl).sub (hwc.mono hAcl)
  have hfr : ∀ y ∈ frontier A, 0 ≤ v y - w y := by
    intro y hy
    rw [hAopen.frontier_eq] at hy
    obtain ⟨hycl, hyA⟩ := hy
    have hyc : y ∈ closedBall (0 : ℂ) R := hAcl hycl
    have hyne : y ≠ 0 := fun h => hyA (by rw [h]; exact h0A)
    linarith [hoff y hyc hyA, hvob y hyc hyne]
  have htest : ∀ φ : ℂ → ℝ, IsTestFunction A φ → 0 ≤ φ →
      ∫ y, (v y - w y) * Laplacian.laplacian φ y ≤ 0 := by
    intro φ hφ hφ0
    have hφB : IsTestFunction (ball (0 : ℂ) R) φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hAball⟩
    have hφout : ∀ y, y ∉ A → φ y = 0 := fun y hy => eq_zero_of_not_mem_tsupport_fn hφ.2.2 hy
    have hφμ : Integrable φ μ :=
      integrable_of_continuous_of_support hμ hφ.1.continuous
        (fun y hy => hφout y (fun hyA => hy (ball_subset_closedBall (hAball hyA))))
    have hvineq := hvL.2 φ hφB hφ0 hφμ
    obtain ⟨-, hCw⟩ := hC4
    obtain ⟨-, -, hCwEq⟩ := hCw φ hφB
    have hrestr : ∫ y, φ y ∂(μ.restrict A) = ∫ y, φ y ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => hφout y hy)
    rw [integral_zero_measure, sub_zero] at hCwEq
    have hIv := integrable_mul_laplacian_of_contOn hvc hφB
    have hIw := integrable_mul_laplacian_of_contOn hwc hφB
    have hsplit : ∫ y, (v y - w y) * Laplacian.laplacian φ y
        = (∫ y, v y * Laplacian.laplacian φ y) - ∫ y, w y * Laplacian.laplacian φ y := by
      simp only [sub_mul]
      exact integral_sub hIv hIw
    rw [hsplit, hCwEq, hrestr]
    linarith [hvineq]
  have hLL : LocallyIntegrableOn (fun y => v y - w y) A :=
    (hfc.mono subset_closure).locallyIntegrableOn hAopen.measurableSet
  have hLLf : LaplacianLE (fun y => v y - w y) 0 A :=
    ⟨hLL, fun φ hφ hφ0 _ => by rw [integral_zero_measure]; exact htest φ hφ hφ0⟩
  have hfA : ∀ y ∈ A, 0 ≤ v y - w y :=
    hmin A (fun y => v y - w y) hAopen (isBounded_ball.subset hAball) hfc hLLf hfr
  by_cases hxA : x ∈ A
  · linarith [hfA x hxA]
  · have hxne : x ≠ 0 := fun h => hxA (by rw [h]; exact h0A)
    linarith [hoff x hx hxA, hvob x hx hxne]

end MatedCRT

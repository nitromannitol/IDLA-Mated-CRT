import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauCanonicalLaw
import MatedCRT.Proofs.Sec4.Prop42Closure.ScaledRegularizedFamily

/-! # FIRST PASS S2k: plateau scale invariance without the bounded-representative input H (task fp-S2k-closure-inside)

Written argument: `notes/fp-gaps/CHATGPT-closure-inside-cycle.md` section 4.1, eqs (11)-(14). The route Z5 of
`Proofs/Sec4/Prop42Closure/PlateauCanonicalLaw.lean` (`plateauScaleInvarianceStep_of_canonical`) takes the regularized
family of the dilated measure from the input H (`ScaledBoundedRepresentativesStep`), which is false for general measures
(steps3:117-137). Here it is not assumed. The canonical radii of the dilated measure `μ'' = scaledMeasure μ a c` are computed
from the regularized family of `μ` alone, through `regularizedCluster_rescaledMeasure` (a deterministic identity). Only the
Harmonic-Balls Draft input I2 (`LQGVolumeGrowthAllScalesStmt`) and the coordinate rule (`InsertionLQGScalingLawStep`, input K,
frozen as `FrozenInsertionCoordinateRule` in `FirstPass/Frozen/S2k.lean`) are used. -/

namespace MatedCRT.FirstPass.S2k

open MeasureTheory Filter Set Metric HarmonicBalls ProbabilityTheory
open scoped Pointwise ENNReal

/-- The preimage of a set under the dilation `x ↦ a x` is the image under `x ↦ a⁻¹ x`, i.e. the set of the scaled family. -/
theorem preimage_mul_eq_scaledFamily_fiber (Λ : ℝ → Set ℂ) {a c : ℝ} (ha : 0 < a) (t : ℝ) :
    (fun x : ℂ => (a : ℂ) * x) ⁻¹' Λ (c * t) = scaledFamily Λ a c t := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  ext x
  constructor
  · intro hx
    exact ⟨(a : ℂ) * x, hx, by push_cast; exact inv_mul_cancel_left₀ ha0 x⟩
  · rintro ⟨y, hy, rfl⟩
    show (a : ℂ) * (((a⁻¹ : ℝ) : ℂ) * y) ∈ Λ (c * t)
    rw [show (a : ℂ) * (((a⁻¹ : ℝ) : ℂ) * y) = y by push_cast; exact mul_inv_cancel_left₀ ha0 y]
    exact hy

/-- **Canonical radii of a dilated measure (H-free).** If `ν` has the regularized family `Λ` at `0`, and `ν'` is the
dilation `scaledMeasure ν a c` with volume growth on every disk `B_{n+1}`, then for every `t > 0` the canonical radius of
`ν'` equals the radius of the scaled family `Λ_a(t) = a⁻¹ Λ(c t)`. Proof: the code radii of `G n ν'` are eventually
(in `n`) those of the regularized cluster of `ν'` at radius `n+1`, which equals `a⁻¹` times `regularizedCluster ν (a(n+1)) 0 (c t)`,
and that equals `Λ (c t)` once `a (n+1) ≥ s`, where `closure Λ(ct) ⊆ B_s` (third conjunct of `IsRegularizedClusterFamily`). -/
theorem canonicalRadius_scaledMeasure_eq {G : ℕ → Measure ℂ → ℝ → Set ℂ}
    (hG : ∀ n : ℕ, CanonicalRawClusterFamily ((n : ℝ) + 1) (G n))
    {ν ν' : Measure ℂ} {Λ : ℝ → Set ℂ} {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hν' : ν' = scaledMeasure ν a c) (hΛ : IsRegularizedClusterFamily ν Λ 0)
    (hgood : ∀ n : ℕ, IsLocallyFiniteMeasure ν' ∧ ∃ βminus βplus : ℝ, VolumeGrowth ν' ((n : ℝ) + 1) βminus βplus)
    {t : ℝ} (ht : 0 < t) :
    canonicalRadius G t ν' = familyRadius (scaledFamily Λ a c t) := by
  have hcpos : 0 < c * t := mul_pos hc ht
  -- a radius `s > 0` with `closure (Λ (c t)) ⊆ B_s`, from boundedness of the time-`c t` cluster
  obtain ⟨r0, hr0⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 (hΛ.1.isBounded (c * t) hcpos).closure
  set s : ℝ := |r0| + 1 with hsdef
  have hs0 : 0 < s := by positivity
  have hcl : closure (Λ (c * t)) ⊆ ball (0 : ℂ) s :=
    hr0.trans (Metric.closedBall_subset_ball (by linarith [le_abs_self r0]))
  have hreg : ∀ r' : ℝ, s ≤ r' → Λ (c * t) = regularizedCluster ν r' 0 (c * t) :=
    fun r' hr' => hΛ.2.2 (c * t) hcpos s hs0 hcl r' hr'
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hev : ∀ᶠ n : ℕ in atTop, codeRadius (G n) t ν' = familyRadius (scaledFamily Λ a c t) := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, s / a ≤ (N : ℝ) := exists_nat_ge (s / a)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn' : s ≤ a * ((n : ℝ) + 1) := by
      have h1 : s / a ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hn)
      have h2 : s ≤ (n : ℝ) * a := (div_le_iff₀ ha).1 h1
      nlinarith
    obtain ⟨hloc, hV⟩ := hgood n
    rw [codeRadius_eq_familyRadius (hG n) hloc hV ht]
    rw [hν', scaledMeasure_eq_rescaledMeasure ν hc, regularizedCluster_rescaledMeasure ν ha hc hnpos,
      ← hreg (a * ((n : ℝ) + 1)) hn', preimage_mul_eq_scaledFamily_fiber Λ ha t]
  unfold canonicalRadius
  rw [Filter.limsup_congr hev, Filter.limsup_const]

/-- **`PlateauScaleInvarianceStep`, without H.** For `a, r > 0` the probability that `r` is a plateau value of the regularized
family equals the probability that `a r` is one (draft line 265, `p(r) = p(ar)`). Inputs: I2 and the coordinate rule K
(through `InsertionLQGScalingLawStep`). The proof compares the canonical plateau events of `μ` and of its dilation `μ''`
(identity in law by K, measurability by `measurableSet_canonicalPlateauSet`), and identifies the plateau event of the
scaled family with the canonical one of `μ''` (`canonicalRadius_scaledMeasure_eq`). -/
theorem plateauScaleInvarianceStep_HBfree (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : InsertionLQGScalingLawStep) : PlateauScaleInvarianceStep := by
  intro γ α hγ hγ2 hα Ω _ P hC hcirc μ Λ hP hWP hLQG hreg a r ha hr
  obtain ⟨hC'', hcirc'', μ'', c, hWP'', hLQG'', hcoord, hid⟩ :=
    hK γ α hγ hγ2 hα Ω P hC hcirc μ hP hWP hLQG a ha
  have hμ : ∀ᵐ ω ∂P, μ'' ω = scaledMeasure (μ ω) a (c ω) := by
    filter_upwards [hcoord] with ω hω
    exact (scaledMeasure_eq_of_map hω.1 hω.2).symm
  obtain ⟨βm, βp, hvg⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hWP hLQG
  obtain ⟨βm', βp', hvg'⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hWP'' hLQG''
  have hvgN : ∀ᵐ ω ∂P, ∀ n : ℕ, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus : ℝ, VolumeGrowth (μ ω) ((n : ℝ) + 1) βminus βplus :=
    hvg.mono fun ω hω n => ⟨hω.1, βm, βp, hω.2 ((n : ℝ) + 1) (by positivity)⟩
  have hvgN' : ∀ᵐ ω ∂P, ∀ n : ℕ, IsLocallyFiniteMeasure (μ'' ω) ∧
      ∃ βminus βplus : ℝ, VolumeGrowth (μ'' ω) ((n : ℝ) + 1) βminus βplus :=
    hvg'.mono fun ω hω n => ⟨hω.1, βm', βp', hω.2 ((n : ℝ) + 1) (by positivity)⟩
  obtain ⟨G, hG⟩ := exists_canonicalRawClusterFamilies
  have hmono : ∀ᵐ ω ∂P, MonotoneOn (fun t => familyRadius (Λ ω t)) (Ioi 0) := by
    filter_upwards [hreg] with ω h1
    exact familyRadius_monotoneOn_of_regularized h1
  -- the canonical radii of the dilated measure are the radii of the scaled family, at all positive times
  have hradius : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < (q : ℝ) →
      canonicalRadius G (q : ℝ) (μ'' ω) = familyRadius (scaledFamily (Λ ω) a (c ω) (q : ℝ)) := by
    filter_upwards [hμ, hcoord, hvgN', hreg] with ω h1 h2 h3 h4
    intro q hq
    exact canonicalRadius_scaledMeasure_eq hG ha h2.1 h1 h4 h3 hq
  -- the plateau event of the scaled family is the canonical plateau event of `μ''`
  have hplat : {ω | r ∈ plateauValues (scaledFamily (Λ ω) a (c ω))} =ᵐ[P]
      μ'' ⁻¹' canonicalPlateauSet G r := by
    filter_upwards [hradius] with ω hω
    refine propext ?_
    change r ∈ plateauValues _ ↔ r ∈ plateauValuesOf (fun q : ℚ => canonicalRadius G (q : ℝ)) (μ'' ω)
    unfold plateauValues plateauValuesOf
    constructor
    · rintro ⟨hr0, s, t, hs, hst, h1, h2⟩
      exact ⟨hr0, s, t, hs, hst, (hω s hs).trans h1, (hω t (hs.trans hst)).trans h2⟩
    · rintro ⟨hr0, s, t, hs, hst, h1, h2⟩
      exact ⟨hr0, s, t, hs, hst, (hω s hs).symm.trans h1, (hω t (hs.trans hst)).symm.trans h2⟩
  calc P {ω | r ∈ plateauValues (Λ ω)}
      = P (μ ⁻¹' canonicalPlateauSet G r) :=
        measure_congr (plateau_event_ae_eq_canonical hvgN hreg hG r)
    _ = P (μ'' ⁻¹' canonicalPlateauSet G r) :=
        (hid.measure_mem_eq (measurableSet_canonicalPlateauSet hG r)).symm
    _ = P {ω | r ∈ plateauValues (scaledFamily (Λ ω) a (c ω))} := measure_congr hplat.symm
    _ = P {ω | a * r ∈ plateauValues (Λ ω)} := by
        apply measure_congr
        filter_upwards [hcoord, hmono] with ω h3 h4
        exact propext (mem_plateauValues_scaledFamily_iff ha h3.1 h4 r)

end MatedCRT.FirstPass.S2k

import MatedCRT.FirstPass.S2y.ConeDecoder250

/-!
# A Borel decoder of the circle smears of a circle average process

For a test function `φ` and a circle average process `q : Set.Ioi 0 × ℂ → ℝ` (`ConeCircleCode`), the circle smear at
radius `ε` is `∫ φ(z) q(ε, z) dz`. The *circle smear limit* `circleSmearLimit φ q` is the `limsup` of the pairing
approximants `pairingApprox φ n q` (the circle smears at the dyadic radii `pairingRadius n = 2^{-(n+1)}`, read through
midpoint Riemann sums). It is a Borel function of `q` for the product σ-algebra, and it equals
`lim_{ε → 0+} ∫ φ(z) q(ε, z) dz` whenever every circle slice `z ↦ q(ε, z)` is continuous and the limit exists.

## Main statements

* `measurable_circleSmearLimit`: `q ↦ circleSmearLimit φ q` is measurable.
* `circleSmearCode_eq_integral`: for a continuous slice, the Riemann-sum code is the circle smear.
* `circleSmearLimit_eq_of_tendsto`: the decoder returns the limit of the circle smears.
* `circleSmearLimit_circleProcess_eq_of_tendsto`: the same for `circleProcess p` with `p` jointly continuous on
  `(0, ∞) × ℂ`.
-/

open MeasureTheory Filter Topology Set

open MatedCRT.LQGMeasure

namespace MatedCRT.FirstPass.Derived

/-- The circle smear limit of a circle average process: the `limsup` of the dyadic pairing approximants. -/
noncomputable def circleSmearLimit (φ : ℂ → ℝ) (q : MatedCRT.ConeCircleCode) : ℝ :=
  limsup (fun n => pairingApprox φ n q) atTop

/-- The circle smear limit is a Borel function of the circle average process. -/
theorem measurable_circleSmearLimit (φ : ℂ → ℝ) : Measurable (circleSmearLimit φ) :=
  Measurable.limsup fun n => measurable_pairingApprox φ n

/-- For a continuous circle slice, the Riemann-sum code of the circle smear is the circle smear itself. -/
theorem circleSmearCode_eq_integral {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) {ε : ℝ}
    (hε : 0 < ε) {q : MatedCRT.ConeCircleCode} (hq : Continuous fun z => q (⟨ε, hε⟩, z)) :
    circleSmearCode φ ε hε q = ∫ z, φ z * q (⟨ε, hε⟩, z) :=
  (planeQuad_tendsto_integral (hφ.mul hq) hφc.mul_right).limsup_eq

/-- **The decoder returns the limit of the circle smears.** If every circle slice of `q` is continuous and the circle
smears `∫ φ(z) q(ε, z) dz` converge as `ε → 0+`, then `circleSmearLimit φ q` is their limit. -/
theorem circleSmearLimit_eq_of_tendsto {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {q : MatedCRT.ConeCircleCode} (hq : ∀ (ε : ℝ) (hε : 0 < ε), Continuous fun z => q (⟨ε, hε⟩, z))
    {L : ℝ} (hL : Tendsto (fun ε => ∫ z, φ z * coneCircleFun q ε z) (𝓝[>] 0) (𝓝 L)) :
    circleSmearLimit φ q = L := by
  have hr : Tendsto pairingRadius atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨pairingRadius_tendsto, Eventually.of_forall pairingRadius_pos⟩
  have hseq : (fun n => pairingApprox φ n q) =
      (fun ε => ∫ z, φ z * coneCircleFun q ε z) ∘ pairingRadius := by
    funext n
    simp only [Function.comp_apply, pairingApprox]
    rw [circleSmearCode_eq_integral hφ hφc (pairingRadius_pos n) (hq _ (pairingRadius_pos n))]
    simp [coneCircleFun, pairingRadius_pos n]
  unfold circleSmearLimit
  rw [hseq]
  exact (hL.comp hr).limsup_eq

/-- **The decoder on a jointly continuous circle average process.** If `p` is continuous on `(0, ∞) × ℂ` and
`∫ φ(z) p(ε, z) dz` converges as `ε → 0+`, then `circleSmearLimit φ (circleProcess p)` is the limit. -/
theorem circleSmearLimit_circleProcess_eq_of_tendsto {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {p : ℝ → ℂ → ℝ} (hp : ContinuousOn (fun x : ℝ × ℂ => p x.1 x.2) (Ioi 0 ×ˢ univ)) {L : ℝ}
    (hL : Tendsto (fun ε => ∫ z, φ z * p ε z) (𝓝[>] 0) (𝓝 L)) :
    circleSmearLimit φ (MatedCRT.circleProcess p) = L := by
  refine circleSmearLimit_eq_of_tendsto hφ hφc (fun ε hε => ?_) ?_
  · exact hp.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hε, mem_univ z⟩
  · refine hL.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
    simp [coneCircleFun, MatedCRT.circleProcess, hε]

end MatedCRT.FirstPass.Derived

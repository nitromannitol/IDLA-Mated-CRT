import MatedCRT.Defs.Notation

/-!
# Countable reduction of the uniform volume lower bound

The uniform lower bound of `VolumeGrowthStmt` (Draft Lemma 2.8-type input, `Draft/Section2.lean:121`) says that at scale `δ`,
for all centres `z ∈ B_{1-δ}`, the LQG mass of the ball is at least `δ^{βm}` (with polynomially high probability). The
cutoff of `DyadicCutoff68` needs events that are measurable in the field σ-algebra. This file replaces the uncountable
intersection over centres by the countable intersection over a fixed countable dense set `D`, at the half radius
`δ/2`. This is the standard mass-comparison step: a ball of radius `δ/2` around a point `w` within `δ/2` of `z` lies in
the ball of radius `δ` around `z`.

* `volumeLowerEvent μ βm δ` : the Draft event (lower half), uniform in the centre.
* `volumeCountableEvent μ βm D δ` : the countable event (centres in `D`, radius `δ/2`, constant `(δ/2)^{βm}`).
* `polyHighProb_volumeCountable` : `PolyHighProb` transfers to the countable event (the complement is inside the
  complement of the Draft event at scale `δ/2`).
* `lower_of_countable` : the countable event gives the uniform lower bound at scale `δ` for every centre.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRT
namespace VolumeCountable68

variable {Ω : Type*}

/-- The lower half of the Draft volume-growth event at scale `δ`: all centres `z ∈ ball 0 (1-δ)`. -/
def volumeLowerEvent (μ : Ω → Measure ℂ) (βm : ℝ) (δ : ℝ) : Set Ω :=
  {ω | ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ βm) ≤ μ ω (ball z δ)}

/-- The countable event at scale `δ`: centres `w ∈ D ∩ ball 0 (1-δ)`, radius `δ/2`, constant `(δ/2)^{βm}`. -/
def volumeCountableEvent (μ : Ω → Measure ℂ) (βm : ℝ) (D : Set ℂ) (δ : ℝ) : Set Ω :=
  {ω | ∀ w ∈ D, w ∈ ball (0 : ℂ) (1 - δ) → ENNReal.ofReal ((δ / 2) ^ βm) ≤ μ ω (ball w (δ / 2))}

lemma measurableSet_volumeCountableEvent {F : MeasurableSpace Ω} {μ : Ω → Measure ℂ} {βm : ℝ} {D : Set ℂ}
    (hDc : D.Countable) (hμm : ∀ (w : ℂ) (r : ℝ), Measurable[F] (fun ω => μ ω (ball w r))) (δ : ℝ) :
    MeasurableSet[F] (volumeCountableEvent μ βm D δ) := by
  have hEq : volumeCountableEvent μ βm D δ = ⋂ w ∈ D,
      {ω | w ∈ ball (0 : ℂ) (1 - δ) → ENNReal.ofReal ((δ / 2) ^ βm) ≤ μ ω (ball w (δ / 2))} := by
    ext ω
    simp [volumeCountableEvent]
  rw [hEq]
  refine MeasurableSet.biInter hDc fun w _ => ?_
  by_cases hw : w ∈ ball (0 : ℂ) (1 - δ)
  · have hset : {ω | w ∈ ball (0 : ℂ) (1 - δ) → ENNReal.ofReal ((δ / 2) ^ βm) ≤ μ ω (ball w (δ / 2))} =
        {ω | ENNReal.ofReal ((δ / 2) ^ βm) ≤ μ ω (ball w (δ / 2))} := by
      ext ω
      simp [hw]
    rw [hset]
    exact measurableSet_le measurable_const (hμm w (δ / 2))
  · have hset : {ω | w ∈ ball (0 : ℂ) (1 - δ) → ENNReal.ofReal ((δ / 2) ^ βm) ≤ μ ω (ball w (δ / 2))} = univ := by
      ext ω
      simp [hw]
    rw [hset]
    exact MeasurableSet.univ

/-- The countable event is contained in the Draft event at the half scale: the centres `w ∈ D` form a
subset of the centres `z ∈ ball 0 (1 - δ/2)`. -/
lemma volumeLowerEvent_half_subset_countable (μ : Ω → Measure ℂ) (βm : ℝ) (D : Set ℂ) {δ : ℝ} (hδ : 0 ≤ δ) :
    volumeLowerEvent μ βm (δ / 2) ⊆ volumeCountableEvent μ βm D δ := by
  intro ω hω w _ hwU
  have hz : w ∈ ball (0 : ℂ) (1 - δ / 2) := by
    rw [mem_ball] at hwU ⊢
    linarith
  exact hω w hz

/-- **Transfer of `PolyHighProb`** to the countable event: the complement of the countable event is contained in the
complement of the Draft event at half the scale, so the polynomial rate survives (with constant `C (1/2)^p`). -/
lemma polyHighProb_volumeCountable {m : MeasurableSpace Ω} (P : Measure Ω) (μ : Ω → Measure ℂ) (βm : ℝ)
    (D : Set ℂ) (hV : HarmonicBalls.PolyHighProb P (volumeLowerEvent μ βm)) :
    HarmonicBalls.PolyHighProb P (volumeCountableEvent μ βm D) := by
  obtain ⟨p, hp, C, r₀, hr₀, hpoly⟩ := hV
  refine ⟨p, hp, C * (1 / 2) ^ p, 2 * r₀, by positivity, fun δ hδ hδr => ?_⟩
  have hsub : volumeLowerEvent μ βm (δ / 2) ⊆ volumeCountableEvent μ βm D δ :=
    volumeLowerEvent_half_subset_countable μ βm D hδ.le
  have hcompl : (volumeCountableEvent μ βm D δ)ᶜ ⊆ (volumeLowerEvent μ βm (δ / 2))ᶜ :=
    compl_subset_compl.2 hsub
  calc P (volumeCountableEvent μ βm D δ)ᶜ ≤ P (volumeLowerEvent μ βm (δ / 2))ᶜ := measure_mono hcompl
    _ ≤ ENNReal.ofReal (C * (δ / 2) ^ p) := hpoly (δ / 2) (by positivity) (by linarith)
    _ = ENNReal.ofReal (C * (1 / 2) ^ p * δ ^ p) := by
      congr 1
      rw [Real.div_rpow hδ.le (by norm_num : (0 : ℝ) ≤ 2), Real.div_rpow zero_le_one (by norm_num : (0 : ℝ) ≤ 2), Real.one_rpow]
      ring

/-- **Uniform lower bound from the countable event.** If `ω` lies in the countable event at scale `δ` and `D` is dense,
then for every centre `z ∈ ball 0 (1-δ)` the ball of radius `δ` around `z` has mass at least `(δ/2)^{βm}`. -/
lemma lower_of_countable (μ : Ω → Measure ℂ) (βm : ℝ) {D : Set ℂ} (hD : Dense D) {δ : ℝ} (hδ : 0 < δ)
    {ω : Ω} (hω : ω ∈ volumeCountableEvent μ βm D δ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (1 - δ)) :
    ENNReal.ofReal ((δ / 2) ^ βm) ≤ μ ω (ball z δ) := by
  have hopen : IsOpen (ball z (δ / 2) ∩ ball (0 : ℂ) (1 - δ)) := isOpen_ball.inter isOpen_ball
  have hne : (ball z (δ / 2) ∩ ball (0 : ℂ) (1 - δ)).Nonempty :=
    ⟨z, mem_ball_self (half_pos hδ), hz⟩
  obtain ⟨w, hwD, hwU⟩ := hD.exists_mem_open hopen hne
  obtain ⟨hwz, hw0⟩ := hwU
  have hsub : ball w (δ / 2) ⊆ ball z δ := by
    intro x hx
    rw [mem_ball] at hx hwz ⊢
    have := dist_triangle x w z
    linarith
  calc ENNReal.ofReal ((δ / 2) ^ βm) ≤ μ ω (ball w (δ / 2)) := hω w hwD hw0
    _ ≤ μ ω (ball z δ) := measure_mono hsub

#print axioms MatedCRT.VolumeCountable68.polyHighProb_volumeCountable
#print axioms MatedCRT.VolumeCountable68.lower_of_countable
#print axioms MatedCRT.VolumeCountable68.measurableSet_volumeCountableEvent

end VolumeCountable68
end MatedCRT

import MatedCRT.FirstPass.Derived.MarkovTimeChangeEuclid
import LatticeProb.Prob.CrossingTimesClock19

/-!
# Adaptedness of the inverse crossing clock of a Markovian time-changed planar Brownian motion

For a Markovian time-changed planar Brownian motion `P` (`MatedCRT.IsMarkovTCBM`, Definitions 7.1-7.2 of
Berestycki-Gwynne), the inverse crossing clock `A_s` of the half-speed Euclidean path is a fixed measurable
functional `F_s` of the path read in its crossing clock (`IsMarkovTCBM.exists_clockFunctional`).  Under the
planar Brownian law `planarLaw z`, the half-speed Euclidean reading `halfRead` of the Brownian path is the
clock-read path of the coupling `X = B ∘ τ`, and `F_s ∘ halfRead` agrees almost surely with a functional that
is measurable for the natural filtration `F⁰_{s/2}` of the planar path: the adaptedness of the clock, which
is the `adapted` field of `IsPCAF`.

* `measurable_halfRead_pathFiltration`: `halfRead` is measurable from `F⁰_{s/2}` to the σ-algebra of the
  coordinates at times `≤ s` on `ℝ≥0 → ℝ²`;
* `IsMarkovTCBM.exists_adaptedClock`: the clock functionals and their adapted versions.
-/

open MeasureTheory MarkovProcess Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace MatedCRT

open PlanarBrownianSpace

/-- The half-speed Euclidean reading of a planar path up to time `s` is a function of the planar path up to
time `s / 2`. -/
theorem measurable_halfRead_pathFiltration (s : ℝ≥0) :
    Measurable[pathFiltration (2⁻¹ * s), LatticeProb.coordPast (EuclideanSpace ℝ (Fin 2)) s]
      halfRead := by
  rw [measurable_iff_comap_le]
  unfold LatticeProb.coordPast
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup₂_le fun u hu => ?_
  refine le_trans ?_ (le_iSup₂_of_le (2⁻¹ * u) (mul_le_mul_of_nonneg_left hu (by norm_num)) le_rfl)
  rw [← measurable_iff_comap_le]
  have hm : Measurable[MeasurableSpace.comap (fun ω : ContinuousPath ℂ => ω (2⁻¹ * u)) inferInstance]
      (fun ω : ContinuousPath ℂ => ω (2⁻¹ * u)) := comap_measurable _
  exact toEuclid.continuous.measurable.comp hm

/-- **The inverse crossing clock of a Markovian time-changed planar Brownian motion is adapted.**  There is a
threshold `m ∈ (0, ∞)` such that for every `s ≥ 0` there is a measurable functional `F` with
`A_s = F (clock-read path)` almost surely under every `euclidFamily P y`, the shift identity for the
increments of `A`, and, for every planar starting point `z`, a functional `g` measurable for the natural
filtration of the planar path up to time `s / 2` with `F (halfRead ω) = g ω` for `planarLaw z`-almost every
path `ω`. -/
theorem IsMarkovTCBM.exists_adaptedClock {P : PathLawFamily} (h : IsMarkovTCBM P) :
    ∃ m : ℝ≥0∞, 0 < m ∧ m < ⊤ ∧ ∀ s : ℝ≥0,
      ∃ F : (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ, Measurable F ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        (LatticeProb.pathClockInv m x s).toReal =
          F fun t => LatticeProb.clockPath m (fun u => x u) t) ∧
      (∀ y (t : ℝ≥0), ∀ᵐ x ∂(euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        (LatticeProb.pathClockInv m x (t + s)).toReal = (LatticeProb.pathClockInv m x t).toReal +
          F fun q => LatticeProb.clockPath m (fun u => x u) (t + q)) ∧
      ∀ z : ℂ, ∃ g : ContinuousPath ℂ → ℝ≥0, Measurable[pathFiltration (2⁻¹ * s)] g ∧
        (fun ω => Real.toNNReal (F (halfRead ω))) =ᵐ[planarLaw z] g := by
  obtain ⟨m, hm0, hmt, hlaw, hrest⟩ :=
    LatticeProb.exists_adaptedClockFunctional_timeChangedBM.{0} 2 (by norm_num)
  refine ⟨m, hm0, hmt, fun s => ?_⟩
  obtain ⟨F, hF, hFA, hFsh, hFad⟩ := hrest (continuous_euclidFamily P)
    (markovAt_euclidFamily h.2) (fun y => h.exists_coupling_euclid_core y) s
  refine ⟨F, hF, hFA, hFsh, fun z => ?_⟩
  obtain ⟨Ω, mΩ, Q, hQ, B, τ, X, h1, h2, h3, h4, h5, h6, h7⟩ :=
    h.exists_coupling_euclid (toEuclid z)
  have hmap : (euclidFamily P (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))).map
      (LatticeProb.clockRead m) = (planarLaw z).map halfRead := by
    rw [h6, hlaw Ω Q (toEuclid z) B τ X h1 h2 h3 h4 h5, h7, LinearIsometryEquiv.symm_apply_apply]
  obtain ⟨hh, hhm, hae⟩ := hFad (toEuclid z)
  rw [hmap] at hae
  exact ⟨hh ∘ halfRead, hhm.comp (measurable_halfRead_pathFiltration s),
    ae_of_ae_map (p := fun f => Real.toNNReal (F f) = hh f) measurable_halfRead.aemeasurable hae⟩

end MatedCRT

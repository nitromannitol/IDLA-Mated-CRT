import MatedCRT.FirstPass.Derived.MarkovTimeChangeAdapted
import LatticeProb.Prob.CrossingTimesClock20

/-!
# Adaptedness and goodness of the inverse crossing clock of a Markovian time-changed planar Brownian motion

This refines `IsMarkovTCBM.exists_adaptedClock` by two further conclusions of the same packaging theorem
(`LatticeProb.exists_goodAdaptedClockFunctional_timeChangedBM`), with the same threshold `m`:

* the law of the clock-read Euclidean path under `euclidFamily P (toEuclid z)` is the law of the half-speed
  reading of planar Brownian motion from `z` (the transfer of statements from the time-changed process to the
  Brownian path);
* almost surely under every `euclidFamily P y`, the crossing clock of the path is a good clock (strictly
  increasing and unbounded), so that the inverse crossing clock is nondecreasing and continuous, and the
  inverse crossing clock is strictly increasing and unbounded along the rationals (`InvClockStrict`).

* `IsMarkovTCBM.exists_goodAdaptedClock`: the clock functionals, their adapted versions, the law identification
  and the goodness of the crossing clock.
-/

open MeasureTheory MarkovProcess Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace MatedCRT

open PlanarBrownianSpace

/-- **Inverse crossing clock of a Markovian time-changed planar Brownian motion: law, goodness, adaptedness.**
There is a threshold `m ∈ (0, ∞)` such that
the clock-read path of the Euclidean time-changed process from `toEuclid z` has the law of `halfRead` of planar
Brownian motion from `z`; almost surely the crossing clock of every Euclidean path is good; and for every
`s ≥ 0` there is a measurable functional `F` with `A_s = F (clock-read path)` almost surely, the shift identity
for `A`, and an `F⁰_{s/2}`-measurable version of `F ∘ halfRead` under every `planarLaw z`. -/
theorem IsMarkovTCBM.exists_goodAdaptedClock {P : PathLawFamily} (h : IsMarkovTCBM P) :
    ∃ m : ℝ≥0∞, 0 < m ∧ m < ⊤ ∧
      (∀ z : ℂ, (euclidFamily P (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))).map
          (LatticeProb.clockRead m) = (planarLaw z).map halfRead) ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
          LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u)) ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
          LatticeProb.InvClockStrict m x) ∧
      ∀ s : ℝ≥0,
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
    LatticeProb.exists_goodAdaptedClockFunctional_timeChangedBM.{0} 2 (by norm_num)
  obtain ⟨hgood, hstrict, hF⟩ := hrest (continuous_euclidFamily P) (markovAt_euclidFamily h.2)
    (fun y => h.exists_coupling_euclid_core y)
  have hmap : ∀ z : ℂ, (euclidFamily P (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))).map
      (LatticeProb.clockRead m) = (planarLaw z).map halfRead := by
    intro z
    obtain ⟨Ω, mΩ, Q, hQ, B, τ, X, h1, h2, h3, h4, h5, h6, h7⟩ :=
      h.exists_coupling_euclid (toEuclid z)
    rw [h6, hlaw Ω Q (toEuclid z) B τ X h1 h2 h3 h4 h5, h7, LinearIsometryEquiv.symm_apply_apply]
  refine ⟨m, hm0, hmt, hmap, hgood, hstrict, fun s => ?_⟩
  obtain ⟨F, hFm, hFA, hFsh, hFad⟩ := hF s
  refine ⟨F, hFm, hFA, hFsh, fun z => ?_⟩
  obtain ⟨hh, hhm, hae⟩ := hFad (toEuclid z)
  rw [hmap z] at hae
  exact ⟨hh ∘ halfRead, hhm.comp (measurable_halfRead_pathFiltration s),
    ae_of_ae_map (p := fun f => Real.toNNReal (F f) = hh f) measurable_halfRead.aemeasurable hae⟩

end MatedCRT

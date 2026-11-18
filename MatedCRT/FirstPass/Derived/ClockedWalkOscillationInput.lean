import LatticeProb.Walk.ClockedExcursionStepOscillation
import MatedCRT.FirstPass.Derived.AreaCellWalkOscillation

/-! # Oscillation of a clocked excursion with bounded pre-exit steps

The general bound for the clocked excursion of the walk on a finite conductance network
(the hypothesis `hclock` of `ae_actualWalkExcursionSequence_curveOscillationLe_of_clocked`)
is a theorem of the Lattice-Probability library; here its statement is exhibited for an
arbitrary position map and the oscillation estimate of the walk skeleton is restated
without it. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace MatedCRT
open Set Metric MeasureTheory BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork
  ReflectedGMS ReflectedGMS.GMS LatticeProb LatticeProb.CellConfigInterpolation
open scoped unitInterval ENNReal NNReal
universe u

/-- **Oscillation of a clocked excursion with bounded pre-exit steps.** For every finite
conductance network `N` and position map `q`, the clocked excursion from `w` out of `B` has
oscillation at most `2 r + s'` almost surely, if the positions of the vertices of `B` and of
`w` lie in a ball of radius `r` and almost surely every step before the exit time has length at
most `s'`. -/
theorem clockedWalkExcursion_oscillation_of_steps {V : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] (N : FiniteConductanceNetwork V) (q : V → BouRabeeGwynne.Euc 2) :
    ∀ (B : Set V) (hB : ∀ w ∈ B, 0 < N.totalConductance w) (w : V)
      (c : BouRabeeGwynne.Euc 2) (r s' : ℝ), 0 ≤ s' → (∀ x ∈ B, q x ∈ ball c r) → q w ∈ ball c r →
      (∀ᵐ ω ∂N.trajectoryLaw B hB w, ∀ j : ℕ, (j : WithTop ℕ) < exitTime B ω →
        dist (q (ω (j + 1))) (q (ω j)) ≤ s') →
      ∀ᵐ e ∂N.clockedWalkExcursionKernel q B hB w,
        ClockedWalkExcursion.curve e ∈ curveOscillationLe (2 * r + s') :=
  fun B hB w _ _ _ hs hBpos hv hstep =>
    N.clockedWalkExcursionKernel_ae_curveOscillationLe_of_steps q B hB w hs hBpos hv hstep

/-- Almost surely every excursion of the walk skeleton of the selected-ball scheme of common
radius `ρ` has a curve of oscillation at most `2 ρ + s`, where `s` bounds the steps of the
walk before it leaves the buffered neighbourhood of the ball that contains its start; the
oscillation of a single clocked excursion is proved. -/
theorem ae_actualWalkExcursionSequence_curveOscillationLe
    (H : CellConfig) (hH : H.IsCellConfiguration)
    (hsymm : ∀ v w : H.cells, H.c v w = H.c w v) (hnonneg : ∀ v w : H.cells, 0 ≤ H.c v w)
    (hloop : ∀ v : H.cells, H.c v v = 0)
    (rep : H.cells → Plane) (hrep : ∀ K, rep K ∈ (K.1 : Set Plane))
    (V : Set H.cells) [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (N : FiniteConductanceNetwork V)
    (hN : N = finiteConductanceRestriction (fun v w : H.cells => H.c v w) hsymm hnonneg hloop V)
    {J : Type u} [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (q : V → BouRabeeGwynne.Euc 2) (hinj : Function.Injective q)
    (center : J → BouRabeeGwynne.Euc 2) (rad : J → ℝ) {ρ : ℝ} (hrad : ∀ j, rad j = ρ)
    (hρ : 0 ≤ ρ)
    (select : ℕ → BouRabeeGwynne.Euc 2 → Option J) (hs : ∀ n, Measurable (select n))
    (hselect : ∀ n x j, select n x = some j → x ∈ ball (center j) (rad j))
    (A : Set V) (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (hballA : ∀ j, q ⁻¹' ball (center j) (rad j) ⊆ A)
    (φ : Plane → BouRabeeGwynne.Euc 2) (hφ : Isometry φ) (Wm : Set Plane)
    (a δ α s : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hα : 0 ≤ α) (hs0 : 2 * (a * δ) + 2 * α ≤ s)
    (hbuffer : ∀ x ∈ φ ⁻¹' (⋃ j, ball (center j) (ρ + α)), Metric.closedBall x (a * δ) ⊆ Wm)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane), a • z ∈ Wm) →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    (hq : ∀ x : V, dist (φ (a • rep x.1)) (q x) ≤ α)
    (v : V) (initial : J) (hinit : select 0 (q v) = some initial) :
    ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ i,
      ClockedWalkExcursion.curve (actualWalkExcursionSequence q
        (fun j => q ⁻¹' ball (center j) (rad j)) initial select ω i).2 ∈
        curveOscillationLe (2 * ρ + s) := by
  exact ae_actualWalkExcursionSequence_curveOscillationLe_of_clocked H hH hsymm hnonneg hloop rep
    hrep V N hN q hinj center rad hrad hρ select hs hselect A hA haccess hballA φ hφ Wm a δ α s
    ha hδ hα hs0 hbuffer hmesh hq (clockedWalkExcursion_oscillation_of_steps N q) v initial hinit

end MatedCRT
end

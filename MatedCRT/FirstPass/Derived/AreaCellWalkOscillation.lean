import LatticeProb.Walk.RestrictedCellLocalPreExitMesh
import LatticeProb.Bonanno.BouRabeeGwynne.SelectedExcursionOscillation

/-! # Oscillation of the excursions of the walk skeleton on a finite cell network

For the walk on a finite restriction of a cell configuration, the selected-ball scheme of
covering balls of a common radius `ρ` yields excursions whose curves have oscillation at
most `2 ρ + s`, as soon as the walk makes steps of length at most `s` before leaving the
ball that contains its start.  The bound on the pre-exit steps comes from the local mesh
of the cells that meet the buffered neighbourhood of the balls, and from the
`a`-closeness of the position map `q` to the cell representatives.

The oscillation of one clocked excursion with bounded pre-exit steps is an hypothesis
`hclock` of the final theorem; it is the statement of the general bound for finite
conductance networks. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace MatedCRT
open Set Metric MeasureTheory BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork
  ReflectedGMS ReflectedGMS.GMS LatticeProb LatticeProb.CellConfigInterpolation
open scoped unitInterval ENNReal NNReal
universe u

/-- Paths that stay in a smaller set before time `n` stay in the larger set. -/
theorem lt_exitTime_of_subset {V : Type*} {A S : Set V} (h : A ⊆ S) {ω : ℕ → V} {n : ℕ}
    (hn : (n : WithTop ℕ) < exitTime A ω) : (n : WithTop ℕ) < exitTime S ω := by
  by_contra hcon
  obtain ⟨k, hk, hkS⟩ := (exitTime_le_iff S ω n).mp (not_lt.mp hcon)
  have hk' : (k : WithTop ℕ) < exitTime A ω :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr hk) hn
  exact hkS (h (mem_of_lt_exitTime hk'))

/-- Before leaving a set `B` contained in the preimage of the open region `U₁`, the walk on a
finite restriction of a cell configuration makes steps of `q`-length at most
`2 (a δ) + 2 α`, where `δ` bounds the diameters of the cells meeting the buffered region and
`q` is `α`-close to `φ (a • rep)`. -/
theorem ae_preExit_step_le_of_subset_preimage
    (H : CellConfig) (hH : H.IsCellConfiguration)
    (hsymm : ∀ v w : H.cells, H.c v w = H.c w v) (hnonneg : ∀ v w : H.cells, 0 ≤ H.c v w)
    (hloop : ∀ v : H.cells, H.c v v = 0)
    (rep : H.cells → Plane) (hrep : ∀ K, rep K ∈ (K.1 : Set Plane))
    (V : Set H.cells) [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (N : FiniteConductanceNetwork V)
    (hN : N = finiteConductanceRestriction (fun v w : H.cells => H.c v w) hsymm hnonneg hloop V)
    (B : Set V) (hB : ∀ v ∈ B, 0 < N.totalConductance v) (v : V)
    (φ : Plane → BouRabeeGwynne.Euc 2) (hφ : Isometry φ) (U₁ : Set (BouRabeeGwynne.Euc 2))
    (Wm : Set Plane) (a δ α : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hbuffer : ∀ x ∈ φ ⁻¹' U₁, Metric.closedBall x (a * δ) ⊆ Wm)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane), a • z ∈ Wm) →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    (hBU : ∀ w ∈ B, φ (a • rep w.1) ∈ U₁)
    (q : V → BouRabeeGwynne.Euc 2) (hq : ∀ x : V, dist (φ (a • rep x.1)) (q x) ≤ α) :
    ∀ᵐ ω ∂N.trajectoryLaw B hB v, ∀ j : ℕ, (j : WithTop ℕ) < exitTime B ω →
      dist (q (ω (j + 1))) (q (ω j)) ≤ 2 * (a * δ) + 2 * α := by
  subst hN
  have hmain := finiteRestriction_trajectoryLaw_ae_preExit_step_le_local_mesh H hH hsymm hnonneg
    hloop rep hrep V B hB v φ hφ U₁ Wm a δ ha hδ hbuffer hmesh
  filter_upwards [hmain] with ω hω j hj
  have hj' := hω j (lt_exitTime_of_subset (fun w hw => (hBU w hw :
    w ∈ (fun x : V => φ (a • rep x.1)) ⁻¹' U₁)) hj)
  have t1 := dist_triangle (q (ω (j + 1))) (φ (a • rep (ω (j + 1)).1)) (q (ω j))
  have t2 := dist_triangle (φ (a • rep (ω (j + 1)).1)) (φ (a • rep (ω j).1)) (q (ω j))
  have h1 := hq (ω (j + 1))
  rw [dist_comm] at h1
  have h0 := hq (ω j)
  linarith

/-- Almost surely every excursion of the walk skeleton of the selected-ball scheme of common
radius `ρ` has a curve of oscillation at most `2 ρ + s`, where `s` bounds the steps of the
walk before it leaves the buffered neighbourhood of the ball that contains its start.  The
oscillation of a single clocked excursion with bounded pre-exit steps is the hypothesis
`hclock`; every other ingredient is proved here. -/
theorem ae_actualWalkExcursionSequence_curveOscillationLe_of_clocked
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
    (hclock : ∀ (B : Set V) (hB : ∀ w ∈ B, 0 < N.totalConductance w) (w : V)
      (c : BouRabeeGwynne.Euc 2) (r s' : ℝ), 0 ≤ s' → (∀ x ∈ B, q x ∈ ball c r) → q w ∈ ball c r →
      (∀ᵐ ω ∂N.trajectoryLaw B hB w, ∀ j : ℕ, (j : WithTop ℕ) < exitTime B ω →
        dist (q (ω (j + 1))) (q (ω j)) ≤ s') →
      ∀ᵐ e ∂N.clockedWalkExcursionKernel q B hB w,
        ClockedWalkExcursion.curve e ∈ curveOscillationLe (2 * r + s'))
    (v : V) (initial : J) (hinit : select 0 (q v) = some initial) :
    ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ i,
      ClockedWalkExcursion.curve (actualWalkExcursionSequence q
        (fun j => q ⁻¹' ball (center j) (rad j)) initial select ω i).2 ∈
        curveOscillationLe (2 * ρ + s) := by
  have hs_nonneg : 0 ≤ s := le_trans (by positivity) hs0
  have hB : ∀ j v, v ∈ q ⁻¹' ball (center j) (rad j) → 0 < N.totalConductance v :=
    fun j v hv => hA v (hballA j hv)
  have hselV : ∀ n v j, select n (q v) = some j → v ∈ q ⁻¹' ball (center j) (rad j) :=
    fun n v j h => hselect n (q v) j h
  refine N.trajectoryLaw_walkSkeleton_ae_oscillation q hinj
    (fun j => q ⁻¹' ball (center j) (rad j)) hB select hs hballA hA haccess
    (R := 2 * ρ + s) (by positivity) ?_ hselV initial v (hselV 0 v initial hinit)
  intro j w hw
  have hBU : ∀ x ∈ q ⁻¹' ball (center j) (rad j),
      φ (a • rep x.1) ∈ ⋃ j, ball (center j) (ρ + α) := by
    intro x hx
    refine mem_iUnion.2 ⟨j, mem_ball.2 ?_⟩
    have h1 : dist (q x) (center j) < rad j := mem_ball.1 hx
    have h2 := dist_triangle (φ (a • rep x.1)) (q x) (center j)
    have h3 := hq x
    rw [hrad j] at h1
    linarith
  have hstep := ae_preExit_step_le_of_subset_preimage H hH hsymm hnonneg hloop rep hrep V N hN
    (q ⁻¹' ball (center j) (rad j)) (hB j) w φ hφ (⋃ j, ball (center j) (ρ + α)) Wm a δ α ha hδ
    hbuffer hmesh hBU q hq
  have hres := hclock _ (hB j) w (center j) (rad j) s hs_nonneg (fun x hx => hx) hw
    (by filter_upwards [hstep] with ω hω j' hj' using (hω j' hj').trans hs0)
  have e : 2 * rad j + s = 2 * ρ + s := by rw [hrad j]
  rw [e] at hres
  exact hres

end MatedCRT

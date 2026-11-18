import MatedCRT.FirstPass.Derived.AreaCellNestedBallContainment

/-! # Shifted area-cell networks for ball selectors -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 LatticeProb
open scoped NNReal Topology

/-- On one common tail, the finite restrictions have positive conductance on
    the representative ambient set and contain both ball preimages there. -/
theorem MatedCRTEnv.exists_areaCell_shifted_selector_networks
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlf : ∀ n, IsLocallyFiniteMult (S.mult (ε n) ω))
    (hlfg : ∀ n, MatedCRTHarmonic.MatedCRT.IsLocallyFinite (ε n) (S.bm ω))
    (H : ∀ n, CellularEmbedding
      (MatedCRTHarmonic.MatedCRT.graph (ε n) (S.bm ω) (hlfg n)) (0 : ℤ))
    (hH : ∀ n, (H n).cell = cell (ε n) (S.η ω))
    {a : ℝ≥0} (ha : 0 < a) {U W : Set Plane} (hUW : U ⊆ W)
    (hW : Bornology.IsBounded W)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Filter.Tendsto t Filter.atTop (𝓝 0))
    {X J : Type*} [MetricSpace X] [ProperSpace X] [Fintype J] (φ : Plane → X) (hφ : Isometry φ)
    (center : J → X) (radius : J → ℝ) {O : Set X}
    (hO : IsOpen O) (hKO : ∀ j, Metric.closedBall (center j) (radius j) ⊆ O)
    (hOW : φ ⁻¹' O ⊆ W) :
    ∃ (R : ∀ n, Set (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells)
      (hR : ∀ n, (R n).Finite) (q : ∀ n, R n → Plane) (N : ℕ),
      (∀ n, Function.Injective (fun v : R (n + N) => φ (q (n + N) v))) ∧
      (∀ n (v : R (n + N)), ∃ x ∈ (v.1.1 : Set Plane), q (n + N) v = (a : ℝ) • x) ∧
      (∀ n, letI := (hR (n + N)).fintype
       let A : Set (R (n + N)) := {v | (a : ℝ) •
         areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v ∈ W}
       let net := finiteConductanceRestriction
          (fun v w : (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).cells =>
            (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).c v w)
          (areaCellConfig_conductance_symm h (hε (n + N)) (S.mult (ε (n + N)) ω)
            (S.mult_symm (ε (n + N)) ω))
          (areaCellConfig_conductance_nonneg h (hε (n + N)) (S.mult (ε (n + N)) ω))
          (areaCellConfig_conductance_self h (hε (n + N)) (S.mult (ε (n + N)) ω)
            (S.mult_self (ε (n + N)) ω)) (R (n + N))
       (∀ v ∈ A, 0 < net.totalConductance v) ∧ net.BoundaryAccessible A ∧
       (∀ j, (fun v : R (n + N) => φ ((a : ℝ) •
           areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v)) ⁻¹'
             Metric.ball (center j) (radius j) ⊆ A) ∧
       (∀ j, (fun v : R (n + N) => φ (q (n + N) v)) ⁻¹'
             Metric.ball (center j) (radius j) ⊆ A)) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop, ∀ v : R (n + N),
        dist (φ ((a : ℝ) • areaCellRepresentative h (hε (n + N))
          (S.mult (ε (n + N)) ω) v)) (φ (q (n + N) v)) < δ) ∧
      (∀ P : ℕ → Prop, (∀ᶠ n in Filter.atTop, P n) →
        ∀ᶠ n in Filter.atTop, P (n + N)) ∧
      (∀ n (v : (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).cells),
        (a : ℝ) • areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v ∈ W →
        ∀ w, w ∉ R (n + N) →
          (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).c v w = 0) := by
  obtain ⟨R, hR, q, hqi, hqc, _, _, _, _, hr, hp, _, N, hball, hclose, hshift⟩ :=
    S.exists_areaCell_nested_ball_containment ω h ε hε hlf hlfg H hH ha hUW hW
      t ht ht0 φ hφ center radius hO hKO hOW
  refine ⟨R, hR, q, N, (fun n => hqi (n + N)), (fun n => hqc (n + N)), ?_, hclose, hshift,
    fun n v hv w hw => hr (n + N) v hv w hw⟩
  intro n
  exact ⟨(hp (n + N)).2.1, (hp (n + N)).2.2.2,
    (fun j v hv => (hball n j v).1 hv), (fun j v hv => (hball n j v).2 hv)⟩

end MatedCRT
end

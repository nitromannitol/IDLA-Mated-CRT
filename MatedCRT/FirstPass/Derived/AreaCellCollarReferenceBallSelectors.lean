import MatedCRT.FirstPass.Derived.AreaCellNestedBallContainment
import LatticeProb.Walk.CollarReferenceBallSelectors

/-! # Collar selectors on area-cell network sequences -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open Set Metric MeasureTheory Filter BouRabeeGwynne ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 LatticeProb
open BouRabeeGwynne.FiniteConductanceNetwork
open scoped ENNReal NNReal Topology

/-- Reference and oscillation estimates on one area-cell network sequence
provide the collar selectors on that same sequence. -/
theorem MatedCRTEnv.exists_areaCell_collar_reference_ball_selectors
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    {d : ℕ} (hd : 1 ≤ d) {J : Type*} [Fintype J] (center : J → Euc d)
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U I K : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j)) (hI : ∀ j, IsCompact (I j))
    (hIU : ∀ j, I j ⊆ U j)
    (ρ : Measure (BrownianPath d)) (hρ : IsStandardBrownianLaw ρ)
    (hK : ∀ j, IsCompact (K j)) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (hcollar : ∀ j x, x ∈ I j → ∀ y, dist y x < r j → y ∈ K j)
    (R : J → ℝ)
    (Rset : ∀ n, Set (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells)
    [∀ n, Fintype (Rset n)] [∀ n, MeasurableSpace (Rset n)]
    [∀ n, MeasurableSingletonClass (Rset n)]
    (N : ∀ n, FiniteConductanceNetwork (Rset n))
    (_hN : ∀ n, N n = finiteConductanceRestriction
      (fun v w : (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells =>
        (areaCellConfig h (hε n) (S.mult (ε n) ω)).c v w)
      (areaCellConfig_conductance_symm h (hε n) (S.mult (ε n) ω) (S.mult_symm (ε n) ω))
      (areaCellConfig_conductance_nonneg h (hε n) (S.mult (ε n) ω))
      (areaCellConfig_conductance_self h (hε n) (S.mult (ε n) ω) (S.mult_self (ε n) ω))
      (Rset n))
    (p q : ∀ n, Rset n → Euc d) (hp : ∀ n, Measurable (p n))
    (φ : Plane → Euc d) (scale : ℝ≥0) (q₀ : ∀ n, Rset n → Plane)
    (_hpdef : ∀ n v, p n v = φ ((scale : ℝ) •
      areaCellRepresentative h (hε n) (S.mult (ε n) ω) v))
    (_hqdef : ∀ n v, q n v = φ (q₀ n v))
    (W : Set Plane) (A : ∀ n, Set (Rset n))
    (hAdef : ∀ n, A n = {v : Rset n | (scale : ℝ) •
      areaCellRepresentative h (hε n) (S.mult (ε n) ω) v ∈ W})
    (hA : ∀ n v, v ∈ A n → 0 < (N n).totalConductance v)
    (hball : ∀ n j (v : Rset n),
      (p n v ∈ ball (center j) (R j) →
        (scale : ℝ) • areaCellRepresentative h (hε n) (S.mult (ε n) ω) v ∈ W) ∧
      (q n v ∈ ball (center j) (R j) →
        (scale : ℝ) • areaCellRepresentative h (hε n) (S.mult (ε n) ω) v ∈ W))
    (ν : ∀ j, K j → ProbabilityMeasure (Euc d)) (hν : ∀ j, Continuous (ν j))
    (hνlaw : ∀ j z, (ν j z : Measure (Euc d)) =
      (stoppedBrownianLaw (U j) z.1 ρ).map BouRabeeGwynne.CurveSpace.endPoint)
    (hclose : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ v, dist (p n v) (q n v) < δ)
    (href : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : Rset n,
      ∀ hv : p n v ∈ K j,
      levyProkhorovDist
        (((N n).discreteHarmonicMeasure (p n ⁻¹' ball (center j) (R j))
          (fun w hw => hA n w ((by rw [hAdef n]; exact (hball n j w).1 hw))) v).map (p n))
        (ν j ⟨p n v, hv⟩ : Measure (Euc d)) < ε)
    (hosc : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : Rset n,
      q n v ∈ I j → ∃ (δ η : ℝ) (E : Set (ℕ → Rset n)),
        (∀ w, dist (p n w) (q n w) ≤ δ) ∧ η + δ < ε / 4 ∧
        (N n).trajectoryLaw (A n) (hA n) v E ≤ (ENNReal.ofReal (ε / 4)) ∧
        (∀ᵐ ω ∂(N n).trajectoryLaw (A n) (hA n) v, ω ∉ E →
          exitTime (p n ⁻¹' ball (center j) (R j + δ)) ω ≠ ⊤ ∧
          ∀ i ∈ Icc ((exitTime (p n ⁻¹' ball (center j) (R j - δ)) ω).untopD 0)
              ((exitTime (p n ⁻¹' ball (center j) (R j + δ)) ω).untopD 0),
            ∀ k ∈ Icc ((exitTime (p n ⁻¹' ball (center j) (R j - δ)) ω).untopD 0)
                ((exitTime (p n ⁻¹' ball (center j) (R j + δ)) ω).untopD 0),
              dist (p n (ω i)) (p n (ω k)) ≤ η))
    (C D : Set (Euc d)) (hC : IsCompact C) (hDC : D ⊆ C)
    (s : ℝ) (hs : 0 < s)
    (hcover : ∀ x ∈ D, ∃ j : J, x ∈ ball (center j) (s / 4))
    (hinner : ∀ j : J, ball (center j) (s / 2) ⊆ I j)
    (hR : ∀ j : J, s ≤ R j)
    (hUball : ∀ j : J, U j = ball (center j) (R j))
    (hIball : ∀ j : J, I j ⊆ ball (center j) (R j))
    (hballC : ∀ j : J, closure (ball (center j) (R j)) ⊆ C)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (L : ℕ) :
    ∃ (m : Fin (L + 1) → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
      (δ : Fin (L + 1) → ℝ) (choice : ∀ i, Fin (m i) → Option J),
      (∀ i, 0 < δ i) ∧
      (∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l))) ∧
      (∀ i, C ⊆ ⋃ k, E i k) ∧
      (∀ i k, MeasurableSet (E i k)) ∧
      (∀ i k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a) ∧
      (∀ i k j, choice i k = some j → E i k ⊆ I j) ∧
      (∀ i k j, choice i k = some j → E i k ⊆ ball (center j) (R j)) ∧
      (∀ i j, closure (ball (center j) (R j)) ⊆ ⋃ k, E i k) ∧
      (∀ i, Measurable (cellSelector (E i) (choice i))) ∧
      (∀ i x, x ∈ D → cellSelector (E i) (choice i) x ≠ none) ∧
      (∀ i x j, cellSelector (E i) (choice i) x = some j →
        ball x (s / 2) ⊆ ball (center j) (R j)) ∧
      ∀ᶠ n in atTop, ∀ (initial : J) (v₀ : Rset n) (z : Euc d),
        q n v₀ ∈ I initial → z ∈ I initial →
        dist (q n v₀) z ≤ δ ⟨0, Nat.zero_lt_succ L⟩ →
        let ix : ℕ → Fin (L + 1) := fun t => ⟨min t L, Nat.lt_succ_of_le (min_le_right _ _)⟩
        let m' : ℕ → ℕ := fun t => m (ix t)
        let E' : ∀ t, Fin (m' t) → Set (Euc d) := fun t => E (ix t)
        let choice' : ∀ t, Fin (m' t) → Option J := fun t => choice (ix t)
        (∀ t < L, ∀ k j, choice' t k = some j →
          ∀ v : Rset n, q n v ∈ E' t k → ∀ y ∈ E' t k, ∀ l,
            |(((N n).discreteHarmonicMeasure (q n ⁻¹' ball (center j) (R j)) (fun w hw => hA n w ((by rw [hAdef n]; exact (hball n j w).2 hw))) v).map (q n) (E' (t + 1) l)).toReal -
              (((stoppedBrownianLaw (ball (center j) (R j)) y ρ).map BouRabeeGwynne.CurveSpace.endPoint) (E' (t + 1) l)).toReal| ≤
                b / (m' (t + 1) + 1)) ∧
        (∀ k, |(((N n).discreteHarmonicMeasure (q n ⁻¹' ball (center initial) (R initial)) (fun w hw => hA n w ((by rw [hAdef n]; exact (hball n initial w).2 hw))) v₀).map (q n)
            (E' 0 k)).toReal -
          (((stoppedBrownianLaw (ball (center initial) (R initial)) z ρ).map BouRabeeGwynne.CurveSpace.endPoint) (E' 0 k)).toReal| ≤
            b / (m' 0 + 1)) := by
  have hpA : ∀ n j, p n ⁻¹' ball (center j) (R j) ⊆ A n := by
    intro n j v hv
    rw [hAdef n]
    exact (hball n j v).1 hv
  have hqA : ∀ n j, q n ⁻¹' ball (center j) (R j) ⊆ A n := by
    intro n j v hv
    rw [hAdef n]
    exact (hball n j v).2 hv
  exact exists_collar_reference_ball_selectors hd center U I K hU hUb hI hIU
    ρ hρ hK r hr hcollar R (fun n => Rset n) N p q hp A hA hpA hqA
    ν hν hνlaw hclose href hosc C D hC hDC s hs hcover hinner hR hUball
    hIball hballC a b ha hb L

end MatedCRT
end

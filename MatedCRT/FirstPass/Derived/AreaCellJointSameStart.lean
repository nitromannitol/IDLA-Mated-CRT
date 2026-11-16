import MatedCRT.FirstPass.Derived.AreaCellShiftedCollarSelectorGeometry

/-! # Same-start endpoint estimates on finite area-cell networks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open Set Metric MeasureTheory Filter BouRabeeGwynne ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 LatticeProb
open BouRabeeGwynne.FiniteConductanceNetwork

/-- For a selected initial vertex, the joint endpoint estimates apply with the
Brownian starting point equal to the embedded vertex. -/
theorem MatedCRTEnv.areaCell_joint_endpoint_estimates_same_start
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (R : ∀ n, Set (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells)
    [∀ n, Fintype (R n)] [∀ n, MeasurableSpace (R n)]
    [∀ n, MeasurableSingletonClass (R n)]
    (net : ∀ n, FiniteConductanceNetwork (R n))
    (_hnet : ∀ n, net n = finiteConductanceRestriction
      (fun v w : (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells =>
        (areaCellConfig h (hε n) (S.mult (ε n) ω)).c v w)
      (areaCellConfig_conductance_symm h (hε n) (S.mult (ε n) ω)
        (S.mult_symm (ε n) ω))
      (areaCellConfig_conductance_nonneg h (hε n) (S.mult (ε n) ω))
      (areaCellConfig_conductance_self h (hε n) (S.mult (ε n) ω)
        (S.mult_self (ε n) ω)) (R n))
    {d : ℕ} {J : Type*} [MeasurableSpace (Option J)]
    (q : ∀ n, R n → Euc d) (A : ∀ n, Set (R n))
    (hA : ∀ n v, v ∈ A n → 0 < (net n).totalConductance v)
    (center : J → Euc d) (rad : J → ℝ)
    (hball : ∀ n j (v : R n), q n v ∈ ball (center j) (rad j) → v ∈ A n)
    (I : J → Set (Euc d)) (D : Set (Euc d))
    (m : ℕ → ℕ) (E : ∀ t, Fin (m t) → Set (Euc d))
    (choice : ∀ t, Fin (m t) → Option J)
    (hactive : ∀ x ∈ D, cellSelector (E 0) (choice 0) x ≠ none)
    (hinner : ∀ k j, choice 0 k = some j → E 0 k ⊆ I j)
    (ρ : Measure (BrownianPath d)) (δ b : ℝ) (hδ : 0 ≤ δ) (L : ℕ)
    (hjoint : ∀ᶠ n in atTop, ∀ j (v : R n) z,
      q n v ∈ I j → z ∈ I j → dist (q n v) z ≤ δ →
      (∀ t < L, ∀ k l, choice t k = some l →
        ∀ w : R n, q n w ∈ E t k → ∀ y ∈ E t k, ∀ r,
          |(((net n).discreteHarmonicMeasure (q n ⁻¹' ball (center l) (rad l))
              (fun u hu => hA n u (hball n l u hu)) w).map (q n) (E (t + 1) r)).toReal -
            (((stoppedBrownianLaw (ball (center l) (rad l)) y ρ).map
              BouRabeeGwynne.CurveSpace.endPoint) (E (t + 1) r)).toReal| ≤
              b / (m (t + 1) + 1)) ∧
      (∀ k, |(((net n).discreteHarmonicMeasure (q n ⁻¹' ball (center j) (rad j))
          (fun u hu => hA n u (hball n j u hu)) v).map (q n) (E 0 k)).toReal -
        (((stoppedBrownianLaw (ball (center j) (rad j)) z ρ).map
          BouRabeeGwynne.CurveSpace.endPoint) (E 0 k)).toReal| ≤ b / (m 0 + 1))) :
    ∀ᶠ n in atTop, ∀ v : R n, q n v ∈ D →
      ∃ j, cellSelector (E 0) (choice 0) (q n v) = some j ∧ q n v ∈ I j ∧
      (∀ t < L, ∀ k l, choice t k = some l →
        ∀ w : R n, q n w ∈ E t k → ∀ y ∈ E t k, ∀ r,
          |(((net n).discreteHarmonicMeasure (q n ⁻¹' ball (center l) (rad l))
              (fun u hu => hA n u (hball n l u hu)) w).map (q n) (E (t + 1) r)).toReal -
            (((stoppedBrownianLaw (ball (center l) (rad l)) y ρ).map
              BouRabeeGwynne.CurveSpace.endPoint) (E (t + 1) r)).toReal| ≤
              b / (m (t + 1) + 1)) ∧
      (∀ k, |(((net n).discreteHarmonicMeasure (q n ⁻¹' ball (center j) (rad j))
          (fun u hu => hA n u (hball n j u hu)) v).map (q n) (E 0 k)).toReal -
        (((stoppedBrownianLaw (ball (center j) (rad j)) (q n v) ρ).map
          BouRabeeGwynne.CurveSpace.endPoint) (E 0 k)).toReal| ≤ b / (m 0 + 1)) := by
  filter_upwards [hjoint] with n hn
  intro v hv
  cases hs : cellSelector (E 0) (choice 0) (q n v) with
  | none => exact False.elim (hactive (q n v) hv hs)
  | some j =>
    obtain ⟨k, hk, hc⟩ := cellSelector_some_mem (E 0) (choice 0) hs
    have hq : q n v ∈ I j := hinner k j hc hk
    exact ⟨j, rfl, hq, hn j v (q n v) hq hq (by simpa using hδ)⟩

end MatedCRT
end

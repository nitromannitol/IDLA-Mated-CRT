import MatedCRT.FirstPass.Derived.AreaCellJointSameStart
import LatticeProb.Prob.FiniteHorizonSelectorExtension

/-! # Finite-horizon selectors for area-cell endpoint estimates -/

set_option autoImplicit false
noncomputable section
namespace MatedCRT
open Set Metric MeasureTheory Filter BouRabeeGwynne ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 LatticeProb
open BouRabeeGwynne.FiniteConductanceNetwork

/-- The finite selector geometry and the joint same-start estimates use the same
area-cell network and the same selector family extended to all times. -/
theorem MatedCRTEnv.areaCell_finite_horizon_joint_same_start
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
    (L : ℕ) (mf : Fin (L + 1) → ℕ)
    (Ef : ∀ i, Fin (mf i) → Set (Euc d))
    (cf : ∀ i, Fin (mf i) → Option J)
    (T : Set (Euc d)) (s a : ℝ)
    (hdisj : ∀ i, Pairwise (fun k l => Disjoint (Ef i k) (Ef i l)))
    (hmeas : ∀ i k, MeasurableSet (Ef i k))
    (hdiam : ∀ i k, ∀ x ∈ Ef i k, ∀ y ∈ Ef i k, dist x y ≤ a)
    (hinner : ∀ i k j, cf i k = some j → Ef i k ⊆ I j)
    (hinside : ∀ i k j, cf i k = some j → Ef i k ⊆ ball (center j) (rad j))
    (hcover : ∀ i j, closure (ball (center j) (rad j)) ⊆ ⋃ k, Ef i k)
    (hselect : ∀ i, Measurable (cellSelector (Ef i) (cf i)))
    (hactive : ∀ i x, x ∈ D → cellSelector (Ef i) (cf i) x ≠ none)
    (hmargin : ∀ i x j, cellSelector (Ef i) (cf i) x = some j →
      ball x (s / 2) ⊆ ball (center j) (rad j))
    (hTD : T ⊆ D) (ρ : Measure (BrownianPath d)) (δ b : ℝ) (hδ : 0 ≤ δ)
    (hjoint :
      let ix : ℕ → Fin (L + 1) := fun t => ⟨min t L, Nat.lt_succ_of_le (min_le_right _ _)⟩
      let m := fun t => mf (ix t)
      let E := fun t => Ef (ix t)
      let choice := fun t => cf (ix t)
      ∀ᶠ n in atTop, ∀ j (v : R n) z,
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
    let ix : ℕ → Fin (L + 1) := fun t => ⟨min t L, Nat.lt_succ_of_le (min_le_right _ _)⟩
    let m := fun t => mf (ix t)
    let E := fun t => Ef (ix t)
    let choice := fun t => cf (ix t)
    ((∀ t, Pairwise (fun k l => Disjoint (E t k) (E t l))) ∧
    (∀ t k, MeasurableSet (E t k)) ∧
    (∀ t k, ∀ x ∈ E t k, ∀ y ∈ E t k, dist x y ≤ a) ∧
    (∀ t k j, choice t k = some j → E t k ⊆ ball (center j) (rad j)) ∧
    (∀ t j, closure (ball (center j) (rad j)) ⊆ ⋃ k, E t k) ∧
    (∀ t, Measurable (cellSelector (E t) (choice t))) ∧
    (∀ t x j, cellSelector (E t) (choice t) x = some j →
      ball x (s / 2) ⊆ ball (center j) (rad j)) ∧
    (∀ t x, cellSelector (E t) (choice t) x = none → x ∉ T)) ∧
    (∀ᶠ n in atTop, ∀ v : R n, q n v ∈ D →
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
          BouRabeeGwynne.CurveSpace.endPoint) (E 0 k)).toReal| ≤ b / (m 0 + 1))) := by
  refine ⟨finite_horizon_cell_selectors_extend L mf Ef cf
    (fun j => ball (center j) (rad j)) D T s a hdisj hmeas hdiam hinside
    hcover hselect hactive hmargin hTD, ?_⟩
  exact S.areaCell_joint_endpoint_estimates_same_start ω h ε hε R net _hnet q A hA
    center rad hball I D _ _ _ (hactive _) (hinner _) ρ δ b hδ L hjoint

end MatedCRT
end

import MatedCRT.FirstPass.Derived.AreaCellShiftedSelectorNetworks
import MatedCRT.FirstPass.Derived.AreaCellCollarReferenceBallSelectors

/-! # Collar selectors on shifted area-cell networks -/
set_option autoImplicit false
noncomputable section
namespace MatedCRT
open Set Metric MeasureTheory Filter BouRabeeGwynne ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 LatticeProb
open BouRabeeGwynne.FiniteConductanceNetwork
open scoped ENNReal NNReal Topology

/-- The same shifted area-cell restrictions support the conditional collar selectors. -/
theorem MatedCRTEnv.exists_shifted_areaCell_collar_selectors
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlf : ∀ n, IsLocallyFiniteMult (S.mult (ε n) ω))
    (hlfg : ∀ n, MatedCRTHarmonic.MatedCRT.IsLocallyFinite (ε n) (S.bm ω))
    (H : ∀ n, CellularEmbedding
      (MatedCRTHarmonic.MatedCRT.graph (ε n) (S.bm ω) (hlfg n)) (0 : ℤ))
    (hH : ∀ n, (H n).cell = cell (ε n) (S.η ω))
    {scale : ℝ≥0} (hscale : 0 < scale) {U₀ W : Set Plane} (hUW : U₀ ⊆ W)
    (hW : Bornology.IsBounded W)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Filter.Tendsto t Filter.atTop (𝓝 0))
    {d : ℕ} (hd : 1 ≤ d) {J : Type*} [Fintype J] (φ : Plane → Euc d) (hφ : Isometry φ)
    (center : J → Euc d) (rad : J → ℝ) {O : Set (Euc d)}
    (hO : IsOpen O) (hKO : ∀ j, Metric.closedBall (center j) (rad j) ⊆ O)
    (hOW : φ ⁻¹' O ⊆ W)
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U I K : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j)) (hI : ∀ j, IsCompact (I j))
    (hIU : ∀ j, I j ⊆ U j)
    (ρ : Measure (BrownianPath d)) (hρ : IsStandardBrownianLaw ρ)
    (hK : ∀ j, IsCompact (K j)) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (hcollar : ∀ j x, x ∈ I j → ∀ y, dist y x < r j → y ∈ K j)
 :
    ∃ (R : ∀ n, Set (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells)
      (hR : ∀ n, (R n).Finite) (q : ∀ n, R n → Plane) (N : ℕ),
      (∀ n, Function.Injective (fun v : R (n + N) => φ (q (n + N) v))) ∧
      (∀ n (v : R (n + N)), ∃ x ∈ (v.1.1 : Set Plane), q (n + N) v = (scale : ℝ) • x) ∧
      (∀ n, letI := (hR (n + N)).fintype
       let A : Set (R (n + N)) := {v | (scale : ℝ) •
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
       (∀ j, (fun v : R (n + N) => φ ((scale : ℝ) •
           areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v)) ⁻¹'
             Metric.ball (center j) (rad j) ⊆ A) ∧
       (∀ j, (fun v : R (n + N) => φ (q (n + N) v)) ⁻¹'
             Metric.ball (center j) (rad j) ⊆ A)) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop, ∀ v : R (n + N),
        dist (φ ((scale : ℝ) • areaCellRepresentative h (hε (n + N))
          (S.mult (ε (n + N)) ω) v)) (φ (q (n + N) v)) < δ) ∧
      (∀ P : ℕ → Prop, (∀ᶠ n in Filter.atTop, P n) →
        ∀ᶠ n in Filter.atTop, P (n + N)) ∧
      (∀ n (v : (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).cells),
        (scale : ℝ) • areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v ∈ W →
        ∀ w, w ∉ R (n + N) →
          (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).c v w = 0) ∧
      (let Rset := fun n => R (n + N)
       let : ∀ n, Fintype (Rset n) := fun n => (hR (n + N)).fintype
       let : ∀ n, MeasurableSpace (Rset n) := fun _ => ⊤
       let : ∀ n, MeasurableSingletonClass (Rset n) := fun _ => ⟨fun _ => trivial⟩
       let net := fun n => finiteConductanceRestriction
          (fun v w : (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).cells =>
            (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).c v w)
          (areaCellConfig_conductance_symm h (hε (n + N)) (S.mult (ε (n + N)) ω)
            (S.mult_symm (ε (n + N)) ω))
          (areaCellConfig_conductance_nonneg h (hε (n + N)) (S.mult (ε (n + N)) ω))
          (areaCellConfig_conductance_self h (hε (n + N)) (S.mult (ε (n + N)) ω)
            (S.mult_self (ε (n + N)) ω)) (Rset n)
       let p := fun n (v : Rset n) => φ ((scale : ℝ) •
          areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v)
       let q' := fun n (v : Rset n) => φ (q (n + N) v)
       let A := fun n => {v : Rset n | (scale : ℝ) •
          areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v ∈ W}
       ∀ (hA : ∀ n v, v ∈ A n → 0 < (net n).totalConductance v)
         (hball : ∀ n j (v : Rset n),
           (p n v ∈ ball (center j) (rad j) → v ∈ A n) ∧
           (q' n v ∈ ball (center j) (rad j) → v ∈ A n))
         (ν : ∀ j, K j → ProbabilityMeasure (Euc d)) (_hν : ∀ j, Continuous (ν j))
    (_hνlaw : ∀ j z, (ν j z : Measure (Euc d)) =
      (stoppedBrownianLaw (U j) z.1 ρ).map BouRabeeGwynne.CurveSpace.endPoint)
    (_href : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : Rset n,
      ∀ hv : p n v ∈ K j,
      levyProkhorovDist
        (((net n).discreteHarmonicMeasure (p n ⁻¹' ball (center j) (rad j))
          (fun w hw => hA n w ((hball n j w).1 hw)) v).map (p n))
        (ν j ⟨p n v, hv⟩ : Measure (Euc d)) < ε)
    (_hosc : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : Rset n,
      q' n v ∈ I j → ∃ (δ η : ℝ) (E : Set (ℕ → Rset n)),
        (∀ w, dist (p n w) (q' n w) ≤ δ) ∧ η + δ < ε / 4 ∧
        (net n).trajectoryLaw (A n) (hA n) v E ≤ (ENNReal.ofReal (ε / 4)) ∧
        (∀ᵐ ω ∂(net n).trajectoryLaw (A n) (hA n) v, ω ∉ E →
          exitTime (p n ⁻¹' ball (center j) (rad j + δ)) ω ≠ ⊤ ∧
          ∀ i ∈ Icc ((exitTime (p n ⁻¹' ball (center j) (rad j - δ)) ω).untopD 0)
              ((exitTime (p n ⁻¹' ball (center j) (rad j + δ)) ω).untopD 0),
            ∀ k ∈ Icc ((exitTime (p n ⁻¹' ball (center j) (rad j - δ)) ω).untopD 0)
                ((exitTime (p n ⁻¹' ball (center j) (rad j + δ)) ω).untopD 0),
              dist (p n (ω i)) (p n (ω k)) ≤ η))
    (C D : Set (Euc d)) (_hC : IsCompact C) (_hDC : D ⊆ C)
    (s : ℝ) (_hs : 0 < s)
    (_hcover : ∀ x ∈ D, ∃ j : J, x ∈ ball (center j) (s / 4))
    (_hinner : ∀ j : J, ball (center j) (s / 2) ⊆ I j)
    (_hR : ∀ j : J, s ≤ rad j)
    (_hUball : ∀ j : J, U j = ball (center j) (rad j))
    (_hIball : ∀ j : J, I j ⊆ ball (center j) (rad j))
    (_hballC : ∀ j : J, closure (ball (center j) (rad j)) ⊆ C)
    (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b) (L : ℕ),
    ∃ (m : Fin (L + 1) → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
      (δ : Fin (L + 1) → ℝ) (choice : ∀ i, Fin (m i) → Option J),
      (∀ i, 0 < δ i) ∧
      (∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l))) ∧
      (∀ i, C ⊆ ⋃ k, E i k) ∧
      (∀ i k, MeasurableSet (E i k)) ∧
      (∀ i k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a) ∧
      (∀ i k j, choice i k = some j → E i k ⊆ I j) ∧
      (∀ i k j, choice i k = some j → E i k ⊆ ball (center j) (rad j)) ∧
      (∀ i j, closure (ball (center j) (rad j)) ⊆ ⋃ k, E i k) ∧
      (∀ i, Measurable (cellSelector (E i) (choice i))) ∧
      (∀ i x, x ∈ D → cellSelector (E i) (choice i) x ≠ none) ∧
      (∀ i x j, cellSelector (E i) (choice i) x = some j →
        ball x (s / 2) ⊆ ball (center j) (rad j)) ∧
      ∀ᶠ n in atTop, ∀ (initial : J) (v₀ : Rset n) (z : Euc d),
        q' n v₀ ∈ I initial → z ∈ I initial →
        dist (q' n v₀) z ≤ δ ⟨0, Nat.zero_lt_succ L⟩ →
        let ix : ℕ → Fin (L + 1) := fun t => ⟨min t L, Nat.lt_succ_of_le (min_le_right _ _)⟩
        let m' : ℕ → ℕ := fun t => m (ix t)
        let E' : ∀ t, Fin (m' t) → Set (Euc d) := fun t => E (ix t)
        let choice' : ∀ t, Fin (m' t) → Option J := fun t => choice (ix t)
        (∀ t < L, ∀ k j, choice' t k = some j →
          ∀ v : Rset n, q' n v ∈ E' t k → ∀ y ∈ E' t k, ∀ l,
            |(((net n).discreteHarmonicMeasure (q' n ⁻¹' ball (center j) (rad j)) (fun w hw => hA n w ((hball n j w).2 hw)) v).map (q' n) (E' (t + 1) l)).toReal -
              (((stoppedBrownianLaw (ball (center j) (rad j)) y ρ).map BouRabeeGwynne.CurveSpace.endPoint) (E' (t + 1) l)).toReal| ≤
                b / (m' (t + 1) + 1)) ∧
        (∀ k, |(((net n).discreteHarmonicMeasure (q' n ⁻¹' ball (center initial) (rad initial)) (fun w hw => hA n w ((hball n initial w).2 hw)) v₀).map (q' n)
            (E' 0 k)).toReal -
          (((stoppedBrownianLaw (ball (center initial) (rad initial)) z ρ).map BouRabeeGwynne.CurveSpace.endPoint) (E' 0 k)).toReal| ≤
            b / (m' 0 + 1)) ) := by
  classical
  obtain ⟨R, hR, q, N, hqi, hqc, hgeom, hclose, hshift, hret⟩ :=
    S.exists_areaCell_shifted_selector_networks ω h ε hε hlf hlfg H hH hscale hUW hW
      t ht ht0 φ hφ center rad hO hKO hOW
  refine ⟨R, hR, q, N, hqi, hqc, hgeom, hclose, hshift, hret, ?_⟩
  let Rset := fun n => R (n + N)
  let : ∀ n, Fintype (Rset n) := fun n => (hR (n + N)).fintype
  let : ∀ n, MeasurableSpace (Rset n) := fun _ => ⊤
  let : ∀ n, MeasurableSingletonClass (Rset n) := fun _ => ⟨fun _ => trivial⟩
  let net := fun n => finiteConductanceRestriction
    (fun v w : (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).cells =>
      (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).c v w)
    (areaCellConfig_conductance_symm h (hε (n + N)) (S.mult (ε (n + N)) ω)
      (S.mult_symm (ε (n + N)) ω))
    (areaCellConfig_conductance_nonneg h (hε (n + N)) (S.mult (ε (n + N)) ω))
    (areaCellConfig_conductance_self h (hε (n + N)) (S.mult (ε (n + N)) ω)
      (S.mult_self (ε (n + N)) ω)) (Rset n)
  let p := fun n (v : Rset n) => φ ((scale : ℝ) •
    areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v)
  let q' := fun n (v : Rset n) => φ (q (n + N) v)
  let A := fun n => {v : Rset n | (scale : ℝ) •
    areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v ∈ W}
  dsimp only
  intro hA hball ν hν hνlaw href hosc C D hC hDC s hs hcover hinner hR' hUball
    hIball hballC a b ha hb L
  exact S.exists_areaCell_collar_reference_ball_selectors ω h (fun n => ε (n + N))
    (fun n => hε (n + N)) hd center U I K hU hUb hI hIU ρ hρ hK r hr hcollar rad
    Rset net (fun _ => rfl) p q' (fun _ _ _ => trivial) φ scale (fun n => q (n + N))
    (fun _ _ => rfl) (fun _ _ => rfl) W A (fun _ => rfl) hA hball ν hν hνlaw hclose
    href hosc C D hC hDC s hs hcover hinner hR' hUball hIball hballC a b ha hb L

end MatedCRT
end

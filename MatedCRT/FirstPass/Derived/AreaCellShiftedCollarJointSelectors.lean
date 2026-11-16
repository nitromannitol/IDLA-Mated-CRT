import MatedCRT.FirstPass.Derived.AreaCellShiftedCollarSelectorGeometry
import MatedCRT.FirstPass.Derived.AreaCellFiniteHorizonJointSameStart

/-! # Joint selector estimates on shifted area-cell networks -/
set_option autoImplicit false
noncomputable section
namespace MatedCRT
open Set Metric MeasureTheory Filter BouRabeeGwynne ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 LatticeProb
open BouRabeeGwynne.FiniteConductanceNetwork
open scoped ENNReal NNReal Topology

/-- The same shifted area-cell restriction supplies both the selector geometry and
joint same-start endpoint estimates at the supplied finite horizon. -/
theorem MatedCRTEnv.exists_shifted_areaCell_joint_selectors_of_geometry
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
       ∃ (hA : ∀ n v, v ∈ A n → 0 < (net n).totalConductance v)
         (hball : ∀ n j (v : Rset n),
           (p n v ∈ ball (center j) (rad j) → v ∈ A n) ∧
           (q' n v ∈ ball (center j) (rad j) → v ∈ A n)),
       ∀ (ν : ∀ j, K j → ProbabilityMeasure (Euc d)) (_hν : ∀ j, Continuous (ν j))
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
    (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b) (L : ℕ) (T : Set (Euc d)) (_hTD : T ⊆ D),
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
      (∀ᶠ n in atTop, ∀ (initial : J) (v₀ : Rset n) (z : Euc d),
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
            b / (m' 0 + 1)) ) ∧
    let ix : ℕ → Fin (L + 1) := fun t => ⟨min t L, Nat.lt_succ_of_le (min_le_right _ _)⟩
    let m := fun t => m (ix t)
    let E := fun t => E (ix t)
    let choice := fun t => choice (ix t)
    ((∀ t, Pairwise (fun k l => Disjoint (E t k) (E t l))) ∧
    (∀ t k, MeasurableSet (E t k)) ∧
    (∀ t k, ∀ x ∈ E t k, ∀ y ∈ E t k, dist x y ≤ a) ∧
    (∀ t k j, choice t k = some j → E t k ⊆ ball (center j) (rad j)) ∧
    (∀ t j, closure (ball (center j) (rad j)) ⊆ ⋃ k, E t k) ∧
    (∀ t, Measurable (cellSelector (E t) (choice t))) ∧
    (∀ t x j, cellSelector (E t) (choice t) x = some j →
      ball x (s / 2) ⊆ ball (center j) (rad j)) ∧
    (∀ t x, cellSelector (E t) (choice t) x = none → x ∉ T)) ∧
    (∀ᶠ n in atTop, ∀ v : Rset n, q' n v ∈ D →
      ∃ j, cellSelector (E 0) (choice 0) (q' n v) = some j ∧ q' n v ∈ I j ∧
      (∀ t < L, ∀ k l, choice t k = some l →
        ∀ w : Rset n, q' n w ∈ E t k → ∀ y ∈ E t k, ∀ r,
          |(((net n).discreteHarmonicMeasure (q' n ⁻¹' ball (center l) (rad l))
              (fun u hu => hA n u ((hball n l u).2 hu)) w).map (q' n) (E (t + 1) r)).toReal -
            (((stoppedBrownianLaw (ball (center l) (rad l)) y ρ).map
              BouRabeeGwynne.CurveSpace.endPoint) (E (t + 1) r)).toReal| ≤
              b / (m (t + 1) + 1)) ∧
      (∀ k, |(((net n).discreteHarmonicMeasure (q' n ⁻¹' ball (center j) (rad j))
          (fun u hu => hA n u ((hball n j u).2 hu)) v).map (q' n) (E 0 k)).toReal -
        (((stoppedBrownianLaw (ball (center j) (rad j)) (q' n v) ρ).map
          BouRabeeGwynne.CurveSpace.endPoint) (E 0 k)).toReal| ≤ b / (m 0 + 1)))) := by
  classical
  obtain ⟨R, hR, q, N, hqi, hqc, hgeom, hclose, hshift, hsel⟩ :=
    S.exists_shifted_areaCell_collar_selectors_of_geometry ω h ε hε hlf hlfg H hH
      hscale hUW hW t ht ht0 hd φ hφ center rad hO hKO hOW U I K hU hUb hI hIU
      ρ hρ hK r hr hcollar
  refine ⟨R, hR, q, N, hqi, hqc, hgeom, hclose, hshift, ?_⟩
  dsimp only at hsel ⊢
  obtain ⟨hA, hball, hsel⟩ := hsel
  refine ⟨hA, hball, ?_⟩
  intro ν hν hνlaw href hosc C D hC hDC s hs hcover hinner hsrad hUball hIball hballC a b ha hb L T hTD
  obtain ⟨m, E, δ, choice, hδ, hdisj, hcov, hmeas, hdiam, hinner', hinside,
    hcover', hselect, hactive, hmargin, hjoint⟩ :=
      hsel ν hν hνlaw href hosc C D hC hDC s hs hcover hinner hsrad hUball hIball hballC a b ha hb L
  refine ⟨m, E, δ, choice, hδ, hdisj, hcov, hmeas, hdiam, hinner', hinside,
    hcover', hselect, hactive, hmargin, hjoint, ?_⟩
  let : ∀ n, Fintype (R (n + N)) := fun n => (hR (n + N)).fintype
  let : ∀ n, MeasurableSpace (R (n + N)) := fun _ => ⊤
  let : ∀ n, MeasurableSingletonClass (R (n + N)) := fun _ => ⟨fun _ => trivial⟩
  exact S.areaCell_finite_horizon_joint_same_start ω h (fun n => ε (n + N))
    (fun n => hε (n + N)) _ _ (fun n => rfl) _ _ hA center rad
    (fun n j v hv => (hball n j v).2 hv) I D L m E choice T s a
    hdisj hmeas hdiam hinner' hinside hcover' hselect hactive hmargin hTD
    ρ (δ ⟨0, Nat.zero_lt_succ L⟩) b (le_of_lt (hδ _)) hjoint

end MatedCRT
end

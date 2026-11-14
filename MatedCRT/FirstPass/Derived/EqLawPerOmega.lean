import MatedCRT.FirstPass.Derived.WalkLawScaleTransport
import MatedCRT.FirstPass.Derived.ConeScaledWalkData
import MatedCRT.FirstPass.Derived.ReversibilityPairingDiscrete
import MatedCRT.FirstPass.Derived.ExitCouplingEvent
import MatedCRT.FirstPass.Derived.ExitFiniteData
import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureScaling

/-!
# The walk-law modulus from the cone-rescaled stopped walks (Berestycki–Gwynne (2020), §6.4)

For a fixed environment `ω` we bound the vertex-indexed modulus `ω^ε_R(δ)` of the quenched walk laws
(`walkLawModulus`) by the Lévy–Prokhorov distances of the *stopped* walks of the cone-rescaled curve
`η2 s = R_b⁻¹ η (b s)` at mesh `ε / b`:

* `pathLevyProkhorovEDist_eq_levyProkhorovEDist`: the pathwise distance is the Lévy–Prokhorov
  edistance of the local uniform metric.
* `walkLawModulus_le_of_rescaled`: if, for the rescaled curve, (i) the walk from every vertex of
  `V^{ε/b}(B_{1/4})` leaves the interior vertices of `B_{1/2}` before time `s b / ε` with probability at
  most `κ` and (ii) the stopped walks from two vertices of `B_{1/2}` at distance at most `δ` are within
  `r` in Lévy–Prokhorov distance, then `ω^ε_R(δ) ≤ 2 κ + R_b r` whenever `4 (R + 2) < R_b`.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric LatticeProb
open scoped ENNReal NNReal
open MarkovProcess (ContinuousPath)
open MatedCRT.ExitCouplingGlue

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- The pathwise Lévy–Prokhorov edistance is the Lévy–Prokhorov edistance of the local uniform metric. -/
theorem pathLevyProkhorovEDist_eq_levyProkhorovEDist (μ ν : ProbabilityMeasure (ContinuousPath ℂ)) :
    pathLevyProkhorovEDist μ ν =
      levyProkhorovEDist (μ : Measure (ContinuousPath ℂ)) (ν : Measure (ContinuousPath ℂ)) := rfl

/-- The interpolated walk path does not depend on the proof of nonnegativity of the speed. -/
theorem interpPathCM_congr (v : ℤ → ℂ) {m m' : ℝ} (h : m = m') (hm : 0 ≤ m) (hm' : 0 ≤ m') :
    interpPathCM v hm = interpPathCM v hm' := by
  subst h
  rfl

/-- **The walk-law modulus from the stopped walks of the cone-rescaled curve.**  Let `η2 s = R_b⁻¹ η' (b s)`
and `4 (R + 2) < R_b`.  Suppose that, for the walk of the environment `S.mult ε ω`: the exit time from
`A = I^{ε/b}(B_{1/2})` (for `η2`) of the walk started at a vertex of `V^{ε/b}(B_{1/4})` is finite and at least
`(ε/b)⁻¹ s` outside probability `κ` (`exp (-T0) < κ`, `m_ε T0 ≤ (ε/b)⁻¹ s`, `m_ε ε / b ≤ 1`); and the stopped walks
from vertices of `B_{1/2}` at distance at most `δ` have laws within `r`.  Then
`ω^ε_R(δ) ≤ 2 κ + R_b r`. -/
theorem walkLawModulus_le_of_rescaled {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (η' : Ω → C(ℝ, ℂ)) (ω : Ω) {eps b Rb R δ : ℝ} (hε : 0 < eps) (hb : 0 < b)
    (hRb : 4 * (R + 2) < Rb) (η2 : ℝ → ℂ) (hη : ∀ s, η2 s = (Rb : ℂ)⁻¹ * η' ω (b * s))
    (hlam : S.mε eps * (eps / b) ≤ 1) {κ T0 s r : ℝ} (hκ0 : 0 < κ) (hT0 : 0 ≤ T0)
    (hκ : Real.exp (-T0) < κ) (hr : 0 ≤ r) (hmT0 : S.mε eps * T0 ≤ (eps / b)⁻¹ * s)
    (hexit : ∀ x : ℤ, vertexPoint (eps / b) η2 x ∈ ball (0 : ℂ) (1 / 4) →
      srwLaw (S.mult eps ω) x
        {X | (vExitTime (interiorCellVertices (eps / b) η2 (ball (0 : ℂ) (1 / 2))) X : ℝ≥0∞) <
          ENNReal.ofReal ((eps / b)⁻¹ * s)} ≤ ENNReal.ofReal κ)
    (hnull : ∀ x : ℤ, srwLaw (S.mult eps ω) x
      {X | vExitTime (interiorCellVertices (eps / b) η2 (ball (0 : ℂ) (1 / 2))) X = ⊤} = 0)
    (h612 : ∀ x y : ℤ, vertexPoint (eps / b) η2 x ∈ ball (0 : ℂ) (1 / 2) →
      vertexPoint (eps / b) η2 y ∈ ball (0 : ℂ) (1 / 2) →
      dist (vertexPoint (eps / b) η2 x) (vertexPoint (eps / b) η2 y) ≤ δ →
      levyProkhorovEDist
        ((srwLaw (S.mult eps ω) x).map (stoppedInterp (vertexPoint (eps / b) η2) ((eps / b)⁻¹).toNNReal
          (interiorCellVertices (eps / b) η2 (ball (0 : ℂ) (1 / 2)))))
        ((srwLaw (S.mult eps ω) y).map (stoppedInterp (vertexPoint (eps / b) η2) ((eps / b)⁻¹).toNNReal
          (interiorCellVertices (eps / b) η2 (ball (0 : ℂ) (1 / 2))))) ≤ ENNReal.ofReal r) :
    walkLawModulus S η' eps R δ ω ≤ ENNReal.ofReal (2 * κ + Rb * r) := by
  unfold walkLawModulus
  refine iSup_le fun j => iSup_le fun k => iSup_le fun hjk => ?_
  obtain ⟨hj, hk, hd⟩ := hjk
  have hRpos : 0 < R + 1 := lt_of_le_of_lt (norm_nonneg _) (mem_ball_zero_iff.1 hj)
  have hRb1 : 1 ≤ Rb := by linarith
  have hRbpos : 0 < Rb := by linarith
  have hq : 0 < eps / b := div_pos hε hb
  have hvp : ∀ x, vertexPoint eps ⇑(η' ω) x = ((Rb : ℝ) : ℂ) * vertexPoint (eps / b) η2 x :=
    fun x => ConeScaledWalkData.vertexPoint_eq_mul_rescale hb (Complex.ofReal_ne_zero.2 hRbpos.ne')
      (⇑(η' ω)) η2 hη x
  have hnorm : ∀ x, ‖vertexPoint eps ⇑(η' ω) x‖ = Rb * ‖vertexPoint (eps / b) η2 x‖ := by
    intro x
    rw [hvp x, norm_mul, Complex.norm_real, Real.norm_of_nonneg hRbpos.le]
  have hsmall : ∀ x, vertexPoint eps ⇑(η' ω) x ∈ ball (0 : ℂ) (R + 1) →
      vertexPoint (eps / b) η2 x ∈ ball (0 : ℂ) (1 / 4) := by
    intro x hx
    rw [mem_ball_zero_iff] at hx ⊢
    rw [hnorm x] at hx
    by_contra hcon
    have hcon' := not_lt.1 hcon
    nlinarith
  have hdist : dist (vertexPoint eps ⇑(η' ω) j) (vertexPoint eps ⇑(η' ω) k) =
      Rb * dist (vertexPoint (eps / b) η2 j) (vertexPoint (eps / b) η2 k) := by
    rw [dist_eq_norm, dist_eq_norm, hvp j, hvp k, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hRbpos.le]
  have hd' : dist (vertexPoint (eps / b) η2 j) (vertexPoint (eps / b) η2 k) ≤ δ := by
    rw [hdist] at hd
    nlinarith [dist_nonneg (x := vertexPoint (eps / b) η2 j) (y := vertexPoint (eps / b) η2 k)]
  have hmnn : 0 ≤ S.mε eps := S.mε_nonneg eps
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ≥0, lam = (S.mε eps * (eps / b)).toNNReal := ⟨_, rfl⟩
  obtain ⟨m', hm'def⟩ : ∃ m' : ℝ≥0, m' = ((eps / b)⁻¹).toNNReal := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Set ℤ, A = interiorCellVertices (eps / b) η2 (ball (0 : ℂ) (1 / 2)) := ⟨_, rfl⟩
  rw [← hm'def, ← hA] at h612
  rw [← hA] at hexit hnull
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef]
    exact Real.toNNReal_le_iff_le_coe.2 (by simpa using hlam)
  have hlm : ((lam * m' : ℝ≥0) : ℝ) = S.mε eps := by
    rw [NNReal.coe_mul, hlamdef, hm'def, Real.coe_toNNReal _ (mul_nonneg hmnn hq.le),
      Real.coe_toNNReal _ (inv_nonneg.2 hq.le), mul_assoc, mul_inv_cancel₀ hq.ne', mul_one]
  have hc : 1 ≤ Rb.toNNReal := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hRbpos.le]
    simpa using hRb1
  have hv : ∀ x, vertexPoint eps ⇑(η' ω) x =
      (((Rb.toNNReal : ℝ≥0) : ℝ) : ℂ) * vertexPoint (eps / b) η2 x := by
    intro x
    rw [Real.coe_toNNReal _ hRbpos.le]
    exact hvp x
  have hbad : ∀ x : ℤ, vertexPoint eps ⇑(η' ω) x ∈ ball (0 : ℂ) (R + 1) →
      srwLaw (S.mult eps ω) x
        {X | ¬ ∃ n : ℕ, vExitTime A X = n ∧ ((lam * m' : ℝ≥0) : ℝ) * ((T0.toNNReal : ℝ≥0) : ℝ) ≤ n} ≤
          (κ.toNNReal : ℝ≥0∞) := by
    intro x hx
    have h1 := hexit x (hsmall x hx)
    have h0 := hnull x
    have hsub : {X | ¬ ∃ n : ℕ, vExitTime A X = n ∧
          ((lam * m' : ℝ≥0) : ℝ) * ((T0.toNNReal : ℝ≥0) : ℝ) ≤ n} ⊆
        {X | (vExitTime A X : ℝ≥0∞) < ENNReal.ofReal ((eps / b)⁻¹ * s)} ∪
          {X | vExitTime A X = ⊤} := by
      intro X hX
      by_contra hcon
      apply hX
      simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hcon
      obtain ⟨hc1, hc2⟩ := hcon
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hc2
      refine ⟨n, hn.symm, ?_⟩
      rw [← hn] at hc1
      have hc1' : ENNReal.ofReal ((eps / b)⁻¹ * s) ≤ ENNReal.ofReal (n : ℝ) := by
        simpa using hc1
      have hc1'' := (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg n)).1 hc1'
      rw [hlm, Real.coe_toNNReal _ hT0]
      exact hmT0.trans hc1''
    refine le_trans (measure_mono hsub) ((measure_union_le _ _).trans ?_)
    calc _ ≤ ENNReal.ofReal κ + 0 := add_le_add h1 h0.le
      _ = (κ.toNNReal : ℝ≥0∞) := by rw [add_zero]; rfl
  have hκ' : Real.exp (-((T0.toNNReal : ℝ≥0) : ℝ)) < ((κ.toNNReal : ℝ≥0) : ℝ) := by
    rw [Real.coe_toNNReal _ hT0, Real.coe_toNNReal _ hκ0.le]
    exact hκ
  have key := StoppedWalkScaling.levyProkhorovEDist_walk_scale_le (srwLaw (S.mult eps ω) j)
    (srwLaw (S.mult eps ω) k) (vertexPoint eps ⇑(η' ω)) (vertexPoint (eps / b) η2) hc hv hlam1 m' A
    T0.toNNReal κ.toNNReal hκ' (hbad j hj) (hbad k hk)
    (h612 j k (ball_subset_ball (by norm_num) (hsmall j hj))
      (ball_subset_ball (by norm_num) (hsmall k hk)) hd')
  rw [pathLevyProkhorovEDist_eq_levyProkhorovEDist]
  show levyProkhorovEDist (Measure.map (interpPathCM (vertexPoint eps ⇑(η' ω)) (S.mε_nonneg eps))
      (srwLaw (S.mult eps ω) j))
      (Measure.map (interpPathCM (vertexPoint eps ⇑(η' ω)) (S.mε_nonneg eps))
        (srwLaw (S.mult eps ω) k)) ≤ _
  rw [interpPathCM_congr (vertexPoint eps ⇑(η' ω)) hlm.symm (S.mε_nonneg eps) (NNReal.coe_nonneg _)]
  refine key.trans (le_of_eq ?_)
  have e1 : (κ.toNNReal : ℝ≥0∞) = ENNReal.ofReal κ := rfl
  have e2 : (Rb.toNNReal : ℝ≥0∞) = ENNReal.ofReal Rb := rfl
  rw [e1, e2, ← ENNReal.ofReal_mul hRbpos.le, ← ENNReal.ofReal_add (mul_nonneg hRbpos.le hr) hκ0.le,
    ← ENNReal.ofReal_add hκ0.le (by positivity)]
  congr 1
  ring


/-- **The event bound for a fixed scaling `b`** (Berestycki–Gwynne (2020), §6.4).  Let `S'` be the rescaled
environment of `S` (curve `R_b⁻¹ η(b ·)`, boundary-length pair `b^{-1/2} (L, R)(b ·)`, same law).  Away from the four events

* `R_b ≤ 4 (R + 2)`, `M < R_b`,
* the exit time of the walk of `S'` from `I^{ε/b}(B_{1/2})` started in `V^{ε/b}(B_{1/4})` is `< s b / ε` with
  probability `> κ` for some vertex,
* the stopped walks of `S'` from two vertices of `B_{1/2}` at distance `≤ δ` are `> r` apart,

of probability at most `θ` each, the walk-law modulus satisfies `ω^ε_R(δ) ≤ 2 κ + M r`. -/
theorem eqLaw_event_of_scaling {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {S S' : MatedCRTEnv Ω} (hS' : S'.IsValid 𝒮 γ) (hP : S'.P = S.P)
    (η' : Ω → C(ℝ, ℂ)) (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {b : ℝ} (hb : 0 < b)
    (hηs : ∀ᵐ ω ∂S.P, ∀ s : ℝ,
      S'.η ω s = ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s))
    (hbm : ∀ᵐ ω ∂S.P, ∀ s : ℝ, S'.bm ω s = (Real.sqrt b)⁻¹ • S.bm ω (b * s))
    {eps R δ κ T0 s r M θ : ℝ} (hε : 0 < eps) (hκ0 : 0 < κ) (hT0 : 0 ≤ T0)
    (hκ : Real.exp (-T0) < κ) (hr : 0 ≤ r) (hlam : S.mε eps * (eps / b) ≤ 1)
    (hmT0 : S.mε eps * T0 ≤ (eps / b)⁻¹ * s)
    (hE1 : S.P {ω | coneScaleRadius γ (S.hcirc ω) b ≤ 4 * (R + 2)} ≤ ENNReal.ofReal θ)
    (hE2 : S.P {ω | M < coneScaleRadius γ (S.hcirc ω) b} ≤ ENNReal.ofReal θ)
    (hE3 : S'.P {ω | ∃ x : ℤ, vertexPoint (eps / b) (S'.η ω) x ∈ ball (0 : ℂ) (1 / 4) ∧
        ENNReal.ofReal κ < srwLaw (S'.mult (eps / b) ω) x
          {y | (vExitTime (interiorCellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2))) y : ℝ≥0∞) <
            ENNReal.ofReal ((eps / b)⁻¹ * s)}} ≤ ENNReal.ofReal θ)
    (hE4 : S'.P {ω | ∃ x y : ℤ, vertexPoint (eps / b) (S'.η ω) x ∈ ball (0 : ℂ) (1 / 2) ∧
        vertexPoint (eps / b) (S'.η ω) y ∈ ball (0 : ℂ) (1 / 2) ∧
        dist (vertexPoint (eps / b) (S'.η ω) x) (vertexPoint (eps / b) (S'.η ω) y) ≤ δ ∧
        ENNReal.ofReal r < levyProkhorovEDist
          ((srwLaw (S'.mult (eps / b) ω) x).map (stoppedInterp (vertexPoint (eps / b) (S'.η ω))
            ((eps / b)⁻¹).toNNReal (interiorCellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2)))))
          ((srwLaw (S'.mult (eps / b) ω) y).map (stoppedInterp (vertexPoint (eps / b) (S'.η ω))
            ((eps / b)⁻¹).toNNReal (interiorCellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2)))))}
        ≤ ENNReal.ofReal θ) :
    S.P {ω | ENNReal.ofReal (2 * κ + M * r) < walkLawModulus S η' eps R δ ω} ≤
      4 * ENNReal.ofReal θ := by
  have hq : 0 < eps / b := div_pos hε hb
  have hreg := ExitCouplingEvent.ae_regular hγ hγ2 hS'
  rw [hP] at hreg hE3 hE4
  have hle : {ω | ENNReal.ofReal (2 * κ + M * r) < walkLawModulus S η' eps R δ ω} ≤ᵐ[S.P]
      ({ω | coneScaleRadius γ (S.hcirc ω) b ≤ 4 * (R + 2)} ∪ {ω | M < coneScaleRadius γ (S.hcirc ω) b} ∪
        {ω | ∃ x : ℤ, vertexPoint (eps / b) (S'.η ω) x ∈ ball (0 : ℂ) (1 / 4) ∧
          ENNReal.ofReal κ < srwLaw (S'.mult (eps / b) ω) x
            {y | (vExitTime (interiorCellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2))) y : ℝ≥0∞) <
              ENNReal.ofReal ((eps / b)⁻¹ * s)}} ∪
        {ω | ∃ x y : ℤ, vertexPoint (eps / b) (S'.η ω) x ∈ ball (0 : ℂ) (1 / 2) ∧
          vertexPoint (eps / b) (S'.η ω) y ∈ ball (0 : ℂ) (1 / 2) ∧
          dist (vertexPoint (eps / b) (S'.η ω) x) (vertexPoint (eps / b) (S'.η ω) y) ≤ δ ∧
          ENNReal.ofReal r < levyProkhorovEDist
            ((srwLaw (S'.mult (eps / b) ω) x).map (stoppedInterp (vertexPoint (eps / b) (S'.η ω))
              ((eps / b)⁻¹).toNNReal (interiorCellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2)))))
            ((srwLaw (S'.mult (eps / b) ω) y).map (stoppedInterp (vertexPoint (eps / b) (S'.η ω))
              ((eps / b)⁻¹).toNNReal (interiorCellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2)))))}) := by
    filter_upwards [hηs, hae, hbm, hreg] with ω h1 h2 h3 h4 hbad
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_lt, not_le] at hcon
    obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hcon
    obtain ⟨hcont, hprop, hlf, -, hcons⟩ := h4
    have hmult : S'.mult (eps / b) ω = S.mult eps ω := MatedCRTEnv.mult_rescale S S' hb ω h3 eps
    rw [hmult] at c3 c4
    have hT1 := walkLawModulus_le_of_rescaled S η' ω hε hb c1 (S'.η ω)
      (fun t => by rw [h1 t, h2]) hlam hκ0 hT0 hκ hr hmT0 c3
      (fun x => by
        rw [← hmult]
        exact ExitFiniteData.srwLaw_vExitTime_eq_top_null_cellVertices (hlf (eps / b) hq)
          (hcons (eps / b) hq) hq hcont hprop isBounded_ball x)
      (fun x y hx hy hd => by simpa using c4 x y hx hy hd)
    refine absurd hbad (not_lt.2 (hT1.trans (ENNReal.ofReal_le_ofReal ?_)))
    nlinarith
  calc S.P _ ≤ _ := measure_mono_ae hle
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add hE1 hE2)) hE3))
        hE4)
    _ = 4 * ENNReal.ofReal θ := by ring

end MatedCRT.FirstPass.Derived

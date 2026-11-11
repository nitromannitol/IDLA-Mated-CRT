import MatedCRT.FirstPass.S1c.Containment
import MatedCRT.FirstPass.S1c.Cluster
import MatedCRT.FirstPass.S2g.PlateauZero
import MatedCRT.FirstPass.Frozen.S1c
import HarmonicBalls.Draft.Section3
import MatedCRT.FirstPass.S2h.PlateauRawZero

/-!
# Raw radii are almost everywhere measurable (fp-S2h, z1, round 16)

Input `hraw` of `plateauRadii_zero_of_ae_raw` (`FirstPass/S2h/PlateauRawZero.lean`). For a
continuity-good measure (the leastSupersolution is continuous on the closed disc, as HB Lemma 3.1 gives almost
surely, `LeastSupersolutionMemStmt`), the raw radius sublevel set `{rawRadius ≤ c}` equals the event that no
rational point of modulus `> c` lies in the cluster (openness of the cluster off the pole, Cluster.lean). That
event is null-measurable by the S1c argument (Containment.lean). A function whose rational sublevel sets are
null-measurable is almost everywhere measurable (Lemma `aemeasurable_of_nullMeasurableSet_le_rat`).

Terminology: cluster, raw radius and plateau follow the fleet notes (CHATGPT-cone-good-set.md, Section 5); the
potential-theoretic objects (Green function, least supersolution) are those of Armitage-Gardiner and HB Section 3.
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter HarmonicBalls

/-- `γ < Q(γ) = 2/γ + γ/2` for `0 < γ < 2` (HB Notation: `lqgQ`). -/
theorem gamma_lt_lqgQ {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ < lqgQ γ := by
  unfold lqgQ
  have h1 : γ * γ < 4 := by nlinarith
  have h2 : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hγ]
    nlinarith
  linarith

/-- The raw radius is nonnegative (a supremum of norms, junk value `0` on the empty set). -/
theorem rawRadius_nonneg' (ν : Measure ℂ) (N : ℕ) (p : ℝ) : 0 ≤ rawRadius ν N p := by
  unfold rawRadius
  exact Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact norm_nonneg x)

/-- **Deterministic sublevel identity (fp-S2h, z1, round 16).** If the least supersolution of `B_N` with pole `0`
and time `u` is continuous on the closed disc and the Green function is continuous on `B_N \ {0}`, then for `c ≥ 0`
the raw radius is at most `c` iff no rational point of modulus `> c` lies in the cluster. The cluster minus the pole
is open (`isOpen_cluster_diff_pole`), so a cluster point of modulus `> c` produces a rational one. -/
theorem rawRadius_le_iff_forall_ratComplex {ν : Measure ℂ} {N : ℕ} {u c : ℝ} (hc : 0 ≤ c)
    (hv : ContinuousOn (leastSupersolution ν (N : ℝ) 0 u) (closedBall (0 : ℂ) (N : ℝ)))
    (hG : ContinuousOn (greenFunction (ball (0 : ℂ) (N : ℝ)) 0) (ball (0 : ℂ) (N : ℝ) \ {0})) :
    rawRadius ν N u ≤ c ↔ ∀ p ∈ ratComplex, c < ‖p‖ → p ∉ cluster ν (N : ℝ) 0 u := by
  have hKball : cluster ν (N : ℝ) 0 u ⊆ closedBall (0 : ℂ) (N : ℝ) :=
    fun x hx => ball_subset_closedBall hx.1
  have hcl : closure (cluster ν (N : ℝ) 0 u) ⊆ closedBall (0 : ℂ) (N : ℝ) :=
    closure_minimal hKball isClosed_closedBall
  have hbdd : BddAbove ((fun x : ℂ => ‖x‖) '' closure (cluster ν (N : ℝ) 0 u)) :=
    ⟨N, by rintro _ ⟨x, hx, rfl⟩; exact mem_closedBall_zero_iff.1 (hcl hx)⟩
  unfold rawRadius
  constructor
  · intro h p hp hcp hpK
    have hle : ‖p‖ ≤ sSup ((fun x : ℂ => ‖x‖) '' closure (cluster ν (N : ℝ) 0 u)) :=
      le_csSup hbdd ⟨p, subset_closure hpK, rfl⟩
    linarith
  · intro h
    have hKc : ∀ y ∈ cluster ν (N : ℝ) 0 u, ‖y‖ ≤ c := by
      intro y hy
      by_contra hlt
      have hlt' : c < ‖y‖ := not_le.1 hlt
      have hy0 : y ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hlt'
        linarith
      have hWo : IsOpen ((cluster ν (N : ℝ) 0 u \ {0}) ∩ {z : ℂ | c < ‖z‖}) :=
        (isOpen_cluster_diff_pole ν hv hG).inter (isOpen_lt continuous_const continuous_norm)
      have hWne : ((cluster ν (N : ℝ) 0 u \ {0}) ∩ {z : ℂ | c < ‖z‖}).Nonempty :=
        ⟨y, ⟨⟨hy, hy0⟩, hlt'⟩⟩
      obtain ⟨p, hpc, hpW⟩ := ratComplex_meets_open hWo hWne
      exact h p hpc hpW.2 hpW.1.1
    have hcl' : closure (cluster ν (N : ℝ) 0 u) ⊆ closedBall (0 : ℂ) c :=
      closure_minimal (fun y hy => mem_closedBall_zero_iff.2 (hKc y hy)) isClosed_closedBall
    refine Real.sSup_le ?_ hc
    rintro _ ⟨x, hx, rfl⟩
    exact mem_closedBall_zero_iff.1 (hcl' hx)

/-- **Null-measurability of the cluster-avoidance event at a real threshold (fp-S2h, z1, round 16).** Same
argument as `nullMeasurableSet_forall_not_mem_cluster` (S1c/Containment.lean) with the integer threshold replaced
by a real `c ≥ 0`. -/
theorem nullMeasurableSet_forall_ratComplex_not_mem_cluster {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF3 : FrozenDiskGreenNonnegCont)
    {μ : Ω → Measure ℂ} {u : ℝ} (hu : 0 < u) (N : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hloc : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) (N : ℝ)) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P)
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest (N : ℝ))
    (hdense : ∀ φ ∈ nonnegTest (N : ℝ), ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) (N : ℝ),
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε) :
    NullMeasurableSet {ω | ∀ p ∈ ratComplex, c < ‖p‖ → p ∉ cluster (μ ω) (N : ℝ) 0 u} P := by
  have : Countable ↥ratComplex := ratComplex_countable.to_subtype
  have hset : {ω | ∀ p ∈ ratComplex, c < ‖p‖ → p ∉ cluster (μ ω) (N : ℝ) 0 u} =
      ⋂ p : ↥ratComplex, {ω | c < ‖(p : ℂ)‖ → (p : ℂ) ∉ cluster (μ ω) (N : ℝ) 0 u} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Subtype.forall]
  rw [hset]
  refine NullMeasurableSet.iInter fun p => ?_
  by_cases hcp : c < ‖(p : ℂ)‖
  · have hp0 : (p : ℂ) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hcp
      linarith
    have hset' : {ω | c < ‖(p : ℂ)‖ → (p : ℂ) ∉ cluster (μ ω) (N : ℝ) 0 u} =
        {ω | (p : ℂ) ∉ cluster (μ ω) (N : ℝ) 0 u} := by
      ext ω
      simp [hcp]
    rw [hset']
    exact nullMeasurableSet_not_mem_cluster hF1 hF3 hu (Nat.cast_nonneg N) hloc hmeas φs hφs hdense hp0
  · have hset' : {ω | c < ‖(p : ℂ)‖ → (p : ℂ) ∉ cluster (μ ω) (N : ℝ) 0 u} = univ := by
      ext ω
      simp [hcp]
    rw [hset']
    exact MeasurableSet.univ.nullMeasurableSet

/-- **Rational sublevel sets give almost everywhere measurability (fp-S2h, z1, round 16).** A real function all of
whose sublevel sets `{f ≤ q}`, `q ∈ ℚ`, are null-measurable is almost everywhere measurable. Proof: pick measurable
representatives `A q` and a measurable null set `T` off which `f ω ≤ q ↔ ω ∈ A q` for all rationals `q`; then
`f` agrees off `T` with the measurable function `if ω ∈ T then 0 else f ω`. -/
theorem aemeasurable_of_nullMeasurableSet_le_rat {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} (hf : ∀ q : ℚ, NullMeasurableSet {ω | f ω ≤ (q : ℝ)} P) : AEMeasurable f P := by
  classical
  have hf' : ∀ q : ℚ, ∃ t, MeasurableSet t ∧ {ω | f ω ≤ (q : ℝ)} =ᵐ[P] t := fun q => hf q
  choose A hAm hA using hf'
  have hbad : ∀ q : ℚ, P {ω | ¬ (f ω ≤ (q : ℝ) ↔ ω ∈ A q)} = 0 := by
    intro q
    have h := Filter.eventuallyEqSet_iff.1 (hA q)
    have h2 : ∀ᵐ ω ∂P, (f ω ≤ (q : ℝ) ↔ ω ∈ A q) := by
      filter_upwards [h] with ω hω
      exact hω
    exact ae_iff.1 h2
  obtain ⟨T, hTm, hT0, hgood⟩ : ∃ T : Set Ω, MeasurableSet T ∧ P T = 0 ∧
      ∀ ω ∉ T, ∀ q : ℚ, (f ω ≤ (q : ℝ) ↔ ω ∈ A q) := by
    refine ⟨⋃ q : ℚ, toMeasurable P {ω | ¬ (f ω ≤ (q : ℝ) ↔ ω ∈ A q)}, ?_, ?_, ?_⟩
    · exact MeasurableSet.iUnion fun q => measurableSet_toMeasurable _ _
    · refine measure_iUnion_null fun q => ?_
      rw [measure_toMeasurable]
      exact hbad q
    · intro ω hω q
      by_contra h
      exact hω (mem_iUnion.2 ⟨q, subset_toMeasurable _ _ h⟩)
  let g : Ω → ℝ := fun ω => if ω ∈ T then 0 else f ω
  have hgm : Measurable g := by
    refine measurable_of_Iic fun x => ?_
    have hpre : g ⁻¹' Iic x = (T ∩ {_ω | (0 : ℝ) ≤ x}) ∪
        (Tᶜ ∩ ⋂ q : {q : ℚ // x < (q : ℝ)}, A q.1) := by
      ext ω
      by_cases hωT : ω ∈ T
      · simp [g, hωT]
      · have hfx : f ω ≤ x ↔ ∀ q : {q : ℚ // x < (q : ℝ)}, ω ∈ A q.1 := by
          constructor
          · intro h q
            exact (hgood ω hωT q.1).1 (le_trans h q.2.le)
          · intro h
            by_contra hlt
            obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (not_le.1 hlt)
            exact absurd ((hgood ω hωT q).2 (h ⟨q, hq1⟩)) (not_le.2 hq2)
        have hgω : g ω = f ω := by simp [g, hωT]
        rw [mem_preimage, mem_Iic, hgω, hfx]
        simp [hωT]
    rw [hpre]
    exact (hTm.inter (MeasurableSet.const _)).union (hTm.compl.inter (MeasurableSet.iInter fun q => hAm q.1))
  have hae : g =ᵐ[P] f := by
    have hc : Tᶜ ∈ ae P := compl_mem_ae_iff.2 hT0
    filter_upwards [hc] with ω hω
    have hωT : ω ∉ T := hω
    simp [g, hωT]
  exact hgm.aemeasurable.congr hae

/-- **Raw radii are almost everywhere measurable (fp-S2h, z1, round 16; input `hraw` of
`plateauRadii_zero_of_ae_raw`).** Under the HB almost sure continuity of the least supersolutions
(`LeastSupersolutionMemStmt`, Draft Section 3), the Green function continuity `FrozenDiskGreenNonnegCont`, the
S1c measurability hypotheses, and local finiteness, the raw radius `ω ↦ rawRadius (μ ω) N u` is almost everywhere
measurable for `N > 0` and `u > 0`. -/
theorem aemeasurable_rawRadius_of_HB {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {C : Ω → (ℂ → ℝ) → ℝ} {H : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF3 : FrozenDiskGreenNonnegCont)
    (hHB : LeastSupersolutionMemStmt.{0}) (hgff : IsWholePlaneGFF P C H)
    (hlgm : IsLQGMeasureOfField P γ γ H μ) {u : ℝ} (hu : 0 < u) {N : ℕ} (hN : 0 < N)
    (hloc : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) (N : ℝ)) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P)
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest (N : ℝ))
    (hdense : ∀ φ ∈ nonnegTest (N : ℝ), ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) (N : ℝ),
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε) :
    AEMeasurable (fun ω => rawRadius (μ ω) N u) P := by
  have hR : (0 : ℝ) < N := by exact_mod_cast hN
  have hgood : ∀ᵐ ω ∂P, ContinuousOn (leastSupersolution (μ ω) (N : ℝ) 0 u) (closedBall (0 : ℂ) (N : ℝ)) := by
    filter_upwards [hHB γ γ hγ hγ2 (gamma_lt_lqgQ hγ hγ2) Ω P C H μ hgff hlgm] with ω hω
    exact (hω u (N : ℝ) hu hR 0 (mem_ball_self hR)).2.1
  have hsub : ∀ q : ℚ, NullMeasurableSet {ω | rawRadius (μ ω) N u ≤ (q : ℝ)} P := by
    intro q
    by_cases hq : (q : ℝ) < 0
    · have hempty : {ω | rawRadius (μ ω) N u ≤ (q : ℝ)} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact lt_of_lt_of_le hq (rawRadius_nonneg' _ _ _)
      rw [hempty]
      exact MeasurableSet.empty.nullMeasurableSet
    · have hq' : 0 ≤ (q : ℝ) := not_lt.1 hq
      have hset : {ω | rawRadius (μ ω) N u ≤ (q : ℝ)} =ᵐ[P]
          {ω | ∀ p ∈ ratComplex, (q : ℝ) < ‖p‖ → p ∉ cluster (μ ω) (N : ℝ) 0 u} := by
        refine Filter.eventuallyEqSet_iff.2 ?_
        filter_upwards [hgood] with ω hω
        exact rawRadius_le_iff_forall_ratComplex hq' hω ((hF3 (N : ℝ) hR).2)
      exact (nullMeasurableSet_forall_ratComplex_not_mem_cluster hF1 hF3 hu N hq' hloc hmeas φs hφs hdense).congr
        hset.symm
  exact aemeasurable_of_nullMeasurableSet_le_rat hsub

/-- **Zero law for the plateau radii of an LQG measure, conditional on the dilation law (fp-S2h, z1, round 16).**
The raw radii are a.e. measurable (`aemeasurable_rawRadius_of_HB`), so `plateauRadii_zero_of_ae_raw` applies. The
dilation invariance `hscale` (the law of the dilated measure, with its cluster identities) is an explicit hypothesis:
it is the open NEW input of `HalfPlateauNullStep`. `hloc` (local finiteness) and `hmeas` (measurability of the
test integrals of the LQG measure) are explicit hypotheses too. -/
theorem plateauRadii_zero_of_HB {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {C : Ω → (ℂ → ℝ) → ℝ} {H : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF3 : FrozenDiskGreenNonnegCont)
    (hHB : LeastSupersolutionMemStmt.{0}) (hgff : IsWholePlaneGFF P C H) (hlgm : IsLQGMeasureOfField P γ γ H μ)
    (hloc : ∀ N : ℕ, ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) (N : ℝ)) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P)
    (hscale : ∀ s r : ℝ, 0 < s → 0 < r → P {ω | s * r ∈ plateauRadii (μ ω)} = P {ω | r ∈ plateauRadii (μ ω)}) :
    ∀ r : ℝ, 0 < r → P {ω | r ∈ plateauRadii (μ ω)} = 0 := by
  refine plateauRadii_zero_of_ae_raw P μ ?_ hscale
  intro N p hN hp
  obtain ⟨φs, hφs, hdense⟩ := exists_dense_nonnegTest_family (N : ℝ)
  exact aemeasurable_rawRadius_of_HB hγ hγ2 hF1 hF3 hHB hgff hlgm hp hN (hloc N) hmeas φs hφs hdense

end MatedCRT

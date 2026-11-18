import MatedCRT.FirstPass.Derived.UniformStartGoodEvent

/-!
# The measurable sandwich of the uniform-start invariance principle

For a valid environment, a measurable version `η'` of the curve and a dense sequence `d` of the separable
curve space, the measurable event `goodM` (see `UniformStartGoodEvent`) is sandwiched between the
uniform-start event `goodG` at two tolerances, on the environments where `η'` agrees with the curve:
`goodG s ∩ finExit ∩ {η' = η} ⊆ goodM s` (`mem_goodM_of_mem_goodG`, lower sandwich) and
`goodM (κ/2) ∩ {η' = η} ⊆ goodG κ` (`mem_goodG_of_mem_goodM`, upper sandwich).  The abstract versions
`lower_sandwich_abstract` and `upper_sandwich_abstract` are statements about an arbitrary walk law and an
arbitrary Brownian law that exits almost surely; they rest on the isometry between the distance of stopped
paths modulo parametrization and the distance of stopped curve classes.
-/

open MeasureTheory ProbabilityTheory Metric Set MarkovProcess HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT.UniformStartGood

open StopAtExitLevyProkhorov

/-- The distance modulo parametrization of two stopped paths with finite exit times is the distance of
their stopped curve classes. -/
theorem cmpEDist_eq_edist_stoppedExitCurve (U : Set ℂ) {f g : ContinuousPath ℂ}
    (hf : pathExitTime U ⇑f ≠ ⊤) (hg : pathExitTime U ⇑g ≠ ⊤) :
    cmpEDist (stopAtExit U ⇑f) (stopAtExit U ⇑g) =
      edist (stoppedExitCurve U f) (stoppedExitCurve U g) :=
  StopAtExitCurveClass.cmpEDist_stopAtExit_eq_edist_normalizedPrefixCurve U U f g hf hg

/-- **Lower sandwich, abstract form.** If a path law `P` (of the paths `g ξ`) satisfies the
uniform-start inequality at tolerance `s` for all sets of paths, then it satisfies the finite-union-of-balls
inequality of `goodM` at the same tolerance. -/
theorem lower_sandwich_abstract {P : Measure (ℕ → ℤ)} {g : (ℕ → ℤ) → ContinuousPath ℂ}
    {μ : Measure (ContinuousPath ℂ)} {U : Set ℂ} (d : ℕ → BouRabeeGwynne.CurveSpace 2) {s : ℝ}
    (hs : 0 ≤ s) (hP : P {ξ | pathExitTime U ⇑(g ξ) = ⊤} = 0)
    (hμ : μ {b | pathExitTime U ⇑b = ⊤} = 0)
    (hG : ∀ A : Set (ℝ≥0 → ℂ), P {ξ | stopAtExit U ⇑(g ξ) ∈ A} ≤
      μ {b | ∃ f ∈ A, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal s} + ENNReal.ofReal s)
    (F : Finset (ℕ × ℕ)) :
    P {ξ | stoppedExitCurve U (g ξ) ∈ testBall d 0 F} ≤
      μ {b | stoppedExitCurve U b ∈ testBall d s F} + ENNReal.ofReal s := by
  classical
  set A : Set (ℝ≥0 → ℂ) := {f | ∃ ξ, pathExitTime U ⇑(g ξ) ≠ ⊤ ∧
    stoppedExitCurve U (g ξ) ∈ testBall d 0 F ∧ f = stopAtExit U ⇑(g ξ)} with hA
  have h1 : {ξ | stoppedExitCurve U (g ξ) ∈ testBall d 0 F} ⊆
      {ξ | stopAtExit U ⇑(g ξ) ∈ A} ∪ {ξ | pathExitTime U ⇑(g ξ) = ⊤} := by
    intro ξ hξ
    by_cases he : pathExitTime U ⇑(g ξ) = ⊤
    · exact Or.inr he
    · exact Or.inl ⟨ξ, he, hξ, rfl⟩
  have h2 : {b : ContinuousPath ℂ | ∃ f ∈ A, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal s} ⊆
      {b | stoppedExitCurve U b ∈ testBall d s F} ∪ {b | pathExitTime U ⇑b = ⊤} := by
    rintro b ⟨f, ⟨ξ, hξ, hξF, rfl⟩, hlt⟩
    by_cases hb : pathExitTime U ⇑b = ⊤
    · exact Or.inr hb
    · left
      rw [cmpEDist_eq_edist_stoppedExitCurve U hb hξ] at hlt
      simp only [testBall, mem_iUnion, Metric.mem_eball, exists_prop] at hξF ⊢
      obtain ⟨p, hp, hmem⟩ := hξF
      refine ⟨p, hp, ?_⟩
      calc edist (stoppedExitCurve U b) (d p.1)
          ≤ edist (stoppedExitCurve U b) (stoppedExitCurve U (g ξ)) +
            edist (stoppedExitCurve U (g ξ)) (d p.1) := edist_triangle _ _ _
        _ < ENNReal.ofReal s + ENNReal.ofReal (1 / ((p.2 : ℝ) + 1) + 0) := ENNReal.add_lt_add hlt hmem
        _ = ENNReal.ofReal (1 / ((p.2 : ℝ) + 1) + s) := by
          rw [add_zero, add_comm (ENNReal.ofReal s), ← ENNReal.ofReal_add (by positivity) hs]
  calc P {ξ | stoppedExitCurve U (g ξ) ∈ testBall d 0 F}
      ≤ P ({ξ | stopAtExit U ⇑(g ξ) ∈ A} ∪ {ξ | pathExitTime U ⇑(g ξ) = ⊤}) := measure_mono h1
    _ ≤ P {ξ | stopAtExit U ⇑(g ξ) ∈ A} + P {ξ | pathExitTime U ⇑(g ξ) = ⊤} := measure_union_le _ _
    _ = P {ξ | stopAtExit U ⇑(g ξ) ∈ A} := by rw [hP, add_zero]
    _ ≤ μ {b | ∃ f ∈ A, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal s} + ENNReal.ofReal s := hG A
    _ ≤ (μ {b | stoppedExitCurve U b ∈ testBall d s F} + μ {b | pathExitTime U ⇑b = ⊤}) +
          ENNReal.ofReal s :=
        add_le_add_left ((measure_mono h2).trans (measure_union_le _ _)) _
    _ = μ {b | stoppedExitCurve U b ∈ testBall d s F} + ENNReal.ofReal s := by rw [hμ, add_zero]

/-- **Upper sandwich, abstract form.** If a path law `P` satisfies the finite-union-of-balls inequality of
`goodM` at tolerance `κ / 2` and the curve space sequence `d` is dense, then `P` satisfies the
uniform-start inequality at tolerance `κ` for all sets of paths. -/
theorem upper_sandwich_abstract {P : Measure (ℕ → ℤ)} {g : (ℕ → ℤ) → ContinuousPath ℂ}
    {μ : Measure (ContinuousPath ℂ)} {U : Set ℂ} {d : ℕ → BouRabeeGwynne.CurveSpace 2}
    (hd : DenseRange d) {κ : ℝ} (hκ : 0 < κ)
    (hP : P {ξ | pathExitTime U ⇑(g ξ) = ⊤} = 0) (hμ : μ {b | pathExitTime U ⇑b = ⊤} = 0)
    (hM : ∀ F : Finset (ℕ × ℕ), P {ξ | stoppedExitCurve U (g ξ) ∈ testBall d 0 F} ≤
      μ {b | stoppedExitCurve U b ∈ testBall d (κ / 2) F} + ENNReal.ofReal (κ / 2))
    (A : Set (ℝ≥0 → ℂ)) :
    P {ξ | stopAtExit U ⇑(g ξ) ∈ A} ≤
      μ {b | ∃ f ∈ A, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal κ} + ENNReal.ofReal κ := by
  classical
  set I : Set (ℕ × ℕ) := {p | 1 / ((p.2 : ℝ) + 1) < κ / 4 ∧ ∃ ξ, stopAtExit U ⇑(g ξ) ∈ A ∧
    pathExitTime U ⇑(g ξ) ≠ ⊤ ∧
      edist (stoppedExitCurve U (g ξ)) (d p.1) < ENNReal.ofReal (1 / ((p.2 : ℝ) + 1))} with hI
  set FN : ℕ → Finset (ℕ × ℕ) := fun N =>
    ((Finset.range N) ×ˢ (Finset.range N)).filter (· ∈ I) with hFN
  set T : ℕ → Set (ℕ → ℤ) := fun N => {ξ | stoppedExitCurve U (g ξ) ∈ testBall d 0 (FN N)} with hT
  have ha : {ξ | stopAtExit U ⇑(g ξ) ∈ A} ⊆ (⋃ N, T N) ∪ {ξ | pathExitTime U ⇑(g ξ) = ⊤} := by
    intro ξ hξ
    by_cases he : pathExitTime U ⇑(g ξ) = ⊤
    · exact Or.inr he
    · left
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show (0 : ℝ) < κ / 4 by positivity)
      have hmem : stoppedExitCurve U (g ξ) ∈ closure (range d) := by
        rw [hd.closure_range]; exact mem_univ _
      obtain ⟨y, ⟨i, rfl⟩, hy⟩ := EMetric.mem_closure_iff.1 hmem
        (ENNReal.ofReal (1 / ((j : ℝ) + 1))) (ENNReal.ofReal_pos.2 (by positivity))
      refine mem_iUnion.2 ⟨i + j + 1, ?_⟩
      simp only [hT, hFN, testBall, mem_iUnion, Metric.mem_eball, exists_prop, mem_ofPred_eq,
        Finset.mem_filter, Finset.mem_product, Finset.mem_range, add_zero]
      exact ⟨(i, j), ⟨⟨by omega, by omega⟩, hj, ξ, hξ, he, hy⟩, hy⟩
  have hmono : Monotone T := by
    intro N N' hN ξ hξ
    simp only [hT, testBall, mem_iUnion, Metric.mem_eball, exists_prop, mem_ofPred_eq] at hξ ⊢
    obtain ⟨p, hp, hm⟩ := hξ
    refine ⟨p, ?_, hm⟩
    simp only [hFN, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    exact ⟨⟨lt_of_lt_of_le hp.1.1 hN, lt_of_lt_of_le hp.1.2 hN⟩, hp.2⟩
  have hN : ∀ N, P (T N) ≤ μ {b | ∃ f ∈ A, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal κ} +
      ENNReal.ofReal κ := by
    intro N
    have hsub : {b : ContinuousPath ℂ | stoppedExitCurve U b ∈ testBall d (κ / 2) (FN N)} ⊆
        {b | ∃ f ∈ A, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal κ} ∪
          {b | pathExitTime U ⇑b = ⊤} := by
      intro b hb
      by_cases hbe : pathExitTime U ⇑b = ⊤
      · exact Or.inr hbe
      · left
        simp only [testBall, mem_iUnion, Metric.mem_eball, exists_prop, mem_ofPred_eq] at hb
        obtain ⟨p, hp, hmem⟩ := hb
        simp only [hFN, Finset.mem_filter] at hp
        obtain ⟨-, hr4, ξ, hξA, hξfin, hξd⟩ := hp
        refine ⟨_, hξA, ?_⟩
        rw [cmpEDist_eq_edist_stoppedExitCurve U hbe hξfin]
        calc edist (stoppedExitCurve U b) (stoppedExitCurve U (g ξ))
            ≤ edist (stoppedExitCurve U b) (d p.1) + edist (d p.1) (stoppedExitCurve U (g ξ)) :=
              edist_triangle _ _ _
          _ < ENNReal.ofReal (1 / ((p.2 : ℝ) + 1) + κ / 2) +
                ENNReal.ofReal (1 / ((p.2 : ℝ) + 1)) :=
              ENNReal.add_lt_add hmem (by rw [edist_comm]; exact hξd)
          _ = ENNReal.ofReal (1 / ((p.2 : ℝ) + 1) + κ / 2 + 1 / ((p.2 : ℝ) + 1)) :=
              (ENNReal.ofReal_add (by positivity) (by positivity)).symm
          _ ≤ ENNReal.ofReal κ := ENNReal.ofReal_le_ofReal (by linarith)
    calc P (T N) ≤ μ {b | stoppedExitCurve U b ∈ testBall d (κ / 2) (FN N)} +
            ENNReal.ofReal (κ / 2) := hM (FN N)
      _ ≤ (μ {b | ∃ f ∈ A, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal κ} +
            μ {b | pathExitTime U ⇑b = ⊤}) + ENNReal.ofReal (κ / 2) :=
          add_le_add_left ((measure_mono hsub).trans (measure_union_le _ _)) _
      _ = μ {b | ∃ f ∈ A, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal κ} +
            ENNReal.ofReal (κ / 2) := by rw [hμ, add_zero]
      _ ≤ μ {b | ∃ f ∈ A, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal κ} +
            ENNReal.ofReal κ :=
          add_le_add_right (ENNReal.ofReal_le_ofReal (by linarith)) _
  calc P {ξ | stopAtExit U ⇑(g ξ) ∈ A}
      ≤ P ((⋃ N, T N) ∪ {ξ | pathExitTime U ⇑(g ξ) = ⊤}) := measure_mono ha
    _ ≤ P (⋃ N, T N) + P {ξ | pathExitTime U ⇑(g ξ) = ⊤} := measure_union_le _ _
    _ = P (⋃ N, T N) := by rw [hP, add_zero]
    _ = ⨆ N, P (T N) := hmono.measure_iUnion
    _ ≤ _ := iSup_le hN

section Environment

variable {Ω : Type} [MeasurableSpace Ω]

/-- The uniform-start event at tolerance `κ`: the event whose complement is bounded in the statement of the
uniform-start invariance principle. -/
def goodG (S : MatedCRTEnv Ω) (ε R ρ κ : ℝ) : Set Ω :=
  {ω | ∀ x : ℤ, vertexPoint ε (S.η ω) x ∈ closedBall (0 : ℂ) ρ → ∀ A : Set (ℝ≥0 → ℂ),
    srwLaw (S.mult ε ω) x
        {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε (S.η ω) 1 w) ∈ A} ≤
      planarBrownianMotion (vertexPoint ε (S.η ω) x)
        {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
        ENNReal.ofReal κ}

/-- The environments for which the interpolated walk exits `ball 0 R` almost surely from every vertex whose
position lies in `closedBall 0 ρ`. -/
def finExit (S : MatedCRTEnv Ω) (ε R ρ : ℝ) : Set Ω :=
  {ω | ∀ x : ℤ, vertexPoint ε (S.η ω) x ∈ closedBall (0 : ℂ) ρ →
    ∀ᵐ ξ ∂(srwLaw (S.mult ε ω) x),
      pathExitTime (ball (0 : ℂ) R) (interpolatedWalk ε (S.η ω) 1 ξ) ≠ ⊤}

private theorem curve_eq {S : MatedCRTEnv Ω} {η' : Ω → C(ℝ, ℂ)} {ω : Ω} (ε : ℝ)
    (hη : ⇑(η' ω) = S.η ω) :
    (fun k : ℤ => η' ω (ε * k)) = vertexPoint ε (S.η ω) := by
  funext k; rw [← hη]; rfl

private theorem point_eq {S : MatedCRTEnv Ω} {η' : Ω → C(ℝ, ℂ)} {ω : Ω} (ε : ℝ) (x : ℤ)
    (hη : ⇑(η' ω) = S.η ω) : η' ω (ε * x) = vertexPoint ε (S.η ω) x := by
  rw [← hη]; rfl

private theorem bm_exit_null (z : ℂ) (R : ℝ) :
    planarBrownianMotion z {b | pathExitTime (ball (0 : ℂ) R) ⇑b = ⊤} = 0 := by
  have h := StopAtExitWalkBound.ae_pathExitTime_planarBrownianMotion_ne_top
    (Metric.isBounded_ball (x := (0 : ℂ)) (r := R)) z
  rw [ae_iff] at h
  simpa using h

/-- **Lower sandwich.** On the environments where `η'` agrees with the curve and the walk exits almost
surely, the uniform-start event at tolerance `s` is contained in the measurable event `goodM` at `s`. -/
theorem mem_goodM_of_mem_goodG {S : MatedCRTEnv Ω} {η' : Ω → C(ℝ, ℂ)}
    (d : ℕ → BouRabeeGwynne.CurveSpace 2) {ε R ρ s : ℝ} (hs : 0 ≤ s) {ω : Ω}
    (hη : ⇑(η' ω) = S.η ω) (hfin : ω ∈ finExit S ε R ρ) (hG : ω ∈ goodG S ε R ρ s) :
    ω ∈ goodM S η' d ε R ρ s := by
  refine fun x hx => ?_
  have hz := point_eq (ε := ε) x hη
  have hx' : vertexPoint ε (S.η ω) x ∈ closedBall (0 : ℂ) ρ := hz ▸ hx
  have hP : srwLaw (S.mult ε ω) x {ξ | pathExitTime (ball (0 : ℂ) R)
      ⇑(interpPathCM (vertexPoint ε (S.η ω)) zero_le_one ξ) = ⊤} = 0 := by
    have h := hfin x hx'
    rw [ae_iff] at h
    simp only [ne_eq, not_not] at h
    exact h
  rw [curve_eq ε hη, hz]
  exact ⟨hP, fun F => lower_sandwich_abstract (g := interpPathCM (vertexPoint ε (S.η ω)) zero_le_one)
    (U := ball (0 : ℂ) R) d hs hP (bm_exit_null _ R) (fun A => hG x hx' A) F⟩

/-- **Upper sandwich.** On the environments where `η'` agrees with the curve, the measurable event `goodM`
at tolerance `κ / 2` is contained in the uniform-start event at tolerance `κ`. -/
theorem mem_goodG_of_mem_goodM {S : MatedCRTEnv Ω} {η' : Ω → C(ℝ, ℂ)}
    {d : ℕ → BouRabeeGwynne.CurveSpace 2} (hd : DenseRange d) {ε R ρ κ : ℝ} (hκ : 0 < κ) {ω : Ω}
    (hη : ⇑(η' ω) = S.η ω) (hM : ω ∈ goodM S η' d ε R ρ (κ / 2)) :
    ω ∈ goodG S ε R ρ κ := by
  refine fun x hx A => ?_
  have hz := point_eq (ε := ε) x hη
  have hx' : η' ω (ε * x) ∈ closedBall (0 : ℂ) ρ := hz.symm ▸ hx
  obtain ⟨hP, hMF⟩ := hM x hx'
  rw [curve_eq ε hη] at hP
  rw [curve_eq ε hη, hz] at hMF
  exact upper_sandwich_abstract (g := interpPathCM (vertexPoint ε (S.η ω)) zero_le_one)
    (U := ball (0 : ℂ) R) hd hκ hP (bm_exit_null _ R) hMF A

end Environment

end MatedCRT.UniformStartGood

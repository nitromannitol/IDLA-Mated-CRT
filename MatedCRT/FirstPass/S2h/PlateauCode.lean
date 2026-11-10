import MatedCRT.FirstPass.S2h.PlateauTransfer

/-!
# Moment codes of the plateau radii (fp-S2h, z1, round 19; step NEW-1 of `hscale`)

The plateau event of a locally finite measure `ν` is, on the good class where the least supersolutions are continuous at
every radius, a countable Boolean combination of the threshold events of the moment code. The code of radius `N` is the
vector of integrals of the dense test family `famN N` of `exists_dense_nonnegTest_family`; the threshold events are the
analytic sets `Prod.fst '' supersolutionPairs ...` of `S1c/Analytic.lean`. The Borel-free route of CHATGPT-cone-good-set.md
Section 5.1 and CHATGPT-z1-logcert-null.md Sections 3.1-3.2 is followed; null-measurability is by the frozen universal
measurability of analytic sets (`FrozenUniversalMeasurabilityOfAnalytic`), applied to the marginal laws of the codes.
-/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls
open scoped ENNReal

/-- The dense test family of radius `N`: a fixed choice from `exists_dense_nonnegTest_family`. -/
noncomputable def famN (N : ℕ) : ℕ → ℂ → ℝ :=
  Classical.choose (exists_dense_nonnegTest_family (N : ℝ))

theorem famN_mem (N : ℕ) (k : ℕ) : famN N k ∈ nonnegTest (N : ℝ) :=
  (Classical.choose_spec (exists_dense_nonnegTest_family (N : ℝ))).1 k

theorem famN_dense (N : ℕ) : ∀ φ ∈ nonnegTest (N : ℝ), ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) (N : ℝ),
    |φ x - famN N k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (famN N k) x| < ε :=
  (Classical.choose_spec (exists_dense_nonnegTest_family (N : ℝ))).2

/-- The moment code of radius `N` of a measure: its integrals against the family `famN N`. -/
noncomputable def momentCodeN (N : ℕ) (ν : Measure ℂ) : ℕ → ℝ :=
  fun k => ∫ x, famN N k x ∂ν

/-- The joint moment code over all radii. -/
noncomputable def momentCode (ν : Measure ℂ) : ℕ → ℕ → ℝ :=
  fun N => momentCodeN N ν

theorem measurable_momentCodeN (N : ℕ) : Measurable (momentCodeN N) :=
  Measurable.of_eval fun k =>
    measurable_integral_measure_real (contDiff_two_of_isTestFunction (famN_mem N k).1).continuous.measurable

theorem measurable_momentCode : Measurable momentCode :=
  Measurable.of_eval fun N => measurable_momentCodeN N

open Classical in
/-- The threshold code set of radius `N`, time `u`, point `p` and level `q`: the image in the moment code of the
supersolution pairs (analytic, `analyticSet_supersolutionMoments`); empty when `p` is outside the closed disc. -/
noncomputable def threshCell (N : ℕ) (u : ℝ) (p : ℂ) (q : ℚ) : Set (ℕ → ℝ) :=
  if hp : p ∈ closedBall (0 : ℂ) (N : ℝ) then
    Prod.fst '' supersolutionPairs (Nat.cast_nonneg N) (famN N) u
      (greenFunction (ball (0 : ℂ) (N : ℝ)) 0) ⟨p, hp⟩ (q : ℝ)
  else ∅

theorem analyticSet_threshCell (N : ℕ) (u : ℝ) (p : ℂ) (q : ℚ) : AnalyticSet (threshCell N u p q) := by
  unfold threshCell
  split_ifs with hp
  · exact analyticSet_supersolutionMoments (Nat.cast_nonneg N) (fun k => (famN_mem N k).1) u _ ⟨p, hp⟩ (q : ℝ)
  · exact analyticSet_empty

/-- The code set of `p` lying outside the cluster: for every rational level `q` above `-u G(p)` the moment code avoids
the threshold set of `q` is replaced by its contrapositive, so that the set is a countable intersection of analytic
sets (`threshold_iff_moments`, S1c/Threshold.lean:80). -/
noncomputable def notClCode (N : ℕ) (u : ℝ) (p : ℂ) : Set (ℕ → ℝ) :=
  ⋂ q : ℚ, {m | -u * greenFunction (ball (0 : ℂ) (N : ℝ)) 0 p < (q : ℝ) → m ∈ threshCell N u p q}

theorem nullMeasurableSet_notClCode (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (ρ : Measure (ℕ → ℝ))
    [IsFiniteMeasure ρ] (N : ℕ) (u : ℝ) (p : ℂ) : NullMeasurableSet (notClCode N u p) ρ := by
  unfold notClCode
  refine NullMeasurableSet.iInter fun q => ?_
  by_cases h : -u * greenFunction (ball (0 : ℂ) (N : ℝ)) 0 p < (q : ℝ)
  · have hset : {m : ℕ → ℝ | -u * greenFunction (ball (0 : ℂ) (N : ℝ)) 0 p < (q : ℝ) →
        m ∈ threshCell N u p q} = threshCell N u p q := by
      ext m
      simp only [mem_ofPred_eq, h, true_implies]
    rw [hset]
    exact hF1 (ℕ → ℝ) ρ (by infer_instance) _ (analyticSet_threshCell N u p q)
  · have hset : {m : ℕ → ℝ | -u * greenFunction (ball (0 : ℂ) (N : ℝ)) 0 p < (q : ℝ) →
        m ∈ threshCell N u p q} = univ := by
      ext m
      simp only [mem_ofPred_eq, h, false_implies, mem_univ,]
    rw [hset]
    exact MeasurableSet.univ.nullMeasurableSet

open Classical in
/-- The code set of `{ν : rawRadius ν N u ≤ c}` (CHATGPT-cone-good-set.md (36)-(37)): for every rational point `p` of
modulus in `(c, N)`, the moment code of radius `N` avoids the threshold sets of `p` (`notClCode`). -/
noncomputable def rawLeCode (N : ℕ) (u c : ℝ) : Set (ℕ → ℝ) :=
  ⋂ p : ratComplex, {m | (c < ‖(p : ℂ)‖ ∧ ‖(p : ℂ)‖ < (N : ℝ)) → m ∈ notClCode N u (p : ℂ)}

theorem nullMeasurableSet_rawLeCode (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (ρ : Measure (ℕ → ℝ))
    [IsFiniteMeasure ρ] (N : ℕ) (u c : ℝ) : NullMeasurableSet (rawLeCode N u c) ρ := by
  unfold rawLeCode
  have : Countable ↥ratComplex := ratComplex_countable.to_subtype
  refine NullMeasurableSet.iInter fun p => ?_
  by_cases h : c < ‖(p : ℂ)‖ ∧ ‖(p : ℂ)‖ < (N : ℝ)
  · have hset : {m : ℕ → ℝ | (c < ‖(p : ℂ)‖ ∧ ‖(p : ℂ)‖ < (N : ℝ)) → m ∈ notClCode N u (p : ℂ)} =
        notClCode N u (p : ℂ) := by
      ext m
      exact ⟨fun hm => hm h, fun hm _ => hm⟩
    rw [hset]
    exact nullMeasurableSet_notClCode hF1 ρ N u (p : ℂ)
  · have hset : {m : ℕ → ℝ | (c < ‖(p : ℂ)‖ ∧ ‖(p : ℂ)‖ < (N : ℝ)) → m ∈ notClCode N u (p : ℂ)} = univ := by
      ext m
      simp only [mem_ofPred_eq, h, false_implies, mem_univ]
    rw [hset]
    exact MeasurableSet.univ.nullMeasurableSet

open Classical in
/-- The code set of `{ν : rawRadius ν N u = c}`: `rawLeCode c` minus the union of `rawLeCode s` over rational
`0 ≤ s < c` (the value `c` is attained iff it is a bound and no smaller rational bound holds). -/
noncomputable def rawEqCode (N : ℕ) (u c : ℝ) : Set (ℕ → ℝ) :=
  rawLeCode N u c ∩ (⋃ s : {s : ℚ // 0 ≤ (s : ℝ) ∧ (s : ℝ) < c}, rawLeCode N u (s.1 : ℝ))ᶜ

theorem nullMeasurableSet_rawEqCode (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (ρ : Measure (ℕ → ℝ))
    [IsFiniteMeasure ρ] (N : ℕ) (u c : ℝ) : NullMeasurableSet (rawEqCode N u c) ρ := by
  unfold rawEqCode
  refine (nullMeasurableSet_rawLeCode hF1 ρ N u c).inter ?_
  refine NullMeasurableSet.compl ?_
  exact NullMeasurableSet.iUnion fun s => nullMeasurableSet_rawLeCode hF1 ρ N u (s.1 : ℝ)

/-- The code set of one plateau candidate: radius `N`, rational times `0 < p < q`, value `r < N` attained at both times
(one summand of `plateauRadii`, CHATGPT-cone-good-set.md (37)). -/
def plateauCodeAt (N : ℕ) (p q : ℚ) (r : ℝ) : Set (ℕ → ℕ → ℝ) :=
  {m | (0 < N ∧ 0 < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ r < (N : ℝ)) ∧
    (m N ∈ rawEqCode N (p : ℝ) r ∧ m N ∈ rawEqCode N (q : ℝ) r)}

/-- The code set of the plateau radii: the union of the candidates `plateauCodeAt`. -/
def plateauCode (r : ℝ) : Set (ℕ → ℕ → ℝ) :=
  ⋃ (N : ℕ) (p : ℚ) (q : ℚ), plateauCodeAt N p q r

theorem nullMeasurableSet_plateauCodeAt (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (N : ℕ) (p q : ℚ) (r : ℝ)
    (ρ : Measure (ℕ → ℕ → ℝ)) [IsFiniteMeasure ρ] : NullMeasurableSet (plateauCodeAt N p q r) ρ := by
  by_cases h : (0 < N ∧ 0 < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ r < (N : ℝ))
  · have hset : plateauCodeAt N p q r =
        (fun m : ℕ → ℕ → ℝ => m N) ⁻¹' (rawEqCode N (p : ℝ) r ∩ rawEqCode N (q : ℝ) r) := by
      ext m
      exact ⟨fun hm => hm.2, fun hm => ⟨h, hm⟩⟩
    rw [hset]
    refine NullMeasurableSet.preimage (μb := Measure.map (fun m : ℕ → ℕ → ℝ => m N) ρ) ?_
      ⟨measurable_pi_apply N, fun _ h => h⟩
    exact (nullMeasurableSet_rawEqCode hF1 (Measure.map (fun m : ℕ → ℕ → ℝ => m N) ρ) N (p : ℝ) r).inter
      (nullMeasurableSet_rawEqCode hF1 (Measure.map (fun m : ℕ → ℕ → ℝ => m N) ρ) N (q : ℝ) r)
  · have hset : plateauCodeAt N p q r = ∅ := by
      ext m
      exact ⟨fun hm => absurd hm.1 h, fun hm => absurd hm (Set.notMem_empty m)⟩
    rw [hset]
    exact MeasurableSet.empty.nullMeasurableSet

theorem nullMeasurableSet_plateauCode (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (r : ℝ)
    (ρ : Measure (ℕ → ℕ → ℝ)) [IsFiniteMeasure ρ] : NullMeasurableSet (plateauCode r) ρ :=
  NullMeasurableSet.iUnion fun N => NullMeasurableSet.iUnion fun p => NullMeasurableSet.iUnion fun q =>
    nullMeasurableSet_plateauCodeAt hF1 N p q r ρ

theorem not_mem_cluster_iff_momentCodeN {ν : Measure ℂ} {N : ℕ} {u : ℝ} (hu : 0 < u)
    (hloc : ν (closedBall (0 : ℂ) (N : ℝ)) < ⊤)
    (hGnn : ∀ x ∈ ball (0 : ℂ) (N : ℝ), x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) (N : ℝ)) 0 x)
    {p : ℂ} (hp : p ∈ ball (0 : ℂ) (N : ℝ)) (hp0 : p ≠ 0) :
    p ∉ cluster ν (N : ℝ) 0 u ↔ momentCodeN N ν ∈ notClCode N u p := by
  have hpc : p ∈ closedBall (0 : ℂ) (N : ℝ) := ball_subset_closedBall hp
  have key := threshold_iff_moments (μ := ν) (R := (N : ℝ)) (Nat.cast_nonneg N) hloc hu (famN N) (famN_mem N)
    (famN_dense N) hGnn hpc hp0
  have hT : ∀ q : ℚ, threshCell N u p q = Prod.fst '' supersolutionPairs (Nat.cast_nonneg N) (famN N) u
      (greenFunction (ball (0 : ℂ) (N : ℝ)) 0) ⟨p, hpc⟩ (q : ℝ) := fun q => by
    simp only [threshCell, hpc, ↓reduceDIte]
  rw [mem_cluster_iff_of_ne hp0]
  unfold notClCode
  simp only [mem_iInter, mem_ofPred_eq, hT, hp, true_and]
  constructor
  · intro h q hq
    by_contra hc
    exact h (key.2 ⟨q, hq, hc⟩)
  · intro h hL
    obtain ⟨q, hq, hc⟩ := key.1 hL
    exact hc (h q hq)

theorem rawRadius_le_iff_momentCodeN {ν : Measure ℂ} {N : ℕ} {u c : ℝ} (hu : 0 < u) (hc : 0 ≤ c)
    (hloc : ν (closedBall (0 : ℂ) (N : ℝ)) < ⊤)
    (hGnn : ∀ x ∈ ball (0 : ℂ) (N : ℝ), x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) (N : ℝ)) 0 x)
    (hv : ContinuousOn (leastSupersolution ν (N : ℝ) 0 u) (closedBall (0 : ℂ) (N : ℝ)))
    (hG : ContinuousOn (greenFunction (ball (0 : ℂ) (N : ℝ)) 0) (ball (0 : ℂ) (N : ℝ) \ {0})) :
    rawRadius ν N u ≤ c ↔ momentCodeN N ν ∈ rawLeCode N u c := by
  rw [rawRadius_le_iff_forall_ratComplex hc hv hG]
  unfold rawLeCode
  simp only [mem_iInter, mem_ofPred_eq, Subtype.forall]
  constructor
  · intro h p hpR hcond
    have hp0 : p ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hcond
      linarith [hcond.1]
    have hpb : p ∈ ball (0 : ℂ) (N : ℝ) := mem_ball_zero_iff.2 hcond.2
    exact (not_mem_cluster_iff_momentCodeN hu hloc hGnn hpb hp0).1 (h p hpR hcond.1)
  · intro h p hpR hcp
    have hp0 : p ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hcp
      linarith
    by_cases hN : ‖p‖ < (N : ℝ)
    · have hpb : p ∈ ball (0 : ℂ) (N : ℝ) := mem_ball_zero_iff.2 hN
      exact (not_mem_cluster_iff_momentCodeN hu hloc hGnn hpb hp0).2 (h p hpR ⟨hcp, hN⟩)
    · intro hmem
      have hball := ((mem_cluster_iff_of_ne hp0).1 hmem).1
      exact hN (mem_ball_zero_iff.1 hball)

theorem rawRadius_eq_iff_momentCodeN {ν : Measure ℂ} {N : ℕ} {u c : ℝ} (hu : 0 < u) (hc : 0 ≤ c)
    (hloc : ν (closedBall (0 : ℂ) (N : ℝ)) < ⊤)
    (hGnn : ∀ x ∈ ball (0 : ℂ) (N : ℝ), x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) (N : ℝ)) 0 x)
    (hv : ContinuousOn (leastSupersolution ν (N : ℝ) 0 u) (closedBall (0 : ℂ) (N : ℝ)))
    (hG : ContinuousOn (greenFunction (ball (0 : ℂ) (N : ℝ)) 0) (ball (0 : ℂ) (N : ℝ) \ {0})) :
    rawRadius ν N u = c ↔ momentCodeN N ν ∈ rawEqCode N u c := by
  have hR : 0 ≤ rawRadius ν N u := rawRadius_nonneg' ν N u
  have hLe : ∀ x : ℝ, 0 ≤ x → (momentCodeN N ν ∈ rawLeCode N u x ↔ rawRadius ν N u ≤ x) := fun x hx =>
    (rawRadius_le_iff_momentCodeN hu hx hloc hGnn hv hG).symm
  unfold rawEqCode
  constructor
  · intro h
    refine ⟨(hLe c hc).2 h.le, fun hmem => ?_⟩
    obtain ⟨⟨s, hs0, hs1⟩, hs⟩ := mem_iUnion.1 hmem
    have hle := (hLe s hs0).1 hs
    linarith
  · rintro ⟨h1, h2⟩
    have hle : rawRadius ν N u ≤ c := (hLe c hc).1 h1
    refine le_antisymm hle ?_
    by_contra hne
    have hlt : rawRadius ν N u < c := not_le.1 hne
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hlt
    have hs0 : 0 ≤ (s : ℝ) := le_trans hR hs1.le
    exact h2 (mem_iUnion.2 ⟨⟨s, hs0, hs2⟩, (hLe s hs0).2 hs1.le⟩)

end MatedCRT

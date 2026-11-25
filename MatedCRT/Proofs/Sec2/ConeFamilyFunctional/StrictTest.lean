import MatedCRT.Proofs.Sec2.ConeFamilyFunctional.Uniqueness
import MatedCRT.Assembly.ProvedSteps
import MatedCRT.FirstPass.S2g.Draft24

/-!
# The strict growth of the family of Lemma 2.4 as a Borel test on the local measure

For a local measure `s ∈ M_f(B̄_ρ)` the test `StrictTest ρ s` asks that for all rational times `0 < q₁ < q₂` below an
admissible time, the closure of the decoded cluster at time `q₁` lies in the regularized decoded cluster at time `q₂`.

* For a family of Lemma 2.4 whose closures lie in `B_{1/2}` before `T`, strict growth on `(0, T)` is equivalent to the
  test for `ν|_{B̄_ρ}` (`isStrictlyGrowingOn_iff_strictTest`): both sides reduce to rational times by monotonicity.
* The test is Borel (`measurableSet_strictTest`): a compact closure lies in an open set iff it is covered by finitely
  many discs of rational radius with centres in `denseC` whose closures lie in the open set
  (`closure_subset_iff_exists_finset`), and a closed disc lies in a regularized cluster iff a slightly larger open disc
  has all its points of `denseC` in the closure of the cluster (`closedBall_subset_codeBall_iff`).
* For the quantum cone, almost surely a strict family of Lemma 2.4 exists iff the test holds for `μ_h|_{B̄_ρ}`
  (`ae_exists_strict_iff_strictTest`): Lemma 2.4 gives a unique family of Lemma 2.4, and its closures lie in
  `B_{1/2}` before the stopping time (`coneHalfBallClosureInsideStep_holds`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

namespace ConeFamilyFunctional

/-- The strict-growth test on the decoded clusters at rational times. -/
def StrictTest (ρ : ℝ) (s : FinMeasDisk ρ) : Prop :=
  ∀ q₁ q₂ : ℚ, 0 < (q₁ : ℝ) → (q₁ : ℝ) < q₂ → (∃ a : ℚ, (q₂ : ℝ) < a ∧ Admissible ρ s a) →
    closure (StoppedCode.codeCluster ρ q₁ (decoder ρ q₁ s)) ⊆ StoppedCode.codeBall ρ q₂ (decoder ρ q₂ s)

/-- For a family of Lemma 2.4 whose closures lie in `B_{1/2}` before `T`, strict growth is the decoded test. -/
theorem isStrictlyGrowingOn_iff_strictTest {ν : Measure ℂ} [IsLocallyFiniteMeasure ν] {Λ : ℝ → Set ℂ} {T ρ : ℝ}
    (hρ : 1 / 2 < ρ) (hΛ : IsConeHarmonicBallFamilyOn ν Λ T) (hs : IsStoppedAtHalfBall Λ T)
    (hcl : ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ ball 0 (1 / 2)) :
    IsStrictlyGrowingOn Λ T ↔ StrictTest ρ (diskMeasOf ρ ν) := by
  have hρ0 : 0 < ρ := by linarith
  have hclq : ∀ q : ℝ, q ∈ Ioo 0 T →
      closure (StoppedCode.codeCluster ρ q (decoder ρ q (diskMeasOf ρ ν))) = closure (Λ q) := by
    intro q hq
    rw [(codeBall_decoder_eq hρ hΛ hs hq).2, StoppedCode.codeBall,
      StoppedCode.closure_interior_closure_of_isOpen (StoppedCode.isOpen_codeCluster hρ0 hq.1 _)]
  have hT : ∀ q₂ : ℚ, (∃ a : ℚ, (q₂ : ℝ) < a ∧ Admissible ρ (diskMeasOf ρ ν) a) → 0 < (q₂ : ℝ) →
      (q₂ : ℝ) < T := by
    rintro q₂ ⟨a, hqa, hadm⟩ hq₂
    exact hqa.trans ((admissible_iff hρ hΛ hs hcl (hq₂.trans hqa)).1 hadm)
  constructor
  · intro hg q₁ q₂ hq₁ hq₁₂ hex
    have hq₂T := hT q₂ hex (hq₁.trans hq₁₂)
    rw [hclq q₁ ⟨hq₁, hq₁₂.trans hq₂T⟩, ← (codeBall_decoder_eq hρ hΛ hs ⟨hq₁.trans hq₁₂, hq₂T⟩).2]
    exact hg q₁ q₂ hq₁ hq₁₂ hq₂T
  · intro htest s t hs0 hst htT
    obtain ⟨q₁, hsq₁, hq₁t⟩ := exists_rat_btwn hst
    obtain ⟨q₂, hq₁q₂, hq₂t⟩ := exists_rat_btwn hq₁t
    obtain ⟨a, hq₂a, haT⟩ := exists_rat_btwn (hq₂t.trans htT)
    have hq₁T : (q₁ : ℝ) ∈ Ioo 0 T := ⟨hs0.trans hsq₁, hq₁q₂.trans (hq₂t.trans htT)⟩
    have hq₂T : (q₂ : ℝ) ∈ Ioo 0 T := ⟨hq₁T.1.trans hq₁q₂, hq₂t.trans htT⟩
    have hadm : Admissible ρ (diskMeasOf ρ ν) a :=
      (admissible_iff hρ hΛ hs hcl (hq₂T.1.trans hq₂a)).2 haT
    have h1 := htest q₁ q₂ hq₁T.1 hq₁q₂ ⟨a, hq₂a, hadm⟩
    rw [hclq q₁ hq₁T, ← (codeBall_decoder_eq hρ hΛ hs hq₂T).2] at h1
    have hs' : s ∈ Ioo 0 T := ⟨hs0, hst.trans htT⟩
    have ht' : t ∈ Ioo 0 T := ⟨hs0.trans hst, htT⟩
    exact (closure_mono (hΛ.2.1.monotoneOn hs' hq₁T hsq₁.le)).trans
      (h1.trans (hΛ.2.1.monotoneOn hq₂T ht' hq₂t.le))

/-! ### Borel tests for inclusions -/

/-- A compact set lies in an open set iff finitely many discs of rational radius centred in `denseC`, with closures in
the open set, cover it. -/
theorem subset_iff_exists_finset {K V : Set ℂ} (hK : IsCompact K) (hV : IsOpen V) :
    K ⊆ V ↔ ∃ F : Finset (denseC × ℚ), (∀ b ∈ F, closedBall (b.1 : ℂ) b.2 ⊆ V) ∧
      K ⊆ ⋃ b ∈ F, ball (b.1 : ℂ) b.2 := by
  constructor
  · intro hKV
    let ι := {b : denseC × ℚ // closedBall (b.1 : ℂ) b.2 ⊆ V}
    have hcov : K ⊆ ⋃ i : ι, ball (i.1.1 : ℂ) i.1.2 := by
      intro x hx
      obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV x (hKV hx)
      obtain ⟨c, hcD, hcx⟩ : ∃ c ∈ denseC, dist x c < ε / 3 := by
        obtain ⟨c, hc, h⟩ := denseC_spec.2.exists_dist_lt x (by positivity : (0 : ℝ) < ε / 3)
        exact ⟨c, hc, h⟩
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show ε / 3 < 2 * ε / 3 by linarith)
      have hsub : closedBall c r ⊆ V := fun y hy => hεV (by
        rw [mem_ball]
        have := mem_closedBall.1 hy
        linarith [dist_triangle y c x, dist_comm x c])
      refine mem_iUnion.2 ⟨⟨(⟨c, hcD⟩, r), hsub⟩, ?_⟩
      show x ∈ ball c (r : ℝ)
      rw [mem_ball]
      linarith
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : ι => ball (i.1.1 : ℂ) i.1.2) (fun _ => isOpen_ball) hcov
    classical
    refine ⟨t.image Subtype.val, fun b hb => ?_, fun x hx => ?_⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
      exact i.2
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
      exact mem_iUnion₂.2 ⟨i.1, Finset.mem_image_of_mem _ hi, hxi⟩
  · rintro ⟨F, hF, hK⟩ x hx
    obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.1 (hK hx)
    exact hF b hb (ball_subset_closedBall hxb)

/-- A closed disc lies in the interior of the closure of an open set `C` iff, for a larger rational radius, all points of
`denseC` in the open disc lie in `cl C`. -/
theorem closedBall_subset_interior_closure_iff {C : Set ℂ} (c : ℂ) (r : ℝ) :
    closedBall c r ⊆ interior (closure C) ↔
      ∃ r' : ℚ, r < r' ∧ ∀ x ∈ denseC, dist x c < r' → x ∈ closure C := by
  constructor
  · intro h
    by_cases hr : 0 ≤ r
    · obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall c r).exists_thickening_subset_open isOpen_interior h
      obtain ⟨r', hr1, hr2⟩ := exists_rat_btwn (show r < r + δ by linarith)
      refine ⟨r', hr1, fun x _ hx => interior_subset (hδsub ?_)⟩
      rw [mem_thickening_iff]
      by_cases hxr : dist x c ≤ r
      · exact ⟨x, mem_closedBall.2 hxr, by rw [dist_self]; exact hδ⟩
      · push Not at hxr
        refine ⟨c + (r / dist x c : ℝ) • (x - c), ?_, ?_⟩
        · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg hr (dist_nonneg)), ← dist_eq_norm, div_mul_cancel₀ _ (by linarith)]
        · have hd : 0 < dist x c := lt_of_le_of_lt hr hxr
          rw [dist_eq_norm]
          have : x - (c + (r / dist x c : ℝ) • (x - c)) = ((1 - r / dist x c : ℝ)) • (x - c) := by
            rw [sub_smul, one_smul]; abel
          rw [this, norm_smul, Real.norm_eq_abs, ← dist_eq_norm,
            abs_of_nonneg (by rw [sub_nonneg, div_le_one hd]; exact hxr.le), sub_mul, one_mul,
            div_mul_cancel₀ _ hd.ne']
          linarith
    · push Not at hr
      obtain ⟨r', hr1, hr2⟩ := exists_rat_btwn hr
      exact ⟨r', hr1, fun x _ hx => absurd (dist_nonneg.trans_lt hx) (by push Not; exact_mod_cast hr2.le)⟩
  · rintro ⟨r', hr', h⟩
    have hball : ball c r' ⊆ closure C :=
      (denseC_spec.2.open_subset_closure_inter isOpen_ball).trans
        (closure_minimal (fun x hx => h x hx.2 (mem_ball.1 hx.1)) isClosed_closure)
    exact (closedBall_subset_ball hr').trans (interior_maximal hball isOpen_ball)

/-- Point membership in the closure of the cluster of a code is Borel in the code. -/
theorem measurableSet_mem_closure_codeCluster {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (x : ℂ) :
    MeasurableSet {w : DiskFun ρ | x ∈ closure (StoppedCode.codeCluster ρ t w)} := by
  convert StoppedCode.measurableSet_mem_closure_inter_countable (StoppedCode.codeCluster ρ t) denseC_spec.1
    (fun z _ => StoppedCode.measurableSet_mem_codeCluster z) x using 1
  ext w
  have heq : closure (StoppedCode.codeCluster ρ t w) = closure (StoppedCode.codeCluster ρ t w ∩ denseC) :=
    (closure_minimal (denseC_spec.2.open_subset_closure_inter (StoppedCode.isOpen_codeCluster hρ ht w))
      isClosed_closure).antisymm (closure_mono inter_subset_left)
  simp only [mem_ofPred_eq, heq]

/-- A condition `P → w ∈ s` with `s` measurable and `P` independent of `w` is measurable. -/
theorem measurableSet_const_imp' {X : Type*} {m : MeasurableSpace X} {s : Set X} (hs : MeasurableSet[m] s)
    (P : Prop) : MeasurableSet[m] {w | P → w ∈ s} := by
  by_cases hP : P
  · simpa [hP] using hs
  · simp [hP]

/-- The closure of the cluster of a code lies in a fixed open set: a Borel condition on the code. -/
theorem measurableSet_closure_codeCluster_subset {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) {O : Set ℂ}
    (hO : IsOpen O) : MeasurableSet {w : DiskFun ρ | closure (StoppedCode.codeCluster ρ t w) ⊆ O} := by
  have : Countable denseC := denseC_spec.1.to_subtype
  by_cases hOc : Oᶜ.Nonempty
  · have h := MeasurableSet.iUnion fun n : ℕ => MeasurableSet.iInter fun q : denseC =>
      StoppedCode.measurableSet_imp_const (StoppedCode.measurableSet_mem_codeCluster (ρ := ρ) (t := t) (q : ℂ))
        (1 / ((n : ℝ) + 1) ≤ infDist (q : ℂ) Oᶜ)
    convert h using 1
    ext w
    rw [mem_ofPred_eq, StoppedCode.closure_subset_iff_denseC (StoppedCode.isOpen_codeCluster hρ ht w)
      (isBounded_ball.subset (StoppedCode.codeCluster_subset_ball w)) hO hOc]
    simp only [mem_iUnion, mem_iInter, mem_ofPred_eq]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, fun q hq => hn q q.2 hq⟩, fun ⟨n, hn⟩ => ⟨n, fun q hqC hq => hn ⟨q, hqC⟩ hq⟩⟩
  · have hOu : O = univ := by
      rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hOc
      exact hOc
    convert MeasurableSet.univ using 1
    ext w
    simp [hOu]

/-- A closed disc lies in the regularized cluster of a code: a Borel condition on the code. -/
theorem measurableSet_closedBall_subset_codeBall {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (c : ℂ) (r : ℝ) :
    MeasurableSet {w : DiskFun ρ | closedBall c r ⊆ StoppedCode.codeBall ρ t w} := by
  have : Countable denseC := denseC_spec.1.to_subtype
  have h := MeasurableSet.iUnion fun r' : ℚ => measurableSet_const_imp' (P := r < r') (s := ∅)
    MeasurableSet.empty |>.compl.inter (MeasurableSet.iInter fun x : denseC =>
      measurableSet_const_imp' (measurableSet_mem_closure_codeCluster hρ ht (x : ℂ)) (dist (x : ℂ) c < r'))
  convert h using 1
  ext w
  simp only [mem_ofPred_eq, StoppedCode.codeBall, closedBall_subset_interior_closure_iff, mem_iUnion,
    mem_inter_iff, mem_compl_iff, mem_iInter, mem_empty_iff_false, imp_false, not_not]
  exact ⟨fun ⟨r', hr', hall⟩ => ⟨r', hr', fun x => hall x x.2⟩,
    fun ⟨r', hr', hall⟩ => ⟨r', hr', fun x hxD => hall ⟨x, hxD⟩⟩⟩

/-- The inclusion of the closure of one decoded cluster in the regularized decoded cluster of another code is Borel in
the pair of codes. -/
theorem measurableSet_closure_subset_codeBall {ρ t₁ t₂ : ℝ} (hρ : 0 < ρ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) :
    MeasurableSet {w : DiskFun ρ × DiskFun ρ |
      closure (StoppedCode.codeCluster ρ t₁ w.1) ⊆ StoppedCode.codeBall ρ t₂ w.2} := by
  have : Countable denseC := denseC_spec.1.to_subtype
  have hopen : ∀ F : Finset (denseC × ℚ), IsOpen (⋃ b ∈ F, ball (b.1 : ℂ) (b.2 : ℝ)) :=
    fun F => isOpen_biUnion fun b _ => isOpen_ball
  have h := MeasurableSet.iUnion fun F : Finset (denseC × ℚ) =>
    (MeasurableSet.iInter fun b : F => measurable_snd
      (measurableSet_closedBall_subset_codeBall hρ ht₂ (b.1.1 : ℂ) (b.1.2 : ℝ))).inter
    (measurable_fst (measurableSet_closure_codeCluster_subset hρ ht₁ (hopen F)))
  convert h using 1
  ext w
  have hK : IsCompact (closure (StoppedCode.codeCluster ρ t₁ w.1)) :=
    (isBounded_ball.subset (StoppedCode.codeCluster_subset_ball w.1)).isCompact_closure
  rw [mem_ofPred_eq, StoppedCode.codeBall, subset_iff_exists_finset hK isOpen_interior]
  simp only [mem_iUnion, mem_inter_iff, mem_iInter, mem_preimage, mem_ofPred_eq, StoppedCode.codeBall]
  exact ⟨fun ⟨F, hF, hcov⟩ => ⟨F, fun b => hF b.1 b.2, hcov⟩, fun ⟨F, hF, hcov⟩ => ⟨F, fun b hb => hF ⟨b, hb⟩, hcov⟩⟩

/-- The premise "some admissible rational time exceeds `q`" is Borel in the local measure. -/
theorem measurableSet_exists_admissible {ρ : ℝ} (hρ : 0 < ρ) (q : ℝ) :
    MeasurableSet {s : FinMeasDisk ρ | ∃ a : ℚ, q < a ∧ Admissible ρ s a} := by
  convert MeasurableSet.iUnion fun a : ℚ =>
    StoppedCode.measurableSet_and_const (measurableSet_admissible hρ a) (q < a) using 1
  ext s
  simp only [mem_ofPred_eq, mem_iUnion]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, h, ha⟩, fun ⟨a, h, ha⟩ => ⟨a, ha, h⟩⟩

/-- One clause of the strict-growth test is Borel. -/
theorem measurableSet_strictTest_clause {ρ : ℝ} (hρ : 0 < ρ) (q₁ q₂ : ℚ) :
    MeasurableSet {s : FinMeasDisk ρ | 0 < (q₁ : ℝ) → (q₁ : ℝ) < q₂ →
      (∃ a : ℚ, (q₂ : ℝ) < a ∧ Admissible ρ s a) →
      closure (StoppedCode.codeCluster ρ q₁ (decoder ρ q₁ s)) ⊆ StoppedCode.codeBall ρ q₂ (decoder ρ q₂ s)} := by
  by_cases hq : 0 < (q₁ : ℝ) ∧ (q₁ : ℝ) < q₂
  · have hm : MeasurableSet {s : FinMeasDisk ρ |
        closure (StoppedCode.codeCluster ρ q₁ (decoder ρ q₁ s)) ⊆ StoppedCode.codeBall ρ q₂ (decoder ρ q₂ s)} :=
      ((measurable_decoder ρ q₁).prodMk (measurable_decoder ρ q₂))
        (measurableSet_closure_subset_codeBall hρ hq.1 (hq.1.trans hq.2))
    convert ((measurableSet_exists_admissible hρ q₂).compl.union hm) using 1
    ext s
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, hq.1, hq.2, forall_true_left]
    exact imp_iff_not_or
  · convert MeasurableSet.univ using 1
    ext s
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    intro h1 h2
    exact absurd ⟨h1, h2⟩ hq

/-- **The strict-growth test is Borel** on the local measures. -/
theorem measurableSet_strictTest {ρ : ℝ} (hρ : 0 < ρ) : MeasurableSet {s : FinMeasDisk ρ | StrictTest ρ s} := by
  convert MeasurableSet.iInter fun q₁ : ℚ => MeasurableSet.iInter fun q₂ : ℚ =>
    measurableSet_strictTest_clause hρ q₁ q₂ using 1
  ext s
  simp only [StrictTest, mem_ofPred_eq, mem_iInter]

/-! ### The quantum cone -/

/-- **Almost surely a strict family of Lemma 2.4 exists iff the strict-growth test holds** for the quantum cone: Lemma
2.4 gives a unique family of Lemma 2.4, whose closures lie in `B_{1/2}` before its stopping time. -/
theorem ae_exists_strict_iff_strictTest {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) {ρ : ℝ} (hρ : 1 / 2 < ρ) :
    ∀ᵐ ω ∂P, (∃ (T : ℝ) (Λ : ℝ → Set ℂ), IsStrictHalfBallFamily (μ ω) Λ T) ↔
      StrictTest ρ (diskMeasOf ρ (μ ω)) := by
  filter_upwards [coneHarmonicBallsUpToFixedTimeStmt_of_canonical coneCanonicalHalfBallStep_holds
      coneHalfBallClosureInsideStep_holds γ hγ hγ2 Ω P hC hcirc μ hcone,
    coneHalfBallClosureInsideStep_holds γ hγ hγ2 Ω P hC hcirc μ hcone, hcone.2.2] with ω hω hcl hlim
  have : IsLocallyFiniteMeasure (μ ω) := hlim.1
  obtain ⟨T, hT, Λ, hΛ, hs, huniq⟩ := hω
  have hclΛ := hcl T Λ hΛ hs
  rw [← isStrictlyGrowingOn_iff_strictTest hρ hΛ hs hclΛ]
  constructor
  · rintro ⟨T', Λ', hT', hΛ', hs', hg'⟩
    obtain ⟨rfl, heq⟩ := huniq T' Λ' hT' hΛ' hs'
    intro s t hs0 hst htT
    rw [← heq ⟨hs0, hst.trans htT⟩, ← heq ⟨hs0.trans hst, htT⟩]
    exact hg' s t hs0 hst htT
  · intro hg
    exact ⟨T, Λ, hT, hΛ, hs, hg⟩

end ConeFamilyFunctional

end MatedCRT

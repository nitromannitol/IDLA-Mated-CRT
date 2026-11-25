import MatedCRT.Proofs.Sec5.StoppedPoleReduction
import MatedCRT.FirstPass.S5k
import HarmonicBalls.Steps.Sec3.LeastSupersolutionMem
import Mathlib.Topology.Sets.VietorisTopology

/-!
# The stopped harmonic ball as a field-measurable code, and the margin code step

For `0 < ρ < 1` and `t > 0`, the least supersolution `w̄_t = leastSupersolution μ_h ρ 0 t` of the obstacle problem on
`B_ρ` has a `σ(h)`-measurable version with values in `C(B̄_ρ)` (`exists_diskFun_code`): the Lusin-Souslin decoder of
the Borel graph of the obstacle problem (`exists_decoder_disk`), applied to a `σ(h)`-measurable version of `μ_h`
restricted to `B̄_ρ`, agrees with `w̄_t` on `{t < T}` almost surely. This is the route of the answer to the
measurability question of Proposition 5.1 (Bou-Rabee and Gwynne, *Internal DLA on mated-CRT maps*, Theorem 2.3:
the harmonic balls are a Borel function of the area measure).

For a code `w ∈ C(B̄_ρ)` the cluster `codeCluster ρ t w = {x ∈ B_ρ : x = 0 ∨ -t G_{B_ρ}(0, x) < w(x)}` is open, and
its point memberships are Borel in `w`. Its closure is a Borel function of `w` with values in the nonempty compacts
with the Hausdorff (Vietoris) topology (`measurable_codeCompact`): the basic open sets of the Vietoris topology are
tested by hitting open sets with points of a countable dense set, and by containment of the closure in an open set,
which is a uniform lower bound on the distance to the complement at the points of the dense set. The regularized set
`codeBall ρ t w = int cl (codeCluster ρ t w)` has Borel point memberships (`measurableSet_mem_codeBall`). On
`{t < T}`, almost surely, the cluster of the code is the obstacle cluster of `μ_h`, so `Λ_t = codeBall ρ t (W ω)`
(`ae_codeBall_eq`).

* `stoppedMarginCodeStep_holds`: the residual code step `StoppedInterior.StoppedMarginCodeStep` for every model, with
  `K = cl Λ_t` the closure of the cluster of the code and `f = w̄_t + t G_{B_ρ}(0, ·)` the code plus the Green
  function on the margin domain.
* `stoppedInteriorMeasurableStep_holds`: `StoppedInterior.StoppedInteriorMeasurableStep` for every model.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric TopologicalSpace _root_.HarmonicBalls

namespace StoppedCode

/-- Almost surely, for all `0 < ρ < 1` and `t > 0`, the least supersolution is a supersolution (HB Lemma 3.1 in its
deterministic form, under the almost sure volume growth of Lemma 2.7). -/
theorem ae_leastSupersolution_mem {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ t : ℝ, 0 < t →
      leastSupersolution (S.μ ω) ρ 0 t ∈ supersolutions (S.μ ω) ρ 0 t := by
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂S.P, ∃ βm βp,
      VolumeGrowth (S.μ ω) (1 - 1 / ((n : ℝ) + 1)) βm βp := fun n =>
    hS.ae_volumeGrowth_inside_unit hγ hγ2 FirstPass.Derived.volumeGrowthStmt_holds
      (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith)
  have hlf : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) :=
    hS.isLQGMeasure.mono fun ω h => h.isLocallyFiniteMeasure
  filter_upwards [ae_all_iff.mpr hn, hlf] with ω hω hloc ρ hρ0 hρ1 t ht
  obtain ⟨n, hnρ⟩ := exists_nat_one_div_lt (sub_pos.mpr hρ1)
  obtain ⟨βm, βp, hV⟩ := hω n
  exact (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hloc hρ0 (hV.mono (by linarith))
    (Metric.mem_ball_self hρ0) ht).2.2

/-- **A field-measurable code of the least supersolution on the closed disc.** There is a `σ(h)`-measurable
`W : Ω → C(B̄_ρ)` which, almost surely on `{t < T}`, agrees with `w̄_t = leastSupersolution μ_h ρ 0 t` on `B̄_ρ`:
the Lusin-Souslin decoder of the obstacle problem applied to a `σ(h)`-measurable version of `μ_h|_{B̄_ρ}`. -/
theorem exists_diskFun_code (𝒮 : SpaceFillingSLEModel) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ < 1) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {Λ : Ω → ℝ → Set ℂ} (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) {t : ℝ} (ht : 0 < t) :
    ∃ W : Ω → DiskFun ρ, Measurable[S.fieldSigma] W ∧ ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ →
      ∀ x ∈ closedBall (0 : ℂ) ρ, extDisk ρ (W ω) x = leastSupersolution (S.μ ω) ρ 0 t x := by
  obtain ⟨g, hgm, hgae⟩ := frozenLQGMeasureFieldMeasurable_holds 𝒮 γ hγ hγ2 Ω S hS
  obtain ⟨F, hFm, hF1, -⟩ := exists_decoder_disk (ρ := ρ) (t := t) frozenFiniteMeasureDiskStandardBorel_holds
    frozenGreenDiscPole_inRepo hρ ht
  have hloc : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) :=
    hS.isLQGMeasure.mono fun ω h => h.isLocallyFiniteMeasure
  refine ⟨fun ω => F (diskMeasOf ρ (g ω)), hFm.comp ((measurable_diskMeasOf ρ).comp hgm), ?_⟩
  filter_upwards [hgae, hΛ, hloc, ae_leastSupersolution_mem hγ hγ2 hS] with ω hωg hωΛ hωloc hωsup
  intro hexit x hx
  have hId := isObstacleSolutionOn_leastSupersolution frozenGreenDiscPole_inRepo hωΛ hρ ht
    (hωsup ρ hρ hρ1 t ht) hexit
  have hmeas : ((diskMeasOf ρ (g ω) : FinMeasDisk ρ) : Measure ℂ) =
      (S.μ ω).restrict (closedBall (0 : ℂ) ρ) := by
    rw [← hωg]
    exact restrictOrZero_eq_restrict hωloc
  have hId' : IsObstacleSolutionOn ρ t ((diskMeasOf ρ (g ω) : FinMeasDisk ρ) : Measure ℂ)
      (leastSupersolution (S.μ ω) ρ 0 t) := by
    rw [hmeas]
    exact hId
  let fW : DiskFun ρ := ⟨(closedBall (0 : ℂ) ρ).domRestrict (leastSupersolution (S.μ ω) ρ 0 t),
    continuousOn_iff_continuous_domRestrict.1 hId'.continuousOn⟩
  have hcong : IsObstacleSolutionOn ρ t ((diskMeasOf ρ (g ω) : FinMeasDisk ρ) : Measure ℂ) (extDisk ρ fW) :=
    hId'.congr_closedBall frozenGreenDiscPole_inRepo hρ ht (fun y hy => by rw [extDisk_apply_of_mem _ hy]; rfl)
  exact (hF1 _ ⟨fW, hcong⟩).eqOn_closedBall hId' hx

/-! ### The cluster of a code -/

/-- The cluster `{x ∈ B_ρ : x = 0 ∨ -t G_{B_ρ}(0, x) < w(x)}` of a code `w ∈ C(B̄_ρ)`. -/
def codeCluster (ρ t : ℝ) (w : DiskFun ρ) : Set ℂ :=
  floorObstacleCluster ρ t (extDisk ρ w)

theorem isOpen_codeCluster {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (w : DiskFun ρ) : IsOpen (codeCluster ρ t w) :=
  isOpen_obstacleCluster frozenGreenDiscPole_inRepo hρ ht (continuousOn_extDisk w)

theorem zero_mem_codeCluster {ρ t : ℝ} (hρ : 0 < ρ) (w : DiskFun ρ) : (0 : ℂ) ∈ codeCluster ρ t w :=
  ⟨mem_ball_self hρ, Or.inl rfl⟩

theorem codeCluster_subset_ball {ρ t : ℝ} (w : DiskFun ρ) : codeCluster ρ t w ⊆ ball 0 ρ :=
  fun _ hx => hx.1

/-- Point membership in the cluster of a code is a Borel condition on the code. -/
theorem measurableSet_mem_codeCluster {ρ t : ℝ} (x : ℂ) : MeasurableSet {w : DiskFun ρ | x ∈ codeCluster ρ t w} := by
  by_cases hx : x ∈ ball (0 : ℂ) ρ
  · by_cases hx0 : x = 0
    · convert MeasurableSet.univ using 1
      ext w
      exact iff_true_intro ⟨hx, Or.inl hx0⟩
    · have hm : MeasurableSet {w : DiskFun ρ | -t * greenFunction (ball 0 ρ) 0 x < w ⟨x, ball_subset_closedBall hx⟩} :=
        measurableSet_lt measurable_const (measurable_diskFun_eval _)
      convert hm using 1
      ext w
      simp only [codeCluster, mem_obstacleCluster, mem_ofPred_eq, hx, hx0, false_or, true_and,
        extDisk_apply_of_mem _ (ball_subset_closedBall hx)]
  · convert MeasurableSet.empty using 1
    ext w
    exact iff_false_intro fun h => hx h.1

/-- On `{t < T}`, almost surely, the cluster of the code is the obstacle cluster of `μ_h`. -/
theorem codeCluster_eq_cluster {μ : Measure ℂ} {ρ t : ℝ} {w : DiskFun ρ}
    (hw : ∀ x ∈ closedBall (0 : ℂ) ρ, extDisk ρ w x = leastSupersolution μ ρ 0 t x) :
    codeCluster ρ t w = cluster μ ρ 0 t := by
  ext x
  change (x ∈ ball (0 : ℂ) ρ ∧ (x = 0 ∨ -t * greenFunction (ball 0 ρ) 0 x < extDisk ρ w x)) ↔
    (x ∈ ball (0 : ℂ) ρ ∧ (x = 0 ∨ -t * greenFunction (ball 0 ρ) 0 x < leastSupersolution μ ρ 0 t x))
  exact and_congr_right fun hx => by rw [hw x (ball_subset_closedBall hx)]

/-- For an open set `U`, `cl (int (cl U)) = cl U`. -/
theorem closure_interior_closure_of_isOpen {U : Set ℂ} (hU : IsOpen U) :
    closure (interior (closure U)) = closure U := by
  refine (closure_minimal (interior_subset.trans subset_rfl) isClosed_closure).antisymm ?_
  exact closure_mono (hU.subset_interior_iff.mpr subset_closure)

/-! ### Point memberships of closures and regularized sets -/

/-- If point memberships of a random set `A` are measurable on a countable set `C`, then point memberships of
`cl (A ∩ C)` are measurable. -/
theorem measurableSet_mem_closure_inter_countable {X : Type*} [MeasurableSpace X] (A : X → Set ℂ)
    {C : Set ℂ} (hC : C.Countable) (hmem : ∀ z ∈ C, MeasurableSet {w | z ∈ A w}) (x : ℂ) :
    MeasurableSet {w | x ∈ closure (A w ∩ C)} := by
  classical
  have : Countable C := hC.to_subtype
  let B := TopologicalSpace.countableBasis ℂ
  have : Countable B := (TopologicalSpace.countable_countableBasis ℂ).to_subtype
  have hb : ∀ b : B, MeasurableSet
      {w | x ∈ (b : Set ℂ) → ∃ y : C, (y : ℂ) ∈ (b : Set ℂ) ∧ (y : ℂ) ∈ A w} := by
    intro b
    by_cases hx : x ∈ (b : Set ℂ)
    · have h := MeasurableSet.iUnion fun y : C =>
        (show MeasurableSet {w | (y : ℂ) ∈ (b : Set ℂ) ∧ (y : ℂ) ∈ A w} by
          by_cases hy : (y : ℂ) ∈ (b : Set ℂ)
          · simpa [hy] using hmem y y.property
          · simp [hy])
      convert h using 1
      ext w
      simp [hx]
    · simp [hx]
  convert MeasurableSet.iInter hb using 1
  ext w
  simp only [mem_iInter, mem_ofPred_eq]
  rw [(TopologicalSpace.isBasis_countableBasis ℂ).mem_closure_iff]
  constructor
  · intro ha b hxb
    obtain ⟨y, hyb, hyA, hyC⟩ := ha b b.property hxb
    exact ⟨⟨y, hyC⟩, hyb, hyA⟩
  · intro ha b hb hxb
    obtain ⟨y, hyb, hyA⟩ := ha ⟨b, hb⟩ hxb
    exact ⟨y, hyb, hyA, y.property⟩

/-- If point memberships of a random set `A` are measurable on a countable dense set `C` and `C` samples each `A w`
densely, then point memberships of `int (cl (A w))` are measurable. -/
theorem measurableSet_mem_interior_closure_of_countable {X : Type*} [MeasurableSpace X] (A : X → Set ℂ)
    {C : Set ℂ} (hC : C.Countable) (hdense : Dense C) (hmem : ∀ z ∈ C, MeasurableSet {w | z ∈ A w})
    (hsample : ∀ w, A w ⊆ closure (A w ∩ C)) (x : ℂ) :
    MeasurableSet {w | x ∈ interior (closure (A w))} := by
  classical
  have : Countable C := hC.to_subtype
  let B := TopologicalSpace.countableBasis ℂ
  have : Countable B := (TopologicalSpace.countable_countableBasis ℂ).to_subtype
  have hclosure : ∀ y : ℂ, MeasurableSet {w | y ∈ closure (A w)} := by
    intro y
    convert measurableSet_mem_closure_inter_countable A hC hmem y using 1
    ext w
    have heq : closure (A w) = closure (A w ∩ C) :=
      (closure_minimal (hsample w) isClosed_closure).antisymm (closure_mono inter_subset_left)
    simp [heq]
  have hb : ∀ b : B, MeasurableSet
      {w | x ∈ (b : Set ℂ) ∧ ∀ y : C, (y : ℂ) ∈ (b : Set ℂ) → (y : ℂ) ∈ closure (A w)} := by
    intro b
    by_cases hx : x ∈ (b : Set ℂ)
    · have h := MeasurableSet.iInter fun y : C =>
        (show MeasurableSet {w | (y : ℂ) ∈ (b : Set ℂ) → (y : ℂ) ∈ closure (A w)} by
          by_cases hy : (y : ℂ) ∈ (b : Set ℂ)
          · simpa [hy] using hclosure y
          · simp [hy])
      convert h using 1
      ext w
      simp [hx]
    · simp [hx]
  convert MeasurableSet.iUnion hb using 1
  ext w
  simp only [mem_iUnion, mem_ofPred_eq]
  constructor
  · intro hx
    obtain ⟨b, hb, hxb, hbsub⟩ :=
      (TopologicalSpace.isBasis_countableBasis ℂ).exists_subset_of_mem_open hx isOpen_interior
    exact ⟨⟨b, hb⟩, hxb, fun y hy => interior_subset (hbsub hy)⟩
  · rintro ⟨b, hxb, hy⟩
    have hbopen : IsOpen (b : Set ℂ) := (TopologicalSpace.isBasis_countableBasis ℂ).isOpen b.property
    have hbsub : (b : Set ℂ) ⊆ closure (A w) := by
      apply (hdense.open_subset_closure_inter hbopen).trans
      apply closure_minimal _ isClosed_closure
      rintro y ⟨hyb, hyC⟩
      exact hy ⟨y, hyC⟩ hyb
    exact interior_maximal hbsub hbopen hxb

/-- The regularized cluster `int (cl (codeCluster ρ t w))` of a code. -/
def codeBall (ρ t : ℝ) (w : DiskFun ρ) : Set ℂ :=
  interior (closure (codeCluster ρ t w))

/-- Point membership in the regularized cluster of a code is a Borel condition on the code. -/
theorem measurableSet_mem_codeBall {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (x : ℂ) :
    MeasurableSet {w : DiskFun ρ | x ∈ codeBall ρ t w} :=
  measurableSet_mem_interior_closure_of_countable (codeCluster ρ t) denseC_spec.1 denseC_spec.2
    (fun z _ => measurableSet_mem_codeCluster z)
    (fun w => denseC_spec.2.open_subset_closure_inter (isOpen_codeCluster hρ ht w)) x

/-- On `{t < T}`, almost surely, the cone harmonic ball `Λ_t` is the regularized cluster of the code. -/
theorem codeBall_eq_of_family {μ : Measure ℂ} {Λ : ℝ → Set ℂ} (hΛ : IsConeHarmonicBallFamily μ Λ) {ρ t : ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) (hT : t < clusterExitTime Λ ρ) {w : DiskFun ρ}
    (hw : ∀ x ∈ closedBall (0 : ℂ) ρ, extDisk ρ w x = leastSupersolution μ ρ 0 t x) :
    Λ t = codeBall ρ t w := by
  have hsub : Λ t ⊆ ball 0 (ρ / 3) :=
    IDLALowerBound.subset_ball_div_three_of_lt_clusterExitTime hΛ.2.1.monotoneOn ht hT
  rw [(hΛ.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)).1, codeBall, codeCluster_eq_cluster hw]

/-- The code version of `Λ_t`: almost surely on `{t < T}`, `Λ_t = codeBall ρ t (W ω)`. -/
theorem ae_codeBall_eq (𝒮 : SpaceFillingSLEModel) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ < 1) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {Λ : Ω → ℝ → Set ℂ} (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) {t : ℝ} (ht : 0 < t) :
    ∃ W : Ω → DiskFun ρ, Measurable[S.fieldSigma] W ∧ ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ →
      Λ ω t = codeBall ρ t (W ω) ∧
        ∀ x ∈ closedBall (0 : ℂ) ρ, extDisk ρ (W ω) x = leastSupersolution (S.μ ω) ρ 0 t x := by
  obtain ⟨W, hWm, hWae⟩ := exists_diskFun_code 𝒮 hγ hγ2 hρ hρ1 hS hΛ ht
  refine ⟨W, hWm, ?_⟩
  filter_upwards [hWae, hΛ] with ω hωW hωΛ hT
  exact ⟨codeBall_eq_of_family hωΛ hρ ht hT (hωW hT), hωW hT⟩

/-! ### The closure of the cluster as a random compact set -/

/-- The closure of `{0} ∪ codeCluster ρ t w`, a nonempty compact set. -/
def codeCompact (ρ t : ℝ) (w : DiskFun ρ) : NonemptyCompacts ℂ :=
  ⟨⟨closure (insert 0 (codeCluster ρ t w)),
    ((isBounded_ball (x := (0 : ℂ)) (r := ρ)).subset (codeCluster_subset_ball w)).insert 0 |>.isCompact_closure⟩,
    ⟨0, subset_closure (mem_insert 0 _)⟩⟩

theorem coe_codeCompact {ρ t : ℝ} (hρ : 0 < ρ) (w : DiskFun ρ) :
    (codeCompact ρ t w : Set ℂ) = closure (codeCluster ρ t w) := by
  change closure (insert 0 (codeCluster ρ t w)) = closure (codeCluster ρ t w)
  rw [insert_eq_of_mem (zero_mem_codeCluster hρ w)]

/-- A condition `w ∈ s → P` with `s` measurable and `P` independent of `w` is measurable. -/
theorem measurableSet_imp_const {X : Type*} [MeasurableSpace X] {s : Set X} (hs : MeasurableSet s) (P : Prop) :
    MeasurableSet {w | w ∈ s → P} := by
  by_cases hP : P
  · convert MeasurableSet.univ using 1
    ext w
    simp [hP]
  · convert hs.compl using 1
    ext w
    simp [hP]

/-- A condition `w ∈ s ∧ P` with `s` measurable and `P` independent of `w` is measurable. -/
theorem measurableSet_and_const {X : Type*} [MeasurableSpace X] {s : Set X} (hs : MeasurableSet s) (P : Prop) :
    MeasurableSet {w | w ∈ s ∧ P} := by
  by_cases hP : P
  · convert hs using 1
    ext w
    simp [hP]
  · convert MeasurableSet.empty using 1
    ext w
    simp [hP]

/-- The closure of an open set `U` meets an open set `V` iff `U ∩ V` contains a point of `denseC`. -/
theorem closure_inter_nonempty_iff_denseC {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) :
    (closure U ∩ V).Nonempty ↔ ∃ q ∈ denseC, q ∈ U ∧ q ∈ V := by
  rw [closure_inter_open_nonempty_iff hV]
  constructor
  · intro h
    obtain ⟨q, hq, hqC⟩ := denseC_spec.2.inter_open_nonempty _ (hU.inter hV) h
    exact ⟨q, hqC, hq.1, hq.2⟩
  · rintro ⟨q, -, hqU, hqV⟩
    exact ⟨q, hqU, hqV⟩

/-- The closure of an open bounded set `U ∋ 0` lies in an open set `O ≠ ℂ` iff for some `n` every point of `denseC`
in `U` is at distance at least `1/(n+1)` from `Oᶜ`. -/
theorem closure_subset_iff_denseC {U O : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hO : IsOpen O) (hOc : Oᶜ.Nonempty) :
    closure U ⊆ O ↔ ∃ n : ℕ, ∀ q ∈ denseC, q ∈ U → 1 / ((n : ℝ) + 1) ≤ infDist q Oᶜ := by
  constructor
  · intro h
    by_cases hne : (closure U).Nonempty
    · have hK : IsCompact (closure U) := hUb.isCompact_closure
      obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne (continuous_infDist_pt Oᶜ).continuousOn
      have hpos : 0 < infDist x0 Oᶜ :=
        (hO.isClosed_compl.notMem_iff_infDist_pos hOc).1 fun hx => hx (h hx0)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact ⟨n, fun q _ hq => hn.le.trans (isMinOn_iff.1 hmin q (subset_closure hq))⟩
    · refine ⟨0, fun q _ hq => absurd ⟨q, subset_closure hq⟩ hne⟩
  · rintro ⟨n, hn⟩ x hx
    have hcl : closure U ⊆ closure (U ∩ denseC) :=
      closure_minimal (denseC_spec.2.open_subset_closure_inter hU) isClosed_closure
    have hge : x ∈ {y : ℂ | 1 / ((n : ℝ) + 1) ≤ infDist y Oᶜ} :=
      closure_minimal (fun y hy => hn y hy.2 hy.1) (isClosed_le continuous_const (continuous_infDist_pt _))
        (hcl hx)
    by_contra hxO
    have h0 : infDist x Oᶜ = 0 := infDist_zero_of_mem hxO
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have : 1 / ((n : ℝ) + 1) ≤ infDist x Oᶜ := hge
    linarith

attribute [local instance] borel in
/-- **The closure of the cluster is a Borel function of the code**, for the Borel σ-algebra of the Hausdorff
(Vietoris) topology on the nonempty compacts. -/
theorem measurable_codeCompact {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    Measurable (codeCompact ρ t) := by
  have hB : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩
  rw [BorelSpace.measurable_eq (α := NonemptyCompacts ℂ), NonemptyCompacts.isTopologicalBasis.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro s ⟨u, ⟨hu, -, hopen⟩, rfl⟩
  have : Countable denseC := denseC_spec.1.to_subtype
  have hhit : ∀ V, IsOpen V → MeasurableSet {w : DiskFun ρ | (closure (codeCluster ρ t w) ∩ V).Nonempty} := by
    intro V hV
    have h := MeasurableSet.iUnion fun q : denseC =>
      (show MeasurableSet {w : DiskFun ρ | (q : ℂ) ∈ codeCluster ρ t w ∧ (q : ℂ) ∈ V} from
        measurableSet_and_const (measurableSet_mem_codeCluster (ρ := ρ) (t := t) (q : ℂ)) _)
    convert h using 1
    ext w
    rw [mem_ofPred_eq, closure_inter_nonempty_iff_denseC (isOpen_codeCluster hρ ht w) hV, mem_iUnion]
    exact ⟨fun ⟨q, hqC, hqU, hqV⟩ => ⟨⟨q, hqC⟩, hqU, hqV⟩, fun ⟨q, hqU, hqV⟩ => ⟨q, q.2, hqU, hqV⟩⟩
  have hsub : ∀ O, IsOpen O → MeasurableSet {w : DiskFun ρ | closure (codeCluster ρ t w) ⊆ O} := by
    intro O hO
    by_cases hOc : Oᶜ.Nonempty
    · have h := MeasurableSet.iUnion fun n : ℕ => MeasurableSet.iInter fun q : denseC =>
        (show MeasurableSet {w : DiskFun ρ | (q : ℂ) ∈ codeCluster ρ t w →
            1 / ((n : ℝ) + 1) ≤ infDist (q : ℂ) Oᶜ} from
          measurableSet_imp_const (measurableSet_mem_codeCluster (ρ := ρ) (t := t) (q : ℂ)) _)
      convert h using 1
      ext w
      rw [mem_ofPred_eq, closure_subset_iff_denseC (isOpen_codeCluster hρ ht w)
        (isBounded_ball.subset (codeCluster_subset_ball w)) hO hOc]
      simp only [mem_iUnion, mem_iInter, mem_ofPred_eq]
      exact ⟨fun ⟨n, hn⟩ => ⟨n, fun q hq => hn q q.2 hq⟩, fun ⟨n, hn⟩ => ⟨n, fun q hqC hq => hn ⟨q, hqC⟩ hq⟩⟩
    · have hOu : O = univ := by
        rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hOc
        exact hOc
      convert MeasurableSet.univ using 1
      ext w
      simp [hOu]
  convert (hsub _ (isOpen_sUnion hopen)).inter (hu.measurableSet_biInter fun U hU => hhit U (hopen U hU)) using 1
  ext w
  simp only [mem_preimage, mem_ofPred_eq, mem_inter_iff, mem_iInter, coe_codeCompact hρ]

/-! ### The margin code step -/

/-- The margin domain `closedBall 0 (ρ/2) ∩ {s ≤ |x|}` lies in `B̄_ρ` and avoids the pole. -/
theorem marginDomain_subset {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ) :
    StoppedInteriorMargin.marginDomain s (ρ / 2) ⊆ closedBall (0 : ℂ) ρ \ {0} := by
  rintro x ⟨hx, hsx⟩
  refine ⟨closedBall_subset_closedBall (by linarith) hx, fun h0 => ?_⟩
  rw [mem_singleton_iff.1 h0, mem_ofPred_eq, norm_zero] at hsx
  linarith

/-- **The residual code step** `StoppedInterior.StoppedMarginCodeStep` for every model: `K = cl (codeCluster)` and
`f = W + t G_{B_ρ}(0, ·)` on the margin domain, for the field-measurable code `W` of `exists_diskFun_code`. -/
theorem stoppedMarginCodeStep_holds (𝒮 : SpaceFillingSLEModel) : StoppedInterior.StoppedMarginCodeStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ s t _ hs ht
  obtain ⟨W, hWm, hWae⟩ := exists_diskFun_code 𝒮 hγ hγ2 hρ hρ1 hS hΛ ht
  set A : Set ℂ := StoppedInteriorMargin.marginDomain s (ρ / 2) with hAdef
  have hAsub := marginDomain_subset hs hρ
  let ι : C(↥A, closedBall (0 : ℂ) ρ) := ⟨fun x => ⟨x.1, (hAsub x.2).1⟩, by fun_prop⟩
  have hGc : Continuous fun x : ↥A => t * greenFunction (ball 0 ρ) 0 x.1 := by
    refine continuous_const.mul ?_
    exact (frozenGreenDiscPole_inRepo ρ hρ).1.comp_continuous continuous_subtype_val fun x => hAsub x.2
  let gA : C(↥A, ℝ) := ⟨fun x => t * greenFunction (ball 0 ρ) 0 x.1, hGc⟩
  let Φ : DiskFun ρ → C(↥A, ℝ) := fun w => w.comp ι + gA
  have hΦ : Continuous Φ := (ContinuousMap.continuous_precomp ι).add continuous_const
  let : MeasurableSpace (NonemptyCompacts ℂ) := borel _
  have : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩
  refine ⟨fun ω => codeCompact ρ t (W ω), fun ω => Φ (W ω), ?_, ?_⟩
  · have hle : S.fieldSigma ≤ S.envSigma := le_sup_left
    have hK : Measurable[S.fieldSigma] fun ω => codeCompact ρ t (W ω) := (measurable_codeCompact hρ ht).comp hWm
    have hf : Measurable[S.fieldSigma] fun ω => Φ (W ω) := hΦ.measurable.comp hWm
    have hprod : borel (NonemptyCompacts ℂ × C(↥A, ℝ)) = Prod.instMeasurableSpace :=
      (BorelSpace.measurable_eq (α := NonemptyCompacts ℂ × C(↥A, ℝ))).symm
    rw [hprod]
    exact (hK.prodMk hf).mono hle le_rfl
  · filter_upwards [hWae, hΛ] with ω hωW hωΛ hT
    refine ⟨?_, fun x => ?_⟩
    · rw [coe_codeCompact hρ, codeBall_eq_of_family hωΛ hρ ht hT (hωW hT), codeBall,
        closure_interior_closure_of_isOpen (isOpen_codeCluster hρ ht _)]
    · have hx := (hAsub x.2).1
      change W ω (ι x) + t * greenFunction (ball 0 ρ) 0 x.1 = _
      rw [← hωW hT x.1 hx, extDisk_apply_of_mem _ hx]
      rfl

/-- **The measurability step of the stopped interior** `StoppedInterior.StoppedInteriorMeasurableStep` for every
model, from the residual code step. -/
theorem stoppedInteriorMeasurableStep_holds (𝒮 : SpaceFillingSLEModel) :
    StoppedInterior.StoppedInteriorMeasurableStep 𝒮 :=
  StoppedInterior.stoppedInteriorMeasurable_of_code 𝒮 (stoppedMarginCodeStep_holds 𝒮)

end StoppedCode

end MatedCRT

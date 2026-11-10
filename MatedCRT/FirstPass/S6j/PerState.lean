import MatedCRT.FirstPass.S6j.FiniteExit
import MatedCRT.FirstPass.S4S6c.TraceFrom68
import MatedCRT.FirstPass.S6h.Successive
import MatedCRT.FirstPass.S4S6c.PerTest68

/-!
# The per-state outer test bound by a local test at the first hitting vertex (fp-S6j, input `hpt`)

Written argument: `notes/fp-gaps/CHATGPT-z9-6-8-bridge.md` Step C eq. (5) and `notes/fp-gaps/CHATGPT-lemma68-open-parts.md`
lines 600-631 (B18) and 836-860 (C15): the walk started at the state `y0 = X_{T_j}` leaves `A` inside its window
`W y0` with probability at least `q/(1+log(1/R))²`, obtained from the local test at the first hitting time `τ` of the
middle sphere `M`: strong Markov at `τ`, the local bound at `X_τ` (`printed_test_bound`, PerTest68.lean:82), and the
inclusion of the local windows in `W y0`.

* `hit_isWalkRandomTime`: the first hitting time `vHitTime M` of a set `M ⊆ ℤ` is a walk random time.
* `stayIn_le_of_hit`: the abstract per-state bound. Hypotheses: `hincl` (the local windows of the vertices of `M` lie in
  `W y0`), `hloc` (the local bound at each vertex of `M`), `hS2` (almost surely the hitting time precedes the exit from
  `W y0`; write-up C15, z12's S2).
-/

namespace MatedCRT

open MeasureTheory Set Filter
open scoped ENNReal
open WalkPotential

namespace S6j

/-- The first hitting time of a set of vertices is a walk random time. -/
lemma hit_isWalkRandomTime (M : Set ℤ) : IsWalkRandomTime (vHitTime M) := by
  intro k
  rw [histSigma_measurableSet_iff]
  refine ⟨{h : Fin (k + 1) → ℤ | h (Fin.last k) ∈ M ∧ ∀ i : Fin (k + 1), i.val < k → h i ∉ M},
    (Set.to_countable _).measurableSet, ?_⟩
  ext x
  constructor
  · intro hx
    exact (TraceFrom68.vHitTime_eq_iff M k x).2 ⟨hx.1, fun i hi => hx.2 ⟨i, Nat.lt_succ_of_lt hi⟩ hi⟩
  · intro hx
    have hx' := (TraceFrom68.vHitTime_eq_iff M k x).1 hx
    exact ⟨hx'.1, fun i hi => hx'.2 i.val hi⟩

/-- The walk-test event after a random time is measurable. -/
lemma measurableSet_walkTestEvent {τ : (ℕ → ℤ) → ℕ∞} (hτ : IsWalkRandomTime τ) {G : ℤ → Set (ℕ → ℤ)}
    (hG : ∀ y, MeasurableSet (G y)) : MeasurableSet (walkTestEvent τ G) := by
  have hEq : walkTestEvent τ G =
      ⋃ k : ℕ, {x | τ x = (k : ℕ∞)} ∩ {x | WalkPotential.pathShift k x ∈ G (x k)} := by
    ext x
    simp [walkTestEvent]
  rw [hEq]
  exact MeasurableSet.iUnion fun k => (histSigma_le k _ (hτ k)).inter (measurableSet_future_at_state k hG)

/-- If the complement of a measurable event has mass at most `1 - q`, the event has mass at least `q`. -/
lemma ofReal_le_of_compl_le {μ : Measure (ℕ → ℤ)} [IsProbabilityMeasure μ] {s : Set (ℕ → ℤ)}
    (hs : MeasurableSet s) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h : μ sᶜ ≤ ENNReal.ofReal (1 - q)) :
    ENNReal.ofReal q ≤ μ s := by
  have hsum : ENNReal.ofReal q + μ sᶜ ≤ μ s + μ sᶜ := by
    calc ENNReal.ofReal q + μ sᶜ ≤ ENNReal.ofReal q + ENNReal.ofReal (1 - q) := by gcongr
      _ = 1 := by
        have e : q + (1 - q) = 1 := by ring
        rw [← ENNReal.ofReal_add hq0 (by linarith), e, ENNReal.ofReal_one]
      _ = μ s + μ sᶜ := (prob_add_prob_compl hs).symm
  exact ENNReal.le_of_add_le_add_right (measure_ne_top _ _) hsum

/-- Converse of `ofReal_le_of_compl_le`: a mass of at least `q` for the event gives a complement of mass at most
`1 - q`. -/
lemma compl_le_ofReal_of_le {μ : Measure (ℕ → ℤ)} [IsProbabilityMeasure μ] {s : Set (ℕ → ℤ)}
    (hs : MeasurableSet s) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h : ENNReal.ofReal q ≤ μ s) :
    μ sᶜ ≤ ENNReal.ofReal (1 - q) := by
  have hsum : μ sᶜ + ENNReal.ofReal q ≤ μ sᶜ + μ s := by gcongr
  have htot : μ sᶜ + μ s = 1 := by
    rw [add_comm]
    exact prob_add_prob_compl hs
  have hone : ENNReal.ofReal (1 - q) + ENNReal.ofReal q = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hq0, sub_add_cancel, ENNReal.ofReal_one]
  exact ENNReal.le_of_add_le_add_right (ENNReal.ofReal_ne_top) (by rw [hone]; exact hsum.trans_eq htot)

/-- On the event that the hitting time precedes the exit from `W y0`, a walk-test event at the hitting time
is contained in the test event of `W y0`: the local windows of the hitting vertices lie in `W y0`
(`hincl`). -/
lemma walkTestEvent_subset {M : Set ℤ} {W D : ℤ → Set ℤ} {A : Set ℤ} {y0 : ℤ}
    (hincl : ∀ v ∈ M, D v ⊆ W y0) {x : ℕ → ℤ} (hx : vHitTime M x < vExitTime (W y0) x)
    (hw : x ∈ walkTestEvent (vHitTime M) (fun v => testEvent D A v)) : x ∈ testEvent W A y0 := by
  obtain ⟨k, hk, hs⟩ := hw
  obtain ⟨i, hi, hiA⟩ := hs
  have hmem : x k ∈ M := ((TraceFrom68.vHitTime_eq_iff M k x).1 hk).1
  have hkW : (k : ℕ∞) < vExitTime (W y0) x := hk ▸ hx
  have h1 := natCast_lt_vExitTime_iff.1 hkW
  have h2 := natCast_lt_vExitTime_iff.1 hi
  refine ⟨k + i, ?_, ?_⟩
  · apply natCast_lt_vExitTime_iff.2
    intro n hn
    by_cases hnk : n ≤ k
    · exact h1 n hnk
    · have hj : n - k ≤ i := by omega
      have e : x n = WalkPotential.pathShift k x (n - k) := by
        show x n = x (k + (n - k))
        congr 1
        omega
      rw [e]
      exact hincl (x k) hmem (h2 (n - k) hj)
  · exact hiA

/-- **Per-state outer test bound (abstract form).** Started at `y0`, the walk leaves `A` before its exit from `W y0`
with probability at least `q`, given the local bound `hloc` at every vertex of the middle sphere `M`, the inclusion
`hincl` of the local windows, and `hS2`: almost surely the first hitting time of `M` precedes the exit from `W y0`.
Proof: strong Markov at the hitting time (`srwLaw_condExp_strong_markov`), then the inclusion. -/
theorem stayIn_le_of_hit (m : ℤ → ℤ → ℕ) (y0 : ℤ) (W D : ℤ → Set ℤ) (M A : Set ℤ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hincl : ∀ v ∈ M, D v ⊆ W y0)
    (hloc : ∀ v ∈ M, srwLaw m v (TestBound68.stayIn D A v) ≤ ENNReal.ofReal (1 - q))
    (hS2 : ∀ᵐ x ∂srwLaw m y0, vHitTime M x < vExitTime (W y0) x) :
    srwLaw m y0 (TestBound68.stayIn W A y0) ≤ ENNReal.ofReal (1 - q) := by
  set G : ℤ → Set (ℕ → ℤ) := fun v => testEvent D A v with hGdef
  have hG : ∀ v, MeasurableSet (G v) := fun v => measurableSet_testEvent D A v
  have hτ := hit_isWalkRandomTime M
  have hAt : ∀ v ∈ M, q ≤ stateProb m G v := by
    intro v hv
    have h1 := ofReal_le_of_compl_le (measurableSet_testEvent D A v) hq0 hq1
      (by rw [testEvent_compl]; exact hloc v hv)
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h1
  have hcond := srwLaw_condExp_strong_markov m y0 (vHitTime M) hτ G hG
  have hlow : ∀ᵐ x ∂srwLaw m y0, q ≤ atRandomTime m G (vHitTime M) x := by
    filter_upwards [hS2] with x hx
    have hlt : vHitTime M x < ⊤ := lt_of_lt_of_le hx le_top
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hlt.ne
    have hmem : x k ∈ M := ((TraceFrom68.vHitTime_eq_iff M k x).1 hk.symm).1
    simp only [atRandomTime, hlt.ne, ite_false]
    rw [← hk, ENat.toNat_natCast]
    exact hAt _ hmem
  have hint : q ≤ ∫ x, atRandomTime m G (vHitTime M) x ∂srwLaw m y0 := by
    have := integral_mono_ae (integrable_const q) (integrable_atRandomTime m y0 G (vHitTime M) hτ)
      (hlow.mono fun x hx => hx)
    simpa using this
  have hid : (srwLaw m y0).real (walkTestEvent (vHitTime M) G) =
      ∫ x, atRandomTime m G (vHitTime M) x ∂srwLaw m y0 := by
    have hB := measurableSet_walkTestEvent hτ hG
    rw [← integral_indicator_one hB]
    rw [← integral_condExp (stoppedSigma_le (vHitTime M) hτ)]
    exact integral_congr_ae hcond
  have hreal : q ≤ (srwLaw m y0 (walkTestEvent (vHitTime M) G)).toReal := by
    rw [← measureReal_def, hid]
    exact hint
  have hsub : srwLaw m y0 (walkTestEvent (vHitTime M) G) ≤ srwLaw m y0 (testEvent W A y0) :=
    measure_mono_ae (hS2.mono fun x hx hw => walkTestEvent_subset hincl hx hw)
  have hP : ENNReal.ofReal q ≤ srwLaw m y0 (walkTestEvent (vHitTime M) G) :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hreal
  rw [← testEvent_compl]
  exact compl_le_ofReal_of_le (measurableSet_testEvent W A y0) hq0 hq1 (hP.trans hsub)


/-- The middle-sphere vertices: the cells meeting the sphere `∂B_{4R/3}(z)` (write-up Step C, the local test vertices). -/
def middleVertices (ε : ℝ) (η : ℝ → ℂ) (z : ℂ) (R : ℝ) : Set ℤ :=
  {v | (cell ε η v ∩ Metric.sphere z (4 * R / 3)).Nonempty}

/-- For a middle vertex `v`, the window of its local test lies in the window `I(B_{2R}(z))` of the state
(write-up C3; `R/4`-ball around the vertex, cells of diameter at most `c₀R`, `c₀ < 1/8`). -/
lemma interiorCellVertices_vertex_ball_sub {η : ℝ → ℂ} (hη : Continuous η) {ε R c0 : ℝ} {z : ℂ} {v : ℤ}
    (hε : 0 < ε) (hR : 0 < R) (hc0 : c0 < 1 / 8)
    (hv : (cell ε η v ∩ Metric.sphere z (4 * R / 3)).Nonempty)
    (hdy : Metric.diam (cell ε η v) ≤ R / 100)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ Metric.ball (vertexPoint ε η v) (R / 4)).Nonempty →
      Metric.diam (cell ε η k) ≤ c0 * R) :
    interiorCellVertices ε η (Metric.ball (vertexPoint ε η v) (R / 4)) ⊆
      interiorCellVertices ε η (Metric.ball z (2 * R)) := by
  obtain ⟨p0, hp0c, hp0s⟩ := hv
  have hp0 : dist p0 z = 4 * R / 3 := Metric.mem_sphere.1 hp0s
  have hvc : vertexPoint ε η v ∈ cell ε η v := ⟨ε * v, ⟨by nlinarith, le_rfl⟩, rfl⟩
  have hcpt : ∀ k : ℤ, IsCompact (cell ε η k) := fun k => isCompact_Icc.image hη
  have hd1 : dist (vertexPoint ε η v) p0 ≤ R / 100 :=
    (Metric.dist_le_diam_of_mem (hcpt v).isBounded hvc hp0c).trans hdy
  have hvz : dist (vertexPoint ε η v) z ≤ 4 * R / 3 + R / 100 := by
    have := dist_triangle (vertexPoint ε η v) p0 z
    linarith
  rintro k ⟨hk1, -⟩
  have hk1' : (cell ε η k ∩ Metric.ball (vertexPoint ε η v) (R / 4)).Nonempty := hk1
  obtain ⟨q, hqc, hqb⟩ := hk1'
  rw [Metric.mem_ball] at hqb
  refine ⟨⟨q, hqc, ?_⟩, ?_⟩
  · rw [Metric.mem_ball]
    have := dist_triangle q (vertexPoint ε η v) z
    linarith
  · intro hfr
    obtain ⟨p, hpc, hpf⟩ := hfr
    rw [frontier_ball z (by positivity : 2 * R ≠ 0), Metric.mem_sphere] at hpf
    have hdq : Metric.diam (cell ε η k) ≤ c0 * R := hdiam k ⟨q, hqc, Metric.mem_ball.2 hqb⟩
    have hpq : dist p q ≤ Metric.diam (cell ε η k) := Metric.dist_le_diam_of_mem (hcpt k).isBounded hpc hqc
    have := dist_triangle p q z
    have := dist_triangle q (vertexPoint ε η v) z
    have hc : c0 * R < R / 8 := by nlinarith
    linarith

/-- **Per-state outer test bound (the concrete window).** For the state `y0` with centre `z` and radius `R`, the
walk from `y0` leaves `A` before its exit from `I(B_{2R}(z))` with probability at least `min q0 1/(1+log(1/R))²`.
Inputs: the local bound `hloc` at the middle-sphere vertices (printed_test_bound at the local window `I(B_{R/4}(v))`
with scale `r := R`), the local diameter inputs `hdy`, `hdiam` (write-up B11, C3), and `hS2` (z12's S2). -/
theorem perState_stayIn_le {η : ℝ → ℂ} (hη : Continuous η) {ε R c0 q0 : ℝ} {z : ℂ} (m : ℤ → ℤ → ℕ) (y0 : ℤ)
    (A : Set ℤ) (hε : 0 < ε) (hR : 0 < R) (hR1 : R ≤ 1) (hc0 : c0 < 1 / 8) (hq0 : 0 < q0)
    (hloc : ∀ v ∈ middleVertices ε η z R,
      srwLaw m v (TestBound68.stayIn (fun u => interiorCellVertices ε η (Metric.ball (vertexPoint ε η u) (R / 4))) A v)
        ≤ ENNReal.ofReal (1 - min q0 1 / (1 + Real.log (1 / R)) ^ 2))
    (hdy : ∀ v ∈ middleVertices ε η z R, Metric.diam (cell ε η v) ≤ R / 100)
    (hdiam : ∀ v ∈ middleVertices ε η z R, ∀ k : ℤ,
      (cell ε η k ∩ Metric.ball (vertexPoint ε η v) (R / 4)).Nonempty → Metric.diam (cell ε η k) ≤ c0 * R)
    (hS2 : ∀ᵐ x ∂srwLaw m y0,
      vHitTime (middleVertices ε η z R) x < vExitTime (interiorCellVertices ε η (Metric.ball z (2 * R))) x) :
    srwLaw m y0 (TestBound68.stayIn (fun _ => interiorCellVertices ε η (Metric.ball z (2 * R))) A y0) ≤
      ENNReal.ofReal (1 - min q0 1 / (1 + Real.log (1 / R)) ^ 2) := by
  have hlog : 0 ≤ Real.log (1 / R) := Real.log_nonneg (one_le_one_div hR hR1)
  have hL : 1 ≤ (1 + Real.log (1 / R)) ^ 2 := by nlinarith
  have hq0' : 0 ≤ min q0 1 / (1 + Real.log (1 / R)) ^ 2 := by
    apply div_nonneg (le_min hq0.le zero_le_one) (sq_nonneg _)
  have hq1' : min q0 1 / (1 + Real.log (1 / R)) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact (min_le_right _ _).trans hL
  exact stayIn_le_of_hit m y0 (fun _ => interiorCellVertices ε η (Metric.ball z (2 * R)))
    (fun v => interiorCellVertices ε η (Metric.ball (vertexPoint ε η v) (R / 4)))
    (middleVertices ε η z R) A hq0' hq1'
    (fun v hv => interiorCellVertices_vertex_ball_sub hη hε hR hc0 hv (hdy v hv) (hdiam v hv))
    (fun v hv => hloc v hv) hS2


/-- **hpt in the form of `cfgSchedule_valid` (S6h/Schedule.lean).** For a family of successive times `T j`, a centre
map `Z` and a radius map `Rs` (instantiated at `cfgCentre`, `cfgStateRadius`), and a predicate `Good` on the states
(the good event of the configuration), the almost-sure per-state bound at the state `X_{T_j}` holds. The hypotheses are
per state: `hloc` (printed_test_bound at the local windows of the middle vertices), `hdy`, `hdiam` (cell diameters) and
`hS2` (z12's S2), and `hgood` is the almost-sure statement that the exit state is good. -/
theorem hpt_of_state (m : ℤ → ℤ → ℕ) (a : ℤ) (η : ℝ → ℂ) (hη : Continuous η) {ε c0 q0 : ℝ} (A : Set ℤ)
    (T : ℕ → (ℕ → ℤ) → ℕ∞) (Z : ℤ → ℂ) (Rs : ℤ → ℝ) (Good : ℤ → Prop)
    (hε : 0 < ε) (hc0 : c0 < 1 / 8) (hq0 : 0 < q0)
    (hR : ∀ y, 0 < Rs y) (hR1 : ∀ y, Rs y ≤ 1)
    (hloc : ∀ y, Good y → ∀ v ∈ middleVertices ε η (Z y) (Rs y),
      srwLaw m v (TestBound68.stayIn (fun u => interiorCellVertices ε η (Metric.ball (vertexPoint ε η u) (Rs y / 4)))
        A v) ≤ ENNReal.ofReal (1 - min q0 1 / (1 + Real.log (1 / Rs y)) ^ 2))
    (hdy : ∀ y, Good y → ∀ v ∈ middleVertices ε η (Z y) (Rs y), Metric.diam (cell ε η v) ≤ Rs y / 100)
    (hdiam : ∀ y, Good y → ∀ v ∈ middleVertices ε η (Z y) (Rs y), ∀ k : ℤ,
      (cell ε η k ∩ Metric.ball (vertexPoint ε η v) (Rs y / 4)).Nonempty → Metric.diam (cell ε η k) ≤ c0 * Rs y)
    (hS2 : ∀ y, Good y → ∀ᵐ p ∂srwLaw m y,
      vHitTime (middleVertices ε η (Z y) (Rs y)) p < vExitTime (interiorCellVertices ε η (Metric.ball (Z y) (2 * Rs y))) p)
    (hgood : ∀ j, ∀ᵐ x ∂srwLaw m a, T j x < ⊤ → Good (x (T j x).toNat)) (j : ℕ) :
    ∀ᵐ x ∂srwLaw m a, T j x < ⊤ →
      srwLaw m (x (T j x).toNat)
          (TestBound68.stayIn (fun y => interiorCellVertices ε η (Metric.ball (Z y) (2 * Rs y))) A (x (T j x).toNat)) ≤
        ENNReal.ofReal (1 - min q0 1 / (1 + Real.log (1 / Rs (x (T j x).toNat))) ^ 2) := by
  filter_upwards [hgood j] with x hg hT
  exact perState_stayIn_le hη m (x (T j x).toNat) A hε (hR _) (hR1 _) hc0 hq0
    (hloc _ (hg hT)) (hdy _ (hg hT)) (hdiam _ (hg hT)) (hS2 _ (hg hT))


/-- The successive exit schedule of S6h (`Lemma68Successive.exitSchedule`, one window function) is the schedule
`nextExitSchedule` with the constant family of windows: the finiteness of `FiniteExit` applies to `cfgExit`. -/
lemma exitSchedule_eq_nextExitSchedule (W : ℤ → Set ℤ) (N : ℕ) :
    Lemma68Successive.exitSchedule W N = nextExitSchedule (fun _ => W) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    show SuccessiveExitStop.nextExit W (Lemma68Successive.exitSchedule W N) =
      SuccessiveExitStop.nextExit W (nextExitSchedule (fun _ => W) N)
    rw [ih]


/-- **hloc from printed_test_bound.** The local bound at a middle vertex `y` (PerTest68.lean:82) with the scale `r := R`
and the local window `I(B_{R/4}(vertexPoint u))`: the printed bound with constant `q₀ = 1/(288 Cd² K²)` gives the bound with
`min q₀ 1`. All hypotheses are those of `printed_test_bound` (the good-event and configuration inputs at `y`). -/
theorem hloc_of_printed {μ : Measure ℂ} [SFinite μ] {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {A : Set ℤ} {y : ℤ}
    {ε R mr s1 β c0 C Cd Cg p δ : ℝ} {z : ℂ} {Aset : Finset ℤ}
    (hap : IsAreaParametrized μ η) (hη : Continuous η) (hε : 0 < ε) (hR : 0 < R) (hR1 : R ≤ 1)
    (hmr : 0 < mr) (hC : 0 < C) (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hc0 : 0 < c0) (hc0' : c0 < 1 / 8) (hc0C : c0 ≤ Real.exp (-(2 * C)) / 16) (hεc : ε ≤ 16 * c0)
    (hp : p ≤ 3) (hRpow : R ^ p / 2 < R)
    (hmu : ENNReal.ofReal mr ≤ μ (Metric.ball (vertexPoint ε η y) (c0 * R)))
    (hfinD : (cellVertices ε η (Metric.ball (vertexPoint ε η y) (c0 * R))).Finite)
    (hfinr : (cellVertices ε η (Metric.ball (vertexPoint ε η y) R)).Finite)
    (hAs : ∀ k, k ∈ Aset ↔ k ∈ A ∩ cellVertices ε η (Metric.ball (vertexPoint ε η y) (c0 * R)))
    (hsp : ((A ∩ cellVertices ε η (Metric.ball (vertexPoint ε η y) R)).ncard : ℝ) < s1 * R ^ (2 * β) / ε)
    (hs : s1 * R ^ (2 * β) ≤ mr / 4)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ Metric.ball (vertexPoint ε η y) (R / 4)).Nonempty →
      Metric.diam (cell ε η k) ≤ c0 * R)
    (hGreenAt : ∀ b ∈ cellVertices ε η (Metric.ball (vertexPoint ε η y) (c0 * R)),
      greenKernel m (interiorCellVertices ε η (Metric.ball (vertexPoint ε η y) (R / 8))) y b ≤
          greenFn m (interiorCellVertices ε η (Metric.ball (vertexPoint ε η y) (R / 8))) y b ∧
        C⁻¹ * Real.log (if vertexPoint ε η y = vertexPoint ε η b then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η y - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (Metric.ball (vertexPoint ε η y) (R / 8))) y b)
    (hdy : Metric.diam (cell ε η y) ≤ R / 100) (hmeet : (cell ε η y ∩ Metric.sphere z (4 * R / 3)).Nonempty)
    (hδ : δ ≤ R / 100) (hμA : μ (closedAnnulus z R) ≠ ⊤)
    (hint : ∀ v ∈ Metric.ball (vertexPoint ε η y) (R / 4),
      IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) (closedAnnulus z R) μ)
    (hF : ∀ w ∈ closedAnnulus z R, ∫ u in closedAnnulus z R, (Real.log (R / ‖u - w‖) + 1) ∂μ ≤ Cg * mr)
    (hexit : exitTimeMoment m (interiorCellVertices ε η (Metric.ball (vertexPoint ε η y) (R / 4))) y 2 ≤
      ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * Cd ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) *
        (⨆ v ∈ Metric.ball (vertexPoint ε η y) (R / 4),
          ∫⁻ u in Metric.thickening δ (Metric.ball (vertexPoint ε η y) (R / 4)),
            ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ) ^ (2 : ℕ)) :
    srwLaw m y (TestBound68.stayIn (fun u => interiorCellVertices ε η (Metric.ball (vertexPoint ε η u) (R / 4))) A y) ≤
      ENNReal.ofReal (1 - min (1 / (288 * Cd ^ 2 * (Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) ^ 2)) 1 /
        (1 + Real.log (1 / R)) ^ 2) := by
  have hRr : Metric.ball (vertexPoint ε η y) (c0 * R) ⊆ Metric.ball (vertexPoint ε η y) R :=
    Metric.ball_subset_ball (by nlinarith)
  have hP := printed_test_bound (W := fun u => interiorCellVertices ε η (Metric.ball (vertexPoint ε η u) (R / 4)))
    hap hη hε hR hR1 hmr hC hCd hCg hc0 hc0' hc0C hεc hR hR1 hp hRpow hmu hfinD hfinr hRr rfl hAs hsp hs
    hdiam hGreenAt hdy hmeet hδ hμA hint hF hexit
  refine hP.trans (ENNReal.ofReal_le_ofReal ?_)
  exact sub_le_sub_left (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) 1

end S6j

end MatedCRT

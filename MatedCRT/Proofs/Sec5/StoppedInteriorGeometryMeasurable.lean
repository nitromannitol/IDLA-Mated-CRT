import MatedCRT.Proofs.Sec5.StoppedInteriorGeometryProof
import MatedCRT.Proofs.Sec1.EnvironmentScaling.PrestonPolishTransfer
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Borel obstruction matrix and analytic projection of the stopped interior geometry

Notation of the paper: `K^d = cthickening d K`, `L = int K`,
`B_δ(z)` the open ball. The paper's countable set `Q` of rational points is any dense sequence `q : ℕ → ℂ`
(`DenseRange q`) in this file.

Contents:
* `geoTerm`, `infEDist_interior_compl_eq`: for every nonempty compact `K`, `d(z, (int K)^c)` is the infimum of
  `|z - q n|` over the test points `q n ∉ K` (`(int K)^c = closure K^c`). `measurable_infDist_interior_compl`: this is
  a Borel function of `(K, z)` on `NonemptyCompacts ℂ × ℂ`.
* `ball_subset_iff_of_closed`: inclusion of an open ball in a closed set is decided by countably many test points.
* `geoBadMatrix`: the obstruction as a subset of `NonemptyCompacts ℂ × ℂ` (see
  `measurableSet_geoBadMatrix`).
* `geoBad_iff_exists_mem_geoBadMatrix`: for regular closed `K` (`closure (int K) = K`), the existential projection of
  the matrix is exactly `StoppedInteriorGeometry.GeoBad (int K) δ d` of `StoppedInteriorGeometryProof.lean`.
* `analyticSet_fst_geoBadMatrix`: the projection along `ℂ` is analytic.
* `nullMeasurableSet_geoBadEvent`: given the Polish form of Preston's theorem, the event `B_d` of a measurable random
  compact set `K` is null-measurable. `nullMeasurableSet_geoBadEvent_of_cantor` invokes the proved transfer
  `prestonAnalyticUniversallyMeasurable_of_cantor` from the two printed Preston statements.
* `tendsto_measure_geoBadEvent_zero`: `P(B_{1/(n+1)}) → 0`, for a random compact set `K`
  that is almost surely regular closed.

Topology: `NonemptyCompacts ℂ` carries Mathlib's default topology instance. Joint measurability of
`(K, z) ↦ d(z, K)` is obtained from continuity in `z` and measurability in `K`
(`measurable_uncurry_of_continuous_of_measurable`); a direct joint-continuity proof on the product was not used, since
its instance comparison (Vietoris topology against the Hausdorff metric topology) times out.

Literature inputs are explicit hypotheses only: `PrestonAnalyticCantorStmt` and `PrestonTheorem61Stmt`
(`MatedCRT/Proposed/PrestonAnalytic2008.lean`; Preston, arXiv:0809.3066v1, Theorem 7.1 and Theorem 6.1(1)).
Residual inputs not formalized here: the measurable random compact set `K` (hypothesis `hK`) and its almost sure
regularity (hypothesis `hreg`), both produced by the origin code.
-/

namespace MatedCRT
namespace StoppedInteriorGeometryBorel

open Metric Set Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

/-- The `n`-th term of the countable matrix for `d(z, (int K)^c)`: with `q n` a test point, the term is
`edist z (q n)` when `q n ∉ K` (equivalently `d(q n, K) > 0`, as `K` is closed) and `⊤` otherwise. -/
noncomputable def geoTerm (q : ℕ → ℂ) (n : ℕ) (p : NonemptyCompacts ℂ × ℂ) : ℝ≥0∞ :=
  if 0 < infDist (q n) (p.1 : Set ℂ) then edist p.2 (q n) else ⊤

/-- For a fixed point `x`, `(K, z) ↦ d(x, K)` is Borel: it is 1-Lipschitz in `K`. -/
theorem measurable_infDist_fst_const [MeasurableSpace (NonemptyCompacts ℂ)]
    [BorelSpace (NonemptyCompacts ℂ)] (x : ℂ) :
    Measurable fun p : NonemptyCompacts ℂ × ℂ => infDist x (p.1 : Set ℂ) :=
  (NonemptyCompacts.lipschitz_infDist_const x).continuous.measurable.comp measurable_fst

/-- `(K, z) ↦ d(z, K)` is Borel on `NonemptyCompacts ℂ × ℂ`: it is continuous in `z` and measurable in `K`, and the
joint measurability follows from `measurable_uncurry_of_continuous_of_measurable`. -/
theorem measurable_infDist_swap [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)] :
    Measurable fun p : NonemptyCompacts ℂ × ℂ => infDist p.2 (p.1 : Set ℂ) := by
  have hu : Measurable (Function.uncurry fun (z : ℂ) (K : NonemptyCompacts ℂ) => infDist z (K : Set ℂ)) :=
    measurable_uncurry_of_continuous_of_measurable
      (u := fun (z : ℂ) (K : NonemptyCompacts ℂ) => infDist z (K : Set ℂ))
      (fun K => Metric.continuous_infDist_pt (K : Set ℂ))
      (fun z => (NonemptyCompacts.lipschitz_infDist_const z).continuous.measurable)
  have hs : Measurable (Prod.swap : NonemptyCompacts ℂ × ℂ → ℂ × NonemptyCompacts ℂ) := measurable_swap
  have h := hu.comp hs
  exact h

theorem measurable_geoTerm [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (q : ℕ → ℂ) (n : ℕ) : Measurable (geoTerm q n) := by
  unfold geoTerm
  refine Measurable.ite ?_ (continuous_snd.edist continuous_const).measurable measurable_const
  exact measurableSet_lt measurable_const (measurable_infDist_fst_const (q n))

/-- The countable matrix for the extended distance to the complement of the interior: for every
nonempty compact `K` and every `z`, `edist(z, (int K)^c)` is the infimum over the test points outside `K`. The
proof uses that `K` is closed, so that `q n ∉ K` iff `d(q n, K) > 0`, and that `Q` is dense in the open set `K^c`,
whose closure is `(int K)^c`. -/
theorem infEDist_interior_compl_eq (q : ℕ → ℂ) (hq : DenseRange q) (K : NonemptyCompacts ℂ) (z : ℂ) :
    infEDist z (interior (K : Set ℂ))ᶜ = ⨅ n, geoTerm q n (K, z) := by
  have hKc : IsClosed (K : Set ℂ) := K.isCompact.isClosed
  have hUo : IsOpen (K : Set ℂ)ᶜ := hKc.isOpen_compl
  rw [← closure_compl]
  apply le_antisymm
  · refine le_iInf fun n => ?_
    unfold geoTerm
    split_ifs with h
    · have hnK : q n ∈ (K : Set ℂ)ᶜ := by
        intro hmem
        rw [Metric.infDist_zero_of_mem hmem] at h
        exact lt_irrefl 0 h
      exact infEDist_le_edist_of_mem (subset_closure hnK)
    · exact le_top
  · refine le_infEDist.2 fun y hy => ?_
    have hdense : (K : Set ℂ)ᶜ ⊆ closure ((K : Set ℂ)ᶜ ∩ range q) :=
      (show Dense (range q) from hq).open_subset_closure_inter hUo
    have hF : IsClosed {x : ℂ | ⨅ n, geoTerm q n (K, z) ≤ edist z x} :=
      isClosed_le continuous_const (continuous_const.edist continuous_id)
    have hsub : (K : Set ℂ)ᶜ ∩ range q ⊆ {x : ℂ | ⨅ n, geoTerm q n (K, z) ≤ edist z x} := by
      rintro x ⟨hxK, n, rfl⟩
      have hpos : 0 < infDist (q n) (K : Set ℂ) :=
        (Metric.infDist_pos_iff_notMem_closure K.nonempty).1 (by rw [hKc.closure_eq]; exact hxK)
      have hterm : geoTerm q n (K, z) = edist z (q n) := by
        simp only [geoTerm, hpos, ↓reduceIte]
      exact le_trans (iInf_le (fun m => geoTerm q m (K, z)) n) hterm.le
    exact closure_minimal hsub hF (closure_minimal hdense isClosed_closure hy)

/-- The real form of the countable matrix: `d(z, (int K)^c) = (inf_n geoTerm)` in `ℝ`. -/
theorem infDist_interior_compl_eq (q : ℕ → ℂ) (hq : DenseRange q) (K : NonemptyCompacts ℂ) (z : ℂ) :
    infDist z (interior (K : Set ℂ))ᶜ = (⨅ n, geoTerm q n (K, z)).toReal := by
  rw [Metric.infDist, infEDist_interior_compl_eq q hq K z]

/-- The distance to the complement of the interior is Borel on `NonemptyCompacts ℂ × ℂ` (the
Borel matrix). -/
theorem measurable_infDist_interior_compl [MeasurableSpace (NonemptyCompacts ℂ)]
    [BorelSpace (NonemptyCompacts ℂ)] (q : ℕ → ℂ) (hq : DenseRange q) :
    Measurable fun p : NonemptyCompacts ℂ × ℂ => infDist p.2 (interior (p.1 : Set ℂ))ᶜ := by
  have h : (fun p : NonemptyCompacts ℂ × ℂ => infDist p.2 (interior (p.1 : Set ℂ))ᶜ) =
      fun p => (⨅ n, geoTerm q n p).toReal := by
    funext p
    exact infDist_interior_compl_eq q hq p.1 p.2
  rw [h]
  exact ENNReal.measurable_toReal.comp (Measurable.iInf fun n => measurable_geoTerm q n)

/-- For `d ≥ 0` and a nonempty compact `K`, `z ∈ K^d` iff `d(z, K) ≤ d`. -/
theorem mem_cthickening_iff_infDist_le (K : NonemptyCompacts ℂ) {z : ℂ} {d : ℝ} (hd : 0 ≤ d) :
    z ∈ cthickening d (K : Set ℂ) ↔ infDist z (K : Set ℂ) ≤ d := by
  rw [mem_cthickening_iff, Metric.infDist,
    ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top K.nonempty) hd]

/-- Inclusion of an open ball in a closed set is decided by the countably many test points `q n`, which are dense
("open-ball inclusion by countable tests"). -/
theorem ball_subset_iff_of_closed (q : ℕ → ℂ) (hq : DenseRange q) {T : Set ℂ} (hT : IsClosed T)
    {z : ℂ} {δ : ℝ} : ball z δ ⊆ T ↔ ∀ n, dist (q n) z < δ → q n ∈ T := by
  constructor
  · intro h n hn
    exact h (mem_ball.2 hn)
  · intro h w hw
    have hw' : w ∈ closure (ball z δ ∩ range q) :=
      (show Dense (range q) from hq).open_subset_closure_inter isOpen_ball hw
    refine closure_minimal ?_ hT hw'
    rintro x ⟨hx, n, rfl⟩
    exact h n (mem_ball.1 hx)

/-- The Borel obstruction matrix on `NonemptyCompacts ℂ × ℂ`: the pairs `(K, z)` with `z ∈ K^d`,
`B_δ(z) ⊆ K^d` (the inclusion tested on the points `q n`) and `d(z, (int K)^c) < 3δ/4`. Here `z ∈ K^d` is written
`d(z, K) ≤ d`, which is the paper's thickening for `d ≥ 0`; the paper only uses `d = 1/(n+1) > 0`. -/
def geoBadMatrix (q : ℕ → ℂ) (δ d : ℝ) : Set (NonemptyCompacts ℂ × ℂ) :=
  {p | infDist p.2 (p.1 : Set ℂ) ≤ d ∧ (∀ n, dist (q n) p.2 < δ → infDist (q n) (p.1 : Set ℂ) ≤ d) ∧
    infDist p.2 (interior (p.1 : Set ℂ))ᶜ < 3 * δ / 4}

theorem geoBadMatrix_mono (q : ℕ → ℂ) {δ d d' : ℝ} (h : d ≤ d') :
    geoBadMatrix q δ d ⊆ geoBadMatrix q δ d' := by
  rintro p ⟨h1, h2, h3⟩
  exact ⟨h1.trans h, fun n hn => (h2 n hn).trans h, h3⟩

/-- A single countable test of `geoBadMatrix` is Borel. -/
theorem measurableSet_test [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (q : ℕ → ℂ) (n : ℕ) (δ d : ℝ) :
    MeasurableSet {p : NonemptyCompacts ℂ × ℂ | dist (q n) p.2 < δ → infDist (q n) (p.1 : Set ℂ) ≤ d} := by
  have hA : MeasurableSet {p : NonemptyCompacts ℂ × ℂ | δ ≤ dist (q n) p.2} :=
    measurableSet_le measurable_const (continuous_const.dist continuous_snd).measurable
  have hB : MeasurableSet {p : NonemptyCompacts ℂ × ℂ | infDist (q n) (p.1 : Set ℂ) ≤ d} :=
    measurableSet_le (measurable_infDist_fst_const (q n)) measurable_const
  have heq : {p : NonemptyCompacts ℂ × ℂ | dist (q n) p.2 < δ → infDist (q n) (p.1 : Set ℂ) ≤ d} =
      {p : NonemptyCompacts ℂ × ℂ | δ ≤ dist (q n) p.2} ∪
        {p : NonemptyCompacts ℂ × ℂ | infDist (q n) (p.1 : Set ℂ) ≤ d} := by
    ext p
    show (dist (q n) p.2 < δ → infDist (q n) (p.1 : Set ℂ) ≤ d) ↔
      (δ ≤ dist (q n) p.2 ∨ infDist (q n) (p.1 : Set ℂ) ≤ d)
    rw [imp_iff_not_or, not_lt]
  rw [heq]
  exact hA.union hB

/-- The Borel obstruction matrix is a Borel subset of `NonemptyCompacts ℂ × ℂ`. -/
theorem measurableSet_geoBadMatrix [MeasurableSpace (NonemptyCompacts ℂ)]
    [BorelSpace (NonemptyCompacts ℂ)] (q : ℕ → ℂ) (hq : DenseRange q) (δ d : ℝ) :
    MeasurableSet (geoBadMatrix q δ d) := by
  have h1 : MeasurableSet {p : NonemptyCompacts ℂ × ℂ | infDist p.2 (p.1 : Set ℂ) ≤ d} :=
    measurableSet_le measurable_infDist_swap measurable_const
  have h2 : MeasurableSet
      {p : NonemptyCompacts ℂ × ℂ | ∀ n, dist (q n) p.2 < δ → infDist (q n) (p.1 : Set ℂ) ≤ d} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n => measurableSet_test q n δ d
  have h3 : MeasurableSet
      {p : NonemptyCompacts ℂ × ℂ | infDist p.2 (interior (p.1 : Set ℂ))ᶜ < 3 * δ / 4} :=
    measurableSet_lt (measurable_infDist_interior_compl q hq) measurable_const
  exact h1.inter (h2.inter h3)

/-- Relation to the deterministic obstruction: for a regular closed compact `K` (`closure (int K) = K`), the
existential projection of the Borel matrix is exactly `GeoBad (int K) δ d` (with `K = closure L`,
`L = int K`, `d ≥ 0`). -/
theorem geoBad_iff_exists_mem_geoBadMatrix (K : NonemptyCompacts ℂ) (hreg : closure (interior (K : Set ℂ)) = K)
    (q : ℕ → ℂ) (hq : DenseRange q) {δ d : ℝ} (hd : 0 ≤ d) :
    StoppedInteriorGeometry.GeoBad (interior (K : Set ℂ)) δ d ↔ ∃ z, (K, z) ∈ geoBadMatrix q δ d := by
  have hT : IsClosed (cthickening d (K : Set ℂ)) := isClosed_cthickening
  unfold StoppedInteriorGeometry.GeoBad
  rw [hreg]
  constructor
  · rintro ⟨z, hz, hball, hdist⟩
    exact ⟨z, (mem_cthickening_iff_infDist_le K hd).1 hz,
      fun n hn => (mem_cthickening_iff_infDist_le K hd).1 (((ball_subset_iff_of_closed q hq hT).1 hball) n hn),
      hdist⟩
  · rintro ⟨z, h1, h2, h3⟩
    exact ⟨z, (mem_cthickening_iff_infDist_le K hd).2 h1,
      (ball_subset_iff_of_closed q hq hT).2 fun n hn => (mem_cthickening_iff_infDist_le K hd).2 (h2 n hn),
      h3⟩

/-- The projection of the Borel matrix to `NonemptyCompacts ℂ` is analytic: the image of a Borel subset of a Polish
space under a continuous map (Mathlib's `AnalyticSet`). -/
theorem analyticSet_fst_geoBadMatrix [MeasurableSpace (NonemptyCompacts ℂ)]
    [BorelSpace (NonemptyCompacts ℂ)] (q : ℕ → ℂ) (hq : DenseRange q) (δ d : ℝ) :
    AnalyticSet (Prod.fst '' geoBadMatrix q δ d) :=
  AnalyticSet.image_of_continuous
    (measurableSet_geoBadMatrix (δ := δ) (d := d) q hq).analyticSet continuous_fst

/-- The event `B_d` for a random compact set `K`: some `z` with `(K ω, z)` in the matrix. -/
def geoBadEvent {Ω : Type*} (K : Ω → NonemptyCompacts ℂ) (q : ℕ → ℂ) (δ d : ℝ) : Set Ω :=
  {ω | ∃ z, (K ω, z) ∈ geoBadMatrix q δ d}

/-- Given the Polish form `hP` of Preston's theorem (analytic sets are universally measurable), the event `B_d` is
null-measurable for a measurable random compact set `K`.
The projection is analytic (`analyticSet_fst_geoBadMatrix`) and the event is the preimage of it under `K`. -/
theorem nullMeasurableSet_geoBadEvent [MeasurableSpace (NonemptyCompacts ℂ)]
    [BorelSpace (NonemptyCompacts ℂ)] (hP : PrestonAnalyticUniversallyMeasurableStmt)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (K : Ω → NonemptyCompacts ℂ) (hK : Measurable K) (q : ℕ → ℂ) (hq : DenseRange q) (δ d : ℝ) :
    NullMeasurableSet (geoBadEvent K q δ d) P := by
  have hA : NullMeasurableSet (Prod.fst '' geoBadMatrix q δ d) (P.map K) :=
    hP (NonemptyCompacts ℂ) _ (analyticSet_fst_geoBadMatrix q hq δ d) (P.map K) inferInstance
  have hset : geoBadEvent K q δ d = K ⁻¹' (Prod.fst '' geoBadMatrix q δ d) := by
    unfold geoBadEvent
    ext ω
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨(K ω, z), hz, rfl⟩
    · rintro ⟨⟨k, z⟩, hz, hk⟩
      have hk' : k = K ω := hk
      refine ⟨z, ?_⟩
      rw [← hk']
      exact hz
  rw [hset]
  exact hA.preimage (⟨hK, rfl⟩ : MeasurePreserving K P (P.map K)).quasiMeasurePreserving

/-- The same statement, with the two printed Preston inputs as explicit hypotheses and the proved transfer
`prestonAnalyticUniversallyMeasurable_of_cantor` (Preston Theorem 7.1 and Theorem 6.1(1)). -/
theorem nullMeasurableSet_geoBadEvent_of_cantor [MeasurableSpace (NonemptyCompacts ℂ)]
    [BorelSpace (NonemptyCompacts ℂ)] (hCantor : PrestonAnalyticCantorStmt) (hT61 : PrestonTheorem61Stmt)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (K : Ω → NonemptyCompacts ℂ) (hK : Measurable K) (q : ℕ → ℂ) (hq : DenseRange q) (δ d : ℝ) :
    NullMeasurableSet (geoBadEvent K q δ d) P :=
  nullMeasurableSet_geoBadEvent (prestonAnalyticUniversallyMeasurable_of_cantor hCantor hT61) P K hK q hq δ d

/-- `P(B_{1/(n+1)}) → 0`, for a measurable random compact set `K` that is almost surely regular
closed, `K = closure (int K)`. The events decrease in `n`; their intersection is null, since on a regular closed `K`
the obstructions at meshes `1/(n+1)` eventually vanish (`StoppedInteriorGeometry.eventually_not_geoBad`). -/
theorem tendsto_measure_geoBadEvent_zero [MeasurableSpace (NonemptyCompacts ℂ)]
    [BorelSpace (NonemptyCompacts ℂ)] (hP : PrestonAnalyticUniversallyMeasurableStmt)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → NonemptyCompacts ℂ) (hK : Measurable K)
    (hreg : ∀ᵐ ω ∂P, closure (interior (K ω : Set ℂ)) = (K ω : Set ℂ))
    (q : ℕ → ℂ) (hq : DenseRange q) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P (geoBadEvent K q δ (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
  have hanti : Antitone fun n : ℕ => geoBadEvent K q δ (1 / ((n : ℝ) + 1)) := by
    intro m n hmn ω hω
    obtain ⟨z, hz⟩ := hω
    refine ⟨z, geoBadMatrix_mono q ?_ hz⟩
    apply one_div_le_one_div_of_le
    · positivity
    · have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
  have hnull : P (⋂ n : ℕ, geoBadEvent K q δ (1 / ((n : ℝ) + 1))) = 0 := by
    apply measure_mono_null (t := {ω | ¬ closure (interior (K ω : Set ℂ)) = (K ω : Set ℂ)})
    · intro ω hω hreg_ω
      have hev : ∀ᶠ n : ℕ in atTop,
          ¬ StoppedInteriorGeometry.GeoBad (interior (K ω : Set ℂ)) δ (1 / ((n : ℝ) + 1)) :=
        StoppedInteriorGeometry.eventually_not_geoBad (by rw [hreg_ω])
          ((K ω).isCompact.isBounded.subset interior_subset) hδ
      obtain ⟨n, hn⟩ := hev.exists
      obtain ⟨z, hz⟩ := Set.mem_iInter.1 hω n
      exact hn ((geoBad_iff_exists_mem_geoBadMatrix (K ω) hreg_ω q hq (by positivity)).2 ⟨z, hz⟩)
    · exact ae_iff.1 hreg
  have hlim : Tendsto (fun n : ℕ => P (geoBadEvent K q δ (1 / ((n : ℝ) + 1))))
      atTop (𝓝 (P (⋂ n : ℕ, geoBadEvent K q δ (1 / ((n : ℝ) + 1))))) :=
    tendsto_measure_iInter_atTop
      (fun n => nullMeasurableSet_geoBadEvent hP P K hK q hq δ _) hanti ⟨0, measure_ne_top P _⟩
  rw [hnull] at hlim
  exact hlim

end StoppedInteriorGeometryBorel
end MatedCRT

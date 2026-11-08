import MatedCRT.Proofs.Sec5.ConeOriginNullMeasurableProof
import Mathlib.Topology.Sets.VietorisTopology
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Random compact code from measurable rational-point events (steps2-r3:3150-3169)

Formalizes the paragraph "The random closed set and the outer-probability passage" of
`notes/wpn-steps2/steps2-r3.tex`, lines 3150-3169 (final audited draft, sha256 88dfb1f9;
audit `notes/wpn-steps2/AUDIT-steps2-r3.md`, verdict CORRECT).

Setting. `gaussRat` is the countable dense set `Q` of Gaussian rationals (`ConeOriginNull.gaussRat`).
For `z ∈ gaussRat`, `E z` is a measurable event of an arbitrary measurable space `Ω` (no completeness
is assumed). The event `ω ∈ E z` is the selection of `z`; in the paper it is the membership `z ∈ Λ_t`
(steps2-r3:3158-3161). The selected rationals of `ω` are `selectedRats E ω`.

* `codeClosure E ω` is their closure (steps2-r3:3162-3163).
* `CodeAdmissible E ω`: the selected rationals are nonempty and bounded.
* `codeCompact E ω : NonemptyCompacts ℂ` is the closure when admissible and `{0}` otherwise
  (steps2-r3:3166-3168).

Results. Open-hit events of the code are countable unions of the events `E z`
(`measurableSet_selectedRats_hit`, `measurableSet_codeClosure_hit`); admissibility is a countable
Borel test (`measurableSet_codeAdmissible`); the Hausdorff-ball events of the code are measurable
(`measurableSet_hausdorffEDist_lt`, through finite nets of the compact target); hence `codeCompact E` is
Borel (`measurable_codeCompact`). Recovery: `codeCompact_eq_closure_of_membership` and its almost-sure form
`ae_codeCompact_eq_closure` give `closure Λ` when the events agree with rational membership in a bounded,
nonempty, open `Λ`.

Not proved here: the measurable versions of the membership events. The paper obtains them from the origin
code of Section 5 (`eq:clusterpointcode`, steps2-r3:3150-3157). They enter only as the hypotheses `hE`
and `hae` below.
-/

open MeasureTheory Set Filter Topology TopologicalSpace Metric
open scoped ENNReal NNReal

namespace MatedCRT
namespace StoppedCompactCode

open MatedCRT.ConeOriginNull (gaussRat gaussRat_countable gaussRat_dense)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The selected Gaussian rationals of `ω`: the `z ∈ gaussRat` with `ω ∈ E z`. -/
def selectedRats (E : ℂ → Set Ω) (ω : Ω) : Set ℂ :=
  {z | z ∈ gaussRat ∧ ω ∈ E z}

/-- The random closed set: the closure of the selected Gaussian rationals (steps2-r3:3162-3163). -/
def codeClosure (E : ℂ → Set Ω) (ω : Ω) : Set ℂ :=
  closure (selectedRats E ω)

/-- Admissibility: the selected rationals are nonempty and bounded (steps2-r3:3166-3168). -/
def CodeAdmissible (E : ℂ → Set Ω) (ω : Ω) : Prop :=
  (selectedRats E ω).Nonempty ∧ Bornology.IsBounded (selectedRats E ω)

/-- Open-hit events of the selected rationals: `ω` selects a point of `O`. This is the countable
union of the events `E z` over `z ∈ gaussRat ∩ O` (steps2-r3:3164-3165). -/
theorem measurableSet_selectedRats_hit {E : ℂ → Set Ω} (hE : ∀ z ∈ gaussRat, MeasurableSet (E z))
    (O : Set ℂ) : MeasurableSet {ω | (selectedRats E ω ∩ O).Nonempty} := by
  have hset : {ω | (selectedRats E ω ∩ O).Nonempty} = ⋃ z ∈ gaussRat ∩ O, E z := by
    ext ω
    constructor
    · rintro ⟨z, ⟨hzg, hωz⟩, hzO⟩
      exact mem_iUnion₂.2 ⟨z, ⟨hzg, hzO⟩, hωz⟩
    · intro hω
      obtain ⟨z, ⟨hzg, hzO⟩, hωz⟩ := mem_iUnion₂.1 hω
      exact ⟨z, ⟨hzg, hωz⟩, hzO⟩
  rw [hset]
  exact MeasurableSet.biUnion (gaussRat_countable.mono inter_subset_left) fun z hz => hE z hz.1

/-- Open-hit events of the closed code: `closure` does not change the hits of an open set. -/
theorem measurableSet_codeClosure_hit {E : ℂ → Set Ω} (hE : ∀ z ∈ gaussRat, MeasurableSet (E z))
    {O : Set ℂ} (hO : IsOpen O) : MeasurableSet {ω | (codeClosure E ω ∩ O).Nonempty} := by
  have hset : {ω | (codeClosure E ω ∩ O).Nonempty} = {ω | (selectedRats E ω ∩ O).Nonempty} := by
    ext ω
    simp only [Set.mem_ofPred_eq, codeClosure]
    exact closure_inter_open_nonempty_iff hO
  rw [hset]
  exact measurableSet_selectedRats_hit hE O

/-- Nonemptiness of the selected rationals is a countable Borel test. -/
theorem measurableSet_selectedRats_nonempty {E : ℂ → Set Ω}
    (hE : ∀ z ∈ gaussRat, MeasurableSet (E z)) :
    MeasurableSet {ω | (selectedRats E ω).Nonempty} := by
  simpa only [inter_univ] using measurableSet_selectedRats_hit hE univ

/-- Boundedness of the selected rationals is a countable Borel test: the complement of
`⋃ n, ⋂ z ∈ gaussRat ∩ {‖z‖ > n}, (E z)ᶜ` (steps2-r3:3166-3168). -/
theorem measurableSet_selectedRats_bounded {E : ℂ → Set Ω}
    (hE : ∀ z ∈ gaussRat, MeasurableSet (E z)) :
    MeasurableSet {ω | Bornology.IsBounded (selectedRats E ω)} := by
  have hset : {ω | Bornology.IsBounded (selectedRats E ω)} =
      ⋃ n : ℕ, ⋂ z ∈ gaussRat ∩ {z : ℂ | (n : ℝ) < ‖z‖}, (E z)ᶜ := by
    ext ω
    constructor
    · intro hb
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (show Bornology.IsBounded (selectedRats E ω) from hb)
      obtain ⟨n, hn⟩ := exists_nat_gt C
      refine mem_iUnion.2 ⟨n, mem_iInter₂.2 fun z hz hωz => ?_⟩
      have h1 : (n : ℝ) < ‖z‖ := hz.2
      have h2 : ‖z‖ ≤ C := hC z ⟨hz.1, hωz⟩
      linarith
    · intro hω
      obtain ⟨n, hn⟩ := mem_iUnion.1 hω
      refine show Bornology.IsBounded (selectedRats E ω) from
        isBounded_iff_forall_norm_le.2 ⟨n, fun z hz => ?_⟩
      by_contra hlt
      exact mem_iInter₂.1 hn z ⟨hz.1, not_le.1 hlt⟩ hz.2
  rw [hset]
  exact MeasurableSet.iUnion fun n =>
    MeasurableSet.biInter (gaussRat_countable.mono inter_subset_left) fun z hz => (hE z hz.1).compl

/-- Admissibility of the code is a countable Borel test: it defines the exceptional set on which
the code is replaced by `{0}` (steps2-r3:3166-3168). -/
theorem measurableSet_codeAdmissible {E : ℂ → Set Ω} (hE : ∀ z ∈ gaussRat, MeasurableSet (E z)) :
    MeasurableSet {ω | CodeAdmissible E ω} :=
  (measurableSet_selectedRats_nonempty hE).inter (measurableSet_selectedRats_bounded hE)

omit [MeasurableSpace Ω] in
/-- The closure of an admissible code is compact (closed and bounded in `ℂ`). -/
theorem isCompact_codeClosure {E : ℂ → Set Ω} {ω : Ω} (h : CodeAdmissible E ω) :
    IsCompact (codeClosure E ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure h.2.closure

open Classical in
/-- The compact code as an element of `NonemptyCompacts ℂ`: the closure of the selected Gaussian
rationals when admissible, and `{0}` on the exceptional set (steps2-r3:3166-3168). -/
noncomputable def codeCompact (E : ℂ → Set Ω) (ω : Ω) : NonemptyCompacts ℂ :=
  if h : CodeAdmissible E ω then
    ⟨⟨codeClosure E ω, isCompact_codeClosure h⟩, h.1.closure⟩
  else ⟨⟨{0}, isCompact_singleton⟩, Set.singleton_nonempty _⟩

omit [MeasurableSpace Ω] in
theorem coe_codeCompact_of_admissible {E : ℂ → Set Ω} {ω : Ω} (h : CodeAdmissible E ω) :
    ((codeCompact E ω : NonemptyCompacts ℂ) : Set ℂ) = codeClosure E ω := by
  unfold codeCompact
  split_ifs
  rfl

omit [MeasurableSpace Ω] in
theorem coe_codeCompact_of_not_admissible {E : ℂ → Set Ω} {ω : Ω} (h : ¬ CodeAdmissible E ω) :
    ((codeCompact E ω : NonemptyCompacts ℂ) : Set ℂ) = {0} := by
  unfold codeCompact
  split_ifs
  rfl

/-- The edistance of `NonemptyCompacts ℂ` is the Hausdorff edistance of the underlying sets. -/
theorem edist_nonemptyCompacts (K L : NonemptyCompacts ℂ) :
    edist K L = hausdorffEDist (K : Set ℂ) (L : Set ℂ) :=
  rfl

/-- Rational approximation in `ℝ≥0∞` by values `ENNReal.ofReal q`, `q ∈ ℚ`. -/
theorem exists_rat_ofReal_btwn {x y : ℝ≥0∞} (h : x < y) :
    ∃ q : ℚ, x < ENNReal.ofReal (q : ℝ) ∧ ENNReal.ofReal (q : ℝ) < y := by
  obtain ⟨q, -, hxq, hqy⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
  exact ⟨q, hxq, hqy⟩

/-- A finite `δ`-net of a compact set, contained in the set: the covering balls of the
compact set (finite cover, Mathlib `finite_cover_balls_of_compact`). -/
theorem exists_codeNet {L : Set ℂ} (hL : IsCompact L) (δ : ℝ) :
    ∃ D : Set ℂ, D ⊆ L ∧ D.Finite ∧ (0 < δ → L ⊆ ⋃ d ∈ D, ball d δ) := by
  by_cases hδ : 0 < δ
  · obtain ⟨t, htL, htf, hcov⟩ := finite_cover_balls_of_compact hL hδ
    exact ⟨t, htL, htf, fun _ => hcov⟩
  · exact ⟨∅, empty_subset _, finite_empty, fun h => absurd h hδ⟩

/-- Rational parameters `(a, c)` of a Hausdorff-ball event of radius `r`: `0 < a < c` and `ofReal c < r`. -/
def HausdorffPair (r : ℝ≥0∞) (p : ℚ × ℚ) : Prop :=
  (0 : ℝ) < (p.1 : ℝ) ∧ (p.1 : ℝ) < (p.2 : ℝ) ∧ ENNReal.ofReal (p.2 : ℝ) < r

/-- Deterministic characterization of the Hausdorff-ball event through rational parameters and a
finite net `D p ⊆ L` of the compact target `L` (Armitage-Gardiner style open-hit description). -/
theorem hausdorffEDist_lt_iff_codeNet {K L : Set ℂ} {r : ℝ≥0∞} (D : ℚ × ℚ → Set ℂ)
    (hDL : ∀ p, D p ⊆ L)
    (hDcov : ∀ p : ℚ × ℚ, 0 < (p.2 : ℝ) - (p.1 : ℝ) →
      L ⊆ ⋃ d ∈ D p, ball d ((p.2 : ℝ) - (p.1 : ℝ))) :
    hausdorffEDist K L < r ↔ ∃ p : ℚ × ℚ, HausdorffPair r p ∧
      (∀ x ∈ K, infEDist x L ≤ ENNReal.ofReal (p.1 : ℝ)) ∧
      ∀ d ∈ D p, ∃ x ∈ K, dist x d < (p.1 : ℝ) := by
  constructor
  · intro h
    obtain ⟨c, hhc, hcr⟩ := exists_rat_ofReal_btwn h
    obtain ⟨a, hha, hac⟩ := exists_rat_ofReal_btwn hhc
    have hac' : (a : ℝ) < (c : ℝ) := (ENNReal.ofReal_lt_ofReal_iff'.1 hac).1
    have ha0 : (0 : ℝ) < (a : ℝ) := by
      have : (0 : ℝ≥0∞) < ENNReal.ofReal (a : ℝ) := lt_of_le_of_lt zero_le hha
      exact ENNReal.ofReal_pos.1 this
    refine ⟨(a, c), ⟨ha0, hac', hcr⟩, fun x hx => ?_, fun d hd => ?_⟩
    · exact (infEDist_le_hausdorffEDist_of_mem hx).trans hha.le
    · have hdL : d ∈ L := hDL (a, c) hd
      have hsymm : hausdorffEDist L K < ENNReal.ofReal (a : ℝ) := by
        rw [hausdorffEDist_comm]
        exact hha
      obtain ⟨y, hyK, hdy⟩ := exists_edist_lt_of_hausdorffEDist_lt hdL hsymm
      refine ⟨y, hyK, ?_⟩
      rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff ha0] at hdy
      rw [dist_comm]
      exact hdy
  · rintro ⟨p, ⟨-, hpc, hpr⟩, H1, H2⟩
    have hδ : (0 : ℝ) < (p.2 : ℝ) - (p.1 : ℝ) := sub_pos.2 hpc
    have hle : hausdorffEDist K L ≤ ENNReal.ofReal (p.2 : ℝ) := by
      apply hausdorffEDist_le_of_infEDist
      · intro x hx
        exact (H1 x hx).trans (ENNReal.ofReal_le_ofReal hpc.le)
      · intro y hy
        obtain ⟨d, hdD, hyd⟩ := mem_iUnion₂.1 (hDcov p hδ hy)
        obtain ⟨x, hxK, hdx⟩ := H2 d hdD
        refine (infEDist_le_edist_of_mem hxK).trans ?_
        rw [edist_dist]
        apply ENNReal.ofReal_le_ofReal
        have h1 : dist y x ≤ dist y d + dist d x := dist_triangle y d x
        have h2 : dist y d < (p.2 : ℝ) - (p.1 : ℝ) := hyd
        have h3 : dist d x < (p.1 : ℝ) := by
          rw [dist_comm]
          exact hdx
        linarith
    exact lt_of_le_of_lt hle hpr

/-- `{ω | ∀ x ∈ codeClosure, infEDist x L ≤ a}` is the complement of an open-hit event: the
open set `{x | a < infEDist x L}` is hit by the closure iff it is hit by the selected rationals. -/
theorem measurableSet_forall_codeClosure_infEDist {E : ℂ → Set Ω}
    (hE : ∀ z ∈ gaussRat, MeasurableSet (E z)) (L : Set ℂ) (a : ℝ) :
    MeasurableSet {ω | ∀ x ∈ codeClosure E ω, infEDist x L ≤ ENNReal.ofReal a} := by
  have hO : IsOpen {x : ℂ | ENNReal.ofReal a < infEDist x L} :=
    isOpen_lt continuous_const continuous_infEDist
  have key : ∀ ω, (∀ x ∈ codeClosure E ω, infEDist x L ≤ ENNReal.ofReal a) ↔
      ¬ (selectedRats E ω ∩ {x : ℂ | ENNReal.ofReal a < infEDist x L}).Nonempty := by
    intro ω
    rw [← closure_inter_open_nonempty_iff hO]
    constructor
    · rintro h ⟨x, hxc, hxO⟩
      exact (not_le.2 hxO) (h x hxc)
    · intro h x hx
      by_contra hlt
      exact h ⟨x, hx, not_le.1 hlt⟩
  have hset : {ω | ∀ x ∈ codeClosure E ω, infEDist x L ≤ ENNReal.ofReal a} =
      {ω | (selectedRats E ω ∩ {x : ℂ | ENNReal.ofReal a < infEDist x L}).Nonempty}ᶜ := by
    ext ω
    exact key ω
  rw [hset]
  exact (measurableSet_selectedRats_hit hE _).compl

/-- `{ω | ∃ x ∈ codeClosure, dist x d < a}` is an open-hit event of the selected rationals. -/
theorem measurableSet_exists_codeClosure_dist {E : ℂ → Set Ω}
    (hE : ∀ z ∈ gaussRat, MeasurableSet (E z)) (d : ℂ) (a : ℝ) :
    MeasurableSet {ω | ∃ x ∈ codeClosure E ω, dist x d < a} := by
  have hset : {ω | ∃ x ∈ codeClosure E ω, dist x d < a} =
      {ω | (selectedRats E ω ∩ ball d a).Nonempty} := by
    ext ω
    exact closure_inter_open_nonempty_iff (Metric.isOpen_ball (x := d) (ε := a))
  rw [hset]
  exact measurableSet_selectedRats_hit hE _

/-- The Hausdorff-ball event `{ω | hausdorffEDist (codeClosure ω) L < r}` of a compact target `L`
is measurable: a countable union over rational pairs of an intersection of a closed-complement
event and finitely many open-hit events. -/
theorem measurableSet_hausdorffEDist_lt {E : ℂ → Set Ω} (hE : ∀ z ∈ gaussRat, MeasurableSet (E z))
    {L : Set ℂ} (hL : IsCompact L) (r : ℝ≥0∞) :
    MeasurableSet {ω | hausdorffEDist (codeClosure E ω) L < r} := by
  have hnet : ∀ p : ℚ × ℚ, ∃ D : Set ℂ, D ⊆ L ∧ D.Finite ∧
      (0 < (p.2 : ℝ) - (p.1 : ℝ) → L ⊆ ⋃ d ∈ D, ball d ((p.2 : ℝ) - (p.1 : ℝ))) :=
    fun p => exists_codeNet hL _
  choose D hDL hDf hDcov using hnet
  have hset : {ω | hausdorffEDist (codeClosure E ω) L < r} =
      ⋃ p ∈ {p : ℚ × ℚ | HausdorffPair r p},
        ({ω | ∀ x ∈ codeClosure E ω, infEDist x L ≤ ENNReal.ofReal (p.1 : ℝ)} ∩
          ⋂ d ∈ D p, {ω | ∃ x ∈ codeClosure E ω, dist x d < (p.1 : ℝ)}) := by
    ext ω
    have key := hausdorffEDist_lt_iff_codeNet (K := codeClosure E ω) (r := r) D hDL hDcov
    simp only [Set.mem_ofPred_eq, mem_iUnion₂, mem_inter_iff, mem_iInter₂, exists_prop]
    exact key
  rw [hset]
  refine MeasurableSet.biUnion (Set.to_countable _) fun p _ => MeasurableSet.inter
    (measurableSet_forall_codeClosure_infEDist hE L _) ?_
  exact MeasurableSet.biInter (hDf p).countable fun d _ =>
    measurableSet_exists_codeClosure_dist hE d _

/-- The preimage of a ball of `NonemptyCompacts ℂ`: admissible outcomes compare the closure with the
target, exceptional outcomes compare `{0}` with the target. -/
theorem measurableSet_codeCompact_ball {E : ℂ → Set Ω} (hE : ∀ z ∈ gaussRat, MeasurableSet (E z))
    (L : NonemptyCompacts ℂ) (r : ℝ≥0∞) :
    MeasurableSet (codeCompact E ⁻¹' Metric.eball L r) := by
  have hset : codeCompact E ⁻¹' Metric.eball L r =
      ({ω | CodeAdmissible E ω} ∩ {ω | hausdorffEDist (codeClosure E ω) (L : Set ℂ) < r}) ∪
        ({ω | ¬ CodeAdmissible E ω} ∩ {_ω | hausdorffEDist ({0} : Set ℂ) (L : Set ℂ) < r}) := by
    ext ω
    rw [mem_preimage, Metric.mem_eball, edist_nonemptyCompacts]
    by_cases h : CodeAdmissible E ω
    · rw [coe_codeCompact_of_admissible h]
      simp [h]
    · rw [coe_codeCompact_of_not_admissible h]
      simp [h]
  rw [hset]
  exact MeasurableSet.union
    (MeasurableSet.inter (measurableSet_codeAdmissible hE)
      (measurableSet_hausdorffEDist_lt hE L.isCompact r))
    (MeasurableSet.inter (measurableSet_codeAdmissible hE).compl (MeasurableSet.const _))

open Classical in
/-- The countable family of balls used for the Lindelöf argument: the ball of rational radius around
the centre, kept only when it lies in the open set `U`. -/
noncomputable def ballCover (U : Set (NonemptyCompacts ℂ)) (i : NonemptyCompacts ℂ × ℚ) :
    Set (NonemptyCompacts ℂ) :=
  if Metric.eball i.1 (ENNReal.ofReal (i.2 : ℝ)) ⊆ U then
    Metric.eball i.1 (ENNReal.ofReal (i.2 : ℝ))
  else ∅

theorem ballCover_isOpen (U : Set (NonemptyCompacts ℂ)) (i : NonemptyCompacts ℂ × ℚ) :
    IsOpen (ballCover U i) := by
  unfold ballCover
  split_ifs
  · exact Metric.isOpen_eball
  · exact isOpen_empty

theorem ballCover_subset (U : Set (NonemptyCompacts ℂ)) (i : NonemptyCompacts ℂ × ℚ) :
    ballCover U i ⊆ U := by
  unfold ballCover
  split_ifs with h
  · exact h
  · exact empty_subset _

theorem ballCover_cover {U : Set (NonemptyCompacts ℂ)} (hU : IsOpen U) :
    U = ⋃ i, ballCover U i := by
  ext x
  constructor
  · intro hx
    obtain ⟨ε, hε, hεU⟩ := EMetric.isOpen_iff.1 hU x hx
    obtain ⟨q, hq0, hqε⟩ := exists_rat_ofReal_btwn hε
    have hsub : Metric.eball x (ENNReal.ofReal (q : ℝ)) ⊆ U :=
      (Metric.eball_subset_eball hqε.le).trans hεU
    refine mem_iUnion.2 ⟨(x, q), ?_⟩
    simp only [ballCover, hsub, ↓reduceIte]
    exact Metric.mem_eball_self hq0
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    exact ballCover_subset U i hi

theorem measurableSet_codeCompact_preimage_ballCover {E : ℂ → Set Ω}
    (hE : ∀ z ∈ gaussRat, MeasurableSet (E z)) (U : Set (NonemptyCompacts ℂ))
    (i : NonemptyCompacts ℂ × ℚ) :
    MeasurableSet (codeCompact E ⁻¹' ballCover U i) := by
  unfold ballCover
  split_ifs
  · exact measurableSet_codeCompact_ball hE i.1 (ENNReal.ofReal (i.2 : ℝ))
  · rw [preimage_empty]
    exact MeasurableSet.empty

/-- The random compact code is Borel: `codeCompact E : Ω → NonemptyCompacts ℂ` is measurable for the Borel
σ-algebra of the Hausdorff (Vietoris) topology (steps2-r3:3166-3169). -/
theorem measurable_codeCompact [MeasurableSpace (NonemptyCompacts ℂ)]
    [BorelSpace (NonemptyCompacts ℂ)] {E : ℂ → Set Ω}
    (hE : ∀ z ∈ gaussRat, MeasurableSet (E z)) : Measurable (codeCompact E) := by
  refine measurable_of_isOpen fun U hU => ?_
  obtain ⟨T, hT, hTU⟩ := isOpen_iUnion_countable (ballCover U) fun i => ballCover_isOpen U i
  have hUT : U = ⋃ i ∈ T, ballCover U i := by
    rw [hTU]
    exact ballCover_cover hU
  rw [hUT, preimage_iUnion₂]
  exact MeasurableSet.biUnion hT fun i _ => measurableSet_codeCompact_preimage_ballCover hE U i

omit [MeasurableSpace Ω] in
/-- Recovery: if the membership events agree with rational membership in a bounded nonempty open `Λ`,
the code is admissible and equals `closure Λ` (steps2-r3:3162-3163). -/
theorem codeCompact_eq_closure_of_membership {E : ℂ → Set Ω} {Λ : Set ℂ} (hΛo : IsOpen Λ)
    (hΛb : Bornology.IsBounded Λ) (hΛne : Λ.Nonempty) {ω : Ω}
    (hω : ∀ z ∈ gaussRat, ω ∈ E z ↔ z ∈ Λ) :
    ((codeCompact E ω : NonemptyCompacts ℂ) : Set ℂ) = closure Λ := by
  have hsel : selectedRats E ω = gaussRat ∩ Λ := by
    ext z
    constructor
    · rintro ⟨hzg, hωz⟩
      exact ⟨hzg, (hω z hzg).1 hωz⟩
    · rintro ⟨hzg, hzΛ⟩
      exact ⟨hzg, (hω z hzg).2 hzΛ⟩
  have hΛsub : Λ ⊆ closure (gaussRat ∩ Λ) := by
    rw [inter_comm]
    exact gaussRat_dense.open_subset_closure_inter hΛo
  have hadm : CodeAdmissible E ω := by
    unfold CodeAdmissible
    rw [hsel]
    exact ⟨closure_nonempty_iff.1 (hΛne.mono hΛsub), hΛb.subset inter_subset_right⟩
  rw [coe_codeCompact_of_admissible hadm]
  unfold codeClosure
  rw [hsel]
  exact le_antisymm (closure_mono inter_subset_right) (closure_minimal hΛsub isClosed_closure)

/-- Almost-sure recovery of `closure Λ` under the almost-sure agreement of the countably many
membership events (steps2-r3:3158-3161). -/
theorem ae_codeCompact_eq_closure {μ : Measure Ω} {E : ℂ → Set Ω} {Λ : Set ℂ} (hΛo : IsOpen Λ)
    (hΛb : Bornology.IsBounded Λ) (hΛne : Λ.Nonempty)
    (hae : ∀ᵐ ω ∂μ, ∀ z ∈ gaussRat, ω ∈ E z ↔ z ∈ Λ) :
    ∀ᵐ ω ∂μ, ((codeCompact E ω : NonemptyCompacts ℂ) : Set ℂ) = closure Λ :=
  hae.mono fun _ hω => codeCompact_eq_closure_of_membership hΛo hΛb hΛne hω

end StoppedCompactCode
end MatedCRT

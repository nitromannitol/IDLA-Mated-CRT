import MatedCRT.FirstPass.Derived.GMS21UniformStartOfVertexAnnulus
import MatedCRT.FirstPass.Derived.GMS21AnnulusLocality
import MatedCRT.FirstPass.Derived.GMS21UniformAbsoluteContinuity
import MatedCRT.FirstPass.Derived.InterpolatedLawWiring
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellIntegral
import MatedCRT.Proofs.Infra.RandomWalk
import LatticeProb.Prob.ProbabilityMeasureDistance
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws

/-!
# Local cell configurations near an annulus and the transfer by Lemma 3.3

In the proof of Gwynne–Miller–Sheffield (arXiv:1705.11161), Theorem 3.4, case 1, the comparison of the embedded walk
with Brownian motion on an annulus `V = B_R(0) \ closedBall 0 α` is transferred from the `0`-quantum cone to the
`γ`-quantum cone by Lemma 3.3: the laws of the cell configurations near `V` are uniformly mutually absolutely
continuous as `n → ∞`. The cells of the mated-CRT map are determined near `V` only up to index shifts, which may
differ between visits of the curve to `V`; the configuration is therefore taken without labels.

The local configuration of embedded data `(v, m)` (vertex points and edge multiplicities) near `V` is the list, in
increasing order of the labels, of the vertices whose points lie in `V` and of their neighbours, with their points and
the edge multiplicities between them (`localConfig`); it forgets the labels and the gaps between them. This file proves
that the comparison at the vertices on the annulus (`vertexAnnulusLPData`) is a measurable function of this local
configuration whenever the set of these vertices is finite (`mem_vertexLPGood_iff_localConfig`): the walk from a
vertex of `V`, stopped at its exit from `V`, only uses the rows of the multiplicities at the vertices of `V`, and its
law is invariant under relabelling (`GMS21AnnulusLocality`). Hence uniform absolute continuity of the laws of the local
configurations transfers vanishing probabilities of failure of the comparison
(`tendsto_map_vertexAnnulusLPData_compl_of_localConfig`).

## Main definitions

* `vertexData`: the vertex points `η(ε k)` and the multiplicities.
* `vertexLPGood`: the comparison at the vertices for embedded data; `vertexAnnulusLPData` is its preimage.
* `localVertices`, `localConfig`: the vertices of `V` with their neighbours, and the local configuration.
* `localLPGood`: the comparison at the vertices computed from a local configuration.
* `LocalConfigUniformlyMutuallyAbsolutelyContinuous`: the conclusion of Lemma 3.3 of arXiv:1705.11161 for the local
  configurations near annuli.

## Main results

* `mem_vertexLPGood_iff_localConfig`, `measurableSet_localLPGood`, `measurable_localConfig`.
* `tendsto_map_vertexAnnulusLPData_compl_of_localConfig`: the transfer of vanishing probabilities.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open StopAtExitLevyProkhorov

/-! ### Embedded data and the comparison at the vertices -/

/-- The embedded data at mesh `ε`: the vertex points `η(ε k)` and the edge multiplicities. -/
def vertexData (ε : ℝ) (d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : (ℤ → ℂ) × (ℤ → ℤ → ℕ) :=
  (vertexPoint ε d.1, d.2)

theorem measurable_vertexData (ε : ℝ) : Measurable (vertexData ε) := by
  unfold vertexData
  refine Measurable.prodMk ?_ measurable_snd
  exact measurable_pi_iff.2 fun k => (continuous_eval_const (ε * k)).measurable.comp measurable_fst

/-- The comparison at the vertices for embedded data `(v, m)` on an open set `V`: for every vertex `x` with
`v x ∈ closedBall 0 ρ \ B_b(0)`, the laws of the curve classes of the walk of `m` from `x`, embedded by `v` and
interpolated, and of planar Brownian motion from `v x`, both stopped at their exits from `V`, are at Lévy–Prokhorov
distance less than `c`. -/
def vertexLPGood (V : Set ℂ) (b ρ c : ℝ) : Set ((ℤ → ℂ) × (ℤ → ℤ → ℕ)) :=
  {d | ∀ x : ℤ, d.1 x ∉ ball (0 : ℂ) b → d.1 x ∈ closedBall (0 : ℂ) ρ →
    levyProkhorovEDist ((srwLaw d.2 x).map fun w => stoppedExitCurve V (interpPathCM d.1 zero_le_one w))
      ((planarBrownianMotion (d.1 x)).map (stoppedExitCurve V)) < ENNReal.ofReal c}

theorem vertexAnnulusLPData_eq_preimage (ε α b ρ R c : ℝ) :
    vertexAnnulusLPData ε α b ρ R c =
      vertexData ε ⁻¹' vertexLPGood (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) b ρ c :=
  rfl

/-! ### The local configuration -/

/-- The vertices whose points lie in `V`, together with their neighbours. -/
def localVertices (V : Set ℂ) (d : (ℤ → ℂ) × (ℤ → ℤ → ℕ)) : Set ℤ :=
  {y | d.1 y ∈ V ∨ ∃ x, d.1 x ∈ V ∧ d.2 x y ≠ 0}

/-- Local configurations: the number of vertices, their points and the multiplicities between them, listed in
increasing order of the labels (entries beyond the number of vertices are `0`). -/
abbrev LocalConfig : Type := ℕ × (ℕ → ℂ) × (ℕ → ℕ → ℕ)

/-- The configuration of the vertices of a finite set `F` of labels, listed in increasing order. -/
noncomputable def localConfigOf (F : Finset ℤ) (d : (ℤ → ℂ) × (ℤ → ℤ → ℕ)) : LocalConfig :=
  (F.card, fun k => if hk : k < F.card then d.1 (F.orderEmbOfFin rfl ⟨k, hk⟩) else 0,
    fun k l => if hk : k < F.card then
      if hl : l < F.card then d.2 (F.orderEmbOfFin rfl ⟨k, hk⟩) (F.orderEmbOfFin rfl ⟨l, hl⟩) else 0
    else 0)

open Classical in
/-- The vertices of `V` and their neighbours as a finite set (empty if there are infinitely many). -/
noncomputable def localFinset (V : Set ℂ) (d : (ℤ → ℂ) × (ℤ → ℤ → ℕ)) : Finset ℤ :=
  if h : (localVertices V d).Finite then h.toFinset else ∅

/-- **The local configuration near `V`**: the vertices whose points lie in `V` and their neighbours, listed in
increasing order of the labels, with their points and the edge multiplicities between them. -/
noncomputable def localConfig (V : Set ℂ) (d : (ℤ → ℂ) × (ℤ → ℤ → ℕ)) : LocalConfig :=
  localConfigOf (localFinset V d) d

theorem localConfigOf_point (F : Finset ℤ) (d : (ℤ → ℂ) × (ℤ → ℤ → ℕ)) (k : ℕ) (hk : k < F.card) :
    (localConfigOf F d).2.1 k = d.1 (F.orderEmbOfFin rfl ⟨k, hk⟩) := by
  show (if h : k < F.card then d.1 (F.orderEmbOfFin rfl ⟨k, h⟩) else 0) = _
  rw [dite_eq_left hk]

/-- The multigraph of a configuration on the labels `0, …, N - 1`. -/
def reconMult (y : LocalConfig) : ℤ → ℤ → ℕ := fun a b =>
  if 0 ≤ a ∧ 0 ≤ b ∧ a.toNat < y.1 ∧ b.toNat < y.1 then y.2.2 a.toNat b.toNat else 0

/-- The points of a configuration on the labels `0, …, N - 1`. -/
def reconPoint (y : LocalConfig) : ℤ → ℂ := fun a => y.2.1 a.toNat

/-- The comparison at the vertices computed from a local configuration. -/
def localLPGood (V : Set ℂ) (b ρ c : ℝ) : Set LocalConfig :=
  {y | ∀ k : ℕ, k < y.1 → y.2.1 k ∉ ball (0 : ℂ) b → y.2.1 k ∈ closedBall (0 : ℂ) ρ →
    levyProkhorovEDist ((srwLaw (reconMult y) k).map fun w =>
        stoppedExitCurve V (interpPathCM (reconPoint y) zero_le_one w))
      ((planarBrownianMotion (y.2.1 k)).map (stoppedExitCurve V)) < ENNReal.ofReal c}

/-! ### The walk on a local configuration -/

/-- The interpolated path depends only on the points along the walk. -/
theorem interpPathCM_congr_points {v v' : ℤ → ℂ} {m : ℝ} (hm : 0 ≤ m) {w : ℕ → ℤ}
    (h : ∀ n, v (w n) = v' (w n)) : interpPathCM v hm w = interpPathCM v' hm w := by
  have hf : (fun k => v (w k)) = fun k => v' (w k) := funext h
  refine ContinuousMap.ext fun t => ?_
  change linInterp (fun k => v (w k)) (m * (t : ℝ)) = linInterp (fun k => v' (w k)) (m * (t : ℝ))
  rw [hf]

/-- The walk on the multigraph of a configuration started from a label `k < N` stays in `0, …, N - 1`. -/
theorem ae_reconMult_range (y : LocalConfig) (k : ℕ) (hk : k < y.1) :
    ∀ᵐ w ∂srwLaw (reconMult y) k, ∀ n, 0 ≤ w n ∧ (w n).toNat < y.1 := by
  filter_upwards [srwLaw_ae_start (reconMult y) k, srwLaw_ae_step (reconMult y) k] with w h0 hstep
  intro n
  induction n with
  | zero =>
    rw [h0]
    exact ⟨by positivity, by rw [Int.toNat_natCast]; exact hk⟩
  | succ n ih =>
    rcases hstep n with h | h
    · rw [h]; exact ih
    · unfold reconMult at h
      split_ifs at h with hc
      · exact ⟨hc.2.1, hc.2.2.2⟩
      · exact absurd rfl h

open Classical in
/-- A permutation of `ℤ` sending `k < card F` to the `k`-th element of `F` in increasing order. -/
theorem exists_equiv_orderEmbOfFin (F : Finset ℤ) :
    ∃ e : ℤ ≃ ℤ, (∀ (k : ℕ) (hk : k < F.card), e k = F.orderEmbOfFin rfl ⟨k, hk⟩) ∧
      ∀ a : ℤ, e a ∈ F → 0 ≤ a ∧ a.toNat < F.card := by
  let p : ℤ → Prop := fun a => 0 ≤ a ∧ a.toNat < F.card
  let f : {a // p a} → {y // y ∈ F} := fun a =>
    ⟨F.orderEmbOfFin rfl ⟨a.1.toNat, a.2.2⟩, F.orderEmbOfFin_mem rfl _⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, ha⟩ ⟨a', ha'⟩ h
      have h1 : (⟨a.toNat, ha.2⟩ : Fin F.card) = ⟨a'.toNat, ha'.2⟩ :=
        (F.orderEmbOfFin rfl).injective (congrArg Subtype.val h)
      have h2 : a.toNat = a'.toNat := congrArg Fin.val h1
      apply Subtype.ext
      change a = a'
      rw [← Int.toNat_of_nonneg ha.1, ← Int.toNat_of_nonneg ha'.1, h2]
    · rintro ⟨y, hy⟩
      have hy' : y ∈ Set.range (F.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact hy
      obtain ⟨i, hi⟩ := hy'
      have hp : p (i : ℤ) := ⟨by positivity, by rw [Int.toNat_natCast]; exact i.2⟩
      refine ⟨⟨(i : ℤ), hp⟩, Subtype.ext ?_⟩
      have h1 : (⟨((i : ℕ) : ℤ).toNat, hp.2⟩ : Fin F.card) = i := Fin.ext (Int.toNat_natCast _)
      change F.orderEmbOfFin rfl ⟨((i : ℕ) : ℤ).toNat, hp.2⟩ = y
      rw [h1, hi]
  have hfinp : {a : ℤ | p a}.Finite := (Set.finite_Ico (0 : ℤ) F.card).subset fun a ha => by
    have h := Int.toNat_of_nonneg ha.1
    have h2 := ha.2
    exact ⟨ha.1, by omega⟩
  have hinfA : Infinite {a : ℤ // ¬ p a} := hfinp.infinite_compl.to_subtype
  have hinfB : Infinite {y : ℤ // y ∉ F} := F.finite_toSet.infinite_compl.to_subtype
  have ec : {a : ℤ // ¬ p a} ≃ {y : ℤ // y ∉ F} := nonempty_equiv_of_countable.some
  refine ⟨Equiv.subtypeCongr (Equiv.ofBijective f hf) ec, fun k hk => ?_, fun a ha => ?_⟩
  · have hp : p (k : ℤ) := ⟨by positivity, by rw [Int.toNat_natCast]; exact hk⟩
    have h1 : (⟨((k : ℕ) : ℤ).toNat, hp.2⟩ : Fin F.card) = ⟨k, hk⟩ := Fin.ext (Int.toNat_natCast k)
    have h2 : Equiv.subtypeCongr (Equiv.ofBijective f hf) ec (k : ℤ) =
        ((Equiv.ofBijective f hf) ⟨(k : ℤ), hp⟩ : ℤ) := by
      rw [Equiv.subtypeCongr]; simp [hp]
    rw [h2]
    exact congrArg (F.orderEmbOfFin rfl) h1
  · by_contra hpa
    have hpa' : ¬ p a := hpa
    have h2 : Equiv.subtypeCongr (Equiv.ofBijective f hf) ec a = (ec ⟨a, hpa'⟩ : ℤ) := by
      rw [Equiv.subtypeCongr]; simp [hpa']
    rw [h2] at ha
    exact (ec ⟨a, hpa'⟩).2 ha

/-- **The walk on the local configuration.** If the vertices of the open set `V` and their neighbours form the finite
set `F`, then the law of the curve class of the walk on the multigraph of the local configuration from the label `k`,
stopped at its exit from `V`, is the law for the walk of `d` from the `k`-th element of `F`. -/
theorem map_srwLaw_localConfigOf_eq {V : Set ℂ} (hV : IsOpen V) {F : Finset ℤ}
    {d : (ℤ → ℂ) × (ℤ → ℤ → ℕ)} (hF : localVertices V d = ↑F) (k : ℕ) (hk : k < F.card) :
    (srwLaw (reconMult (localConfigOf F d)) k).map
        (fun w => stoppedExitCurve V (interpPathCM (reconPoint (localConfigOf F d)) zero_le_one w)) =
      (srwLaw d.2 (F.orderEmbOfFin rfl ⟨k, hk⟩)).map
        (fun w => stoppedExitCurve V (interpPathCM d.1 zero_le_one w)) := by
  obtain ⟨e, he, heF⟩ := exists_equiv_orderEmbOfFin F
  have hmemF : ∀ x : ℤ, x ∈ localVertices V d → x ∈ F := fun x hx => by
    rw [hF] at hx; exact hx
  have he' : ∀ a : ℤ, 0 ≤ a → ∀ hN : a.toNat < F.card,
      e a = F.orderEmbOfFin rfl ⟨a.toNat, hN⟩ := fun a h0 hN => by
    have h := he a.toNat hN
    rwa [Int.toNat_of_nonneg h0] at h
  have hpt : ∀ a : ℤ, 0 ≤ a → a.toNat < F.card → reconPoint (localConfigOf F d) a = d.1 (e a) := by
    intro a ha0 haN
    rw [he' a ha0 haN]
    exact localConfigOf_point F d a.toNat haN
  have hrow : ∀ x : ℤ, d.1 (e x) ∈ V →
      (fun a b => d.2 (e a) (e b)) x = reconMult (localConfigOf F d) x := by
    intro x hx
    obtain ⟨hx0, hxN⟩ := heF x (hmemF _ (Or.inl hx))
    funext l
    by_cases hl : 0 ≤ l ∧ l.toNat < F.card
    · have hc : 0 ≤ x ∧ 0 ≤ l ∧ x.toNat < (localConfigOf F d).1 ∧ l.toNat < (localConfigOf F d).1 :=
        ⟨hx0, hl.1, hxN, hl.2⟩
      show d.2 (e x) (e l) = reconMult (localConfigOf F d) x l
      unfold reconMult
      rw [ite_eq_left hc, he' x hx0 hxN, he' l hl.1 hl.2]
      show _ = (if h : x.toNat < F.card then if h' : l.toNat < F.card then
        d.2 (F.orderEmbOfFin rfl ⟨x.toNat, h⟩) (F.orderEmbOfFin rfl ⟨l.toNat, h'⟩) else 0 else 0)
      rw [dite_eq_left hxN, dite_eq_left hl.2]
    · have hlF : e l ∉ F := fun h => hl (heF l h)
      have h0 : d.2 (e x) (e l) = 0 := by
        by_contra hne
        exact hlF (hmemF _ (Or.inr ⟨e x, hx, hne⟩))
      show d.2 (e x) (e l) = reconMult (localConfigOf F d) x l
      unfold reconMult
      split_ifs with h
      · exact absurd ⟨h.2.1, h.2.2.2⟩ hl
      · exact h0
  have hstay := ae_reconMult_range (localConfigOf F d) k hk
  calc (srwLaw (reconMult (localConfigOf F d)) k).map
        (fun w => stoppedExitCurve V (interpPathCM (reconPoint (localConfigOf F d)) zero_le_one w))
      = (srwLaw (reconMult (localConfigOf F d)) k).map
          (fun w => stoppedExitCurve V (interpPathCM (fun a => d.1 (e a)) zero_le_one w)) := by
        refine Measure.map_congr ?_
        filter_upwards [hstay] with w hw
        rw [interpPathCM_congr_points (v := reconPoint (localConfigOf F d)) (v' := fun a => d.1 (e a))
          zero_le_one fun n => hpt (w n) (hw n).1 (hw n).2]
    _ = (srwLaw (fun a b => d.2 (e a) (e b)) k).map
          (fun w => stoppedExitCurve V (interpPathCM (fun a => d.1 (e a)) zero_le_one w)) :=
        (map_stoppedExitCurve_interpPathCM_eq_of_rows hV (fun a => d.1 (e a)) hrow (k : ℤ)).symm
    _ = (srwLaw d.2 (e k)).map (fun w => stoppedExitCurve V (interpPathCM d.1 zero_le_one w)) :=
        map_stoppedExitCurve_interpPathCM_relabel hV d.1 d.2 e k
    _ = _ := by rw [he k hk]

/-- **The comparison at the vertices is a function of the local configuration.** If the vertices of `V` and their
neighbours form a finite set and every point of `closedBall 0 ρ \ B_b(0)` lies in `V`, the comparison at the vertices
holds for `d` if and only if it holds for the local configuration of `d` near `V`. -/
theorem mem_vertexLPGood_iff_localConfig {V : Set ℂ} (hV : IsOpen V) {b ρ c : ℝ}
    (hrange : ∀ z : ℂ, z ∉ ball (0 : ℂ) b → z ∈ closedBall (0 : ℂ) ρ → z ∈ V)
    {d : (ℤ → ℂ) × (ℤ → ℤ → ℕ)} (hfin : (localVertices V d).Finite) :
    d ∈ vertexLPGood V b ρ c ↔ localConfig V d ∈ localLPGood V b ρ c := by
  have hF : localVertices V d = ↑hfin.toFinset := hfin.coe_toFinset.symm
  have hloc : localConfig V d = localConfigOf hfin.toFinset d := by
    unfold localConfig localFinset
    rw [dite_eq_left hfin]
  rw [hloc]
  constructor
  · intro hd k hk hkb hkρ
    have hpt := localConfigOf_point hfin.toFinset d k hk
    rw [hpt] at hkb hkρ
    rw [hpt, map_srwLaw_localConfigOf_eq hV hF k hk]
    exact hd _ hkb hkρ
  · intro hy x hxb hxρ
    have hxF : x ∈ hfin.toFinset := by
      rw [← Finset.mem_coe, ← hF]; exact Or.inl (hrange _ hxb hxρ)
    have hxr : x ∈ Set.range (hfin.toFinset.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hxF
    obtain ⟨i, rfl⟩ := hxr
    have hpt := localConfigOf_point hfin.toFinset d i i.2
    have h := hy i i.2 (by rw [hpt]; exact hxb) (by rw [hpt]; exact hxρ)
    rw [hpt, map_srwLaw_localConfigOf_eq hV hF i i.2] at h
    exact h

/-- The comparison at the vertices for `d` gives the comparison for its local configuration (vacuously when there
are infinitely many vertices of `V` and neighbours). -/
theorem localConfig_mem_localLPGood_of_mem {V : Set ℂ} (hV : IsOpen V) {b ρ c : ℝ}
    (hrange : ∀ z : ℂ, z ∉ ball (0 : ℂ) b → z ∈ closedBall (0 : ℂ) ρ → z ∈ V)
    {d : (ℤ → ℂ) × (ℤ → ℤ → ℕ)} (hd : d ∈ vertexLPGood V b ρ c) :
    localConfig V d ∈ localLPGood V b ρ c := by
  by_cases hfin : (localVertices V d).Finite
  · exact (mem_vertexLPGood_iff_localConfig hV hrange hfin).1 hd
  · have h : localConfig V d = localConfigOf ∅ d := by
      unfold localConfig localFinset
      rw [dite_eq_right hfin]
    rw [h]
    intro k hk
    exact absurd hk (by simp [localConfigOf])

/-! ### Measurability -/

theorem measurableSet_mem_localVertices {V : Set ℂ} (hV : MeasurableSet V) (y : ℤ) :
    MeasurableSet {d : (ℤ → ℂ) × (ℤ → ℤ → ℕ) | y ∈ localVertices V d} := by
  have h1 : MeasurableSet ((fun d : (ℤ → ℂ) × (ℤ → ℤ → ℕ) => d.1 y) ⁻¹' V) :=
    ((measurable_pi_apply y).comp measurable_fst) hV
  have h2 : ∀ x : ℤ, MeasurableSet ((fun d : (ℤ → ℂ) × (ℤ → ℤ → ℕ) => d.1 x) ⁻¹' V ∩
      (fun d : (ℤ → ℂ) × (ℤ → ℤ → ℕ) => d.2 x y) ⁻¹' {0}ᶜ) := fun x =>
    (((measurable_pi_apply x).comp measurable_fst) hV).inter
      (((measurable_pi_apply y).comp ((measurable_pi_apply x).comp measurable_snd))
        (measurableSet_singleton 0).compl)
  refine (h1.union (MeasurableSet.iUnion h2)).congr ?_
  ext d
  simp only [localVertices, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, ne_eq]

theorem measurableSet_localVertices_finite {V : Set ℂ} (hV : MeasurableSet V) :
    MeasurableSet {d : (ℤ → ℂ) × (ℤ → ℤ → ℕ) | (localVertices V d).Finite} := by
  have h : MeasurableSet (⋃ F : Finset ℤ, ⋂ y : ℤ,
      ({d : (ℤ → ℂ) × (ℤ → ℤ → ℕ) | y ∈ localVertices V d}ᶜ ∪ {_d | y ∈ F})) :=
    MeasurableSet.iUnion fun F => MeasurableSet.iInter fun y =>
      (measurableSet_mem_localVertices hV y).compl.union (MeasurableSet.const _)
  refine h.congr ?_
  ext d
  simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨F, hF⟩
    exact F.finite_toSet.subset fun y hy => (hF y).resolve_left (not_not.2 hy)
  · intro hfin
    exact ⟨hfin.toFinset, fun y => by
      by_cases hy : y ∈ localVertices V d
      · exact Or.inr (hfin.mem_toFinset.2 hy)
      · exact Or.inl hy⟩

theorem measurableSet_localFinset_eq {V : Set ℂ} (hV : MeasurableSet V) (F : Finset ℤ) :
    MeasurableSet {d : (ℤ → ℂ) × (ℤ → ℤ → ℕ) | localFinset V d = F} := by
  have hA : MeasurableSet (⋂ y : ℤ, ({d : (ℤ → ℂ) × (ℤ → ℤ → ℕ) | y ∈ localVertices V d} ∩ {_d | y ∈ F}) ∪
      ({d : (ℤ → ℂ) × (ℤ → ℤ → ℕ) | y ∈ localVertices V d}ᶜ ∩ {_d | y ∉ F})) :=
    MeasurableSet.iInter fun y =>
      ((measurableSet_mem_localVertices hV y).inter (MeasurableSet.const _)).union
        ((measurableSet_mem_localVertices hV y).compl.inter (MeasurableSet.const _))
  have hB : MeasurableSet ({d : (ℤ → ℂ) × (ℤ → ℤ → ℕ) | (localVertices V d).Finite}ᶜ ∩ {_d | F = ∅}) :=
    (measurableSet_localVertices_finite hV).compl.inter (MeasurableSet.const _)
  refine (hA.union hB).congr ?_
  ext d
  simp only [Set.mem_union, Set.mem_iInter, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (h | ⟨hfin, hF⟩)
    · have hset : localVertices V d = ↑F := by
        ext y
        rcases h y with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact iff_of_true h1 h2
        · exact iff_of_false h1 h2
      have hfin : (localVertices V d).Finite := by rw [hset]; exact F.finite_toSet
      unfold localFinset
      rw [dite_eq_left hfin]
      ext y
      rw [Set.Finite.mem_toFinset, hset, Finset.mem_coe]
    · unfold localFinset
      rw [dite_eq_right hfin, hF]
  · intro h
    by_cases hfin : (localVertices V d).Finite
    · left
      intro y
      have hFe : hfin.toFinset = F := by
        unfold localFinset at h
        rwa [dite_eq_left hfin] at h
      by_cases hy : y ∈ localVertices V d
      · exact Or.inl ⟨hy, by rw [← hFe]; exact hfin.mem_toFinset.2 hy⟩
      · exact Or.inr ⟨hy, fun hyF => hy (hfin.mem_toFinset.1 (by rw [hFe]; exact hyF))⟩
    · right
      refine ⟨hfin, ?_⟩
      unfold localFinset at h
      rw [dite_eq_right hfin] at h
      exact h.symm

theorem measurable_localConfigOf (F : Finset ℤ) : Measurable (localConfigOf F) := by
  have hp : ∀ k : ℕ, Measurable fun d : (ℤ → ℂ) × (ℤ → ℤ → ℕ) =>
      if hk : k < F.card then d.1 (F.orderEmbOfFin rfl ⟨k, hk⟩) else 0 := fun k => by
    by_cases hk : k < F.card
    · simp only [hk, ↓reduceDIte]
      exact (measurable_pi_apply _).comp measurable_fst
    · simp only [hk, ↓reduceDIte]
      exact measurable_const
  have hm : ∀ k l : ℕ, Measurable fun d : (ℤ → ℂ) × (ℤ → ℤ → ℕ) =>
      if hk : k < F.card then
        if hl : l < F.card then d.2 (F.orderEmbOfFin rfl ⟨k, hk⟩) (F.orderEmbOfFin rfl ⟨l, hl⟩) else 0
      else 0 := fun k l => by
    by_cases hk : k < F.card
    · by_cases hl : l < F.card
      · simp only [hk, hl, ↓reduceDIte]
        exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_snd)
      · simp only [hk, hl, ↓reduceDIte]
        exact measurable_const
    · simp only [hk, ↓reduceDIte]
      exact measurable_const
  unfold localConfigOf
  exact measurable_const.prodMk ((measurable_pi_iff.2 hp).prodMk
    (measurable_pi_iff.2 fun k => measurable_pi_iff.2 fun l => hm k l))

theorem measurable_localConfig {V : Set ℂ} (hV : MeasurableSet V) : Measurable (localConfig V) := by
  intro T hT
  have hset : localConfig V ⁻¹' T =
      ⋃ F : Finset ℤ, {d | localFinset V d = F} ∩ localConfigOf F ⁻¹' T := by
    ext d
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨localFinset V d, rfl, h⟩
    · rintro ⟨F, hF, h⟩
      unfold localConfig
      rw [hF]
      exact h
  rw [hset]
  exact MeasurableSet.iUnion fun F =>
    (measurableSet_localFinset_eq hV F).inter (measurable_localConfigOf F hT)

theorem measurable_reconMult : Measurable fun y : LocalConfig => reconMult y := by
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
  unfold reconMult
  refine Measurable.ite ?_ ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
    (measurable_snd.comp measurable_snd))) measurable_const
  exact measurable_fst (Set.to_countable {n : ℕ | 0 ≤ a ∧ 0 ≤ b ∧ a.toNat < n ∧ b.toNat < n}).measurableSet

theorem measurable_reconPoint : Measurable fun y : LocalConfig => reconPoint y :=
  measurable_pi_iff.2 fun a => (measurable_pi_apply a.toNat).comp (measurable_fst.comp measurable_snd)

/-- The law of the interpolated walk depends measurably on the points and the multiplicities. -/
theorem measurable_map_srwLaw_interpPathCM {X : Type*} [MeasurableSpace X] {v : X → ℤ → ℂ}
    (hv : Measurable v) {M : X → ℤ → ℤ → ℕ} (hM : Measurable M) (a : ℤ) :
    Measurable fun x => (srwLaw (M x) a).map (interpPathCM (v x) zero_le_one) := by
  let κ : Kernel X (ℕ → ℤ) := ⟨fun x => srwLaw (M x) a, (measurable_srwLaw a).comp hM⟩
  have : IsMarkovKernel κ := ⟨fun x => isProbabilityMeasure_srwLaw (M x) a⟩
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hset : MeasurableSet {p : X × (ℕ → ℤ) | interpPathCM (v p.1) zero_le_one p.2 ∈ s} :=
    (measurable_interpPathCM_uncurry zero_le_one).comp ((hv.comp measurable_fst).prodMk measurable_snd) hs
  have h := κ.measurable_kernel_prodMk_left hset
  convert h using 1
  funext x
  exact Measure.map_apply (measurable_interpPathCM (v x) zero_le_one) hs

/-- The event that two measurable families of probability measures are at Lévy–Prokhorov distance less than `c` is
measurable. -/
theorem measurableSet_levyProkhorovEDist_lt {X E : Type*} [MeasurableSpace X] [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.SeparableSpace E] {μ ν : X → Measure E}
    (hμ : Measurable μ) (hν : Measurable ν) (hμ1 : ∀ x, IsProbabilityMeasure (μ x))
    (hν1 : ∀ x, IsProbabilityMeasure (ν x)) (c : ℝ≥0∞) :
    MeasurableSet {x | levyProkhorovEDist (μ x) (ν x) < c} := by
  let μ' : X → ProbabilityMeasure E := fun x => ⟨μ x, hμ1 x⟩
  let ν' : X → ProbabilityMeasure E := fun x => ⟨ν x, hν1 x⟩
  have hμ' : Measurable μ' := hμ.subtype_mk
  have hν' : Measurable ν' := hν.subtype_mk
  have h := LatticeProb.measurable_levyProkhorovDist hμ' hν'
  have heq : (fun x => levyProkhorovEDist (μ x) (ν x)) =
      fun x => ENNReal.ofReal (levyProkhorovDist (μ' x : Measure E) (ν' x : Measure E)) := by
    funext x
    have := hμ1 x
    have := hν1 x
    exact (ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top (μ x) (ν x))).symm
  have hm : Measurable fun x => levyProkhorovEDist (μ x) (ν x) := by
    rw [heq]; exact ENNReal.measurable_ofReal.comp h
  exact measurableSet_lt hm measurable_const

theorem measurableSet_localLPGood {V : Set ℂ} (hV : IsOpen V) (b ρ c : ℝ) :
    MeasurableSet (localLPGood V b ρ c) := by
  have hstop := measurable_stoppedExitCurve V hV
  have hwalk : ∀ k : ℕ, Measurable fun y : LocalConfig =>
      (srwLaw (reconMult y) k).map fun w => stoppedExitCurve V (interpPathCM (reconPoint y) zero_le_one w) := by
    intro k
    have h := (Measure.measurable_map _ hstop).comp
      (measurable_map_srwLaw_interpPathCM measurable_reconPoint measurable_reconMult (k : ℤ))
    have heq : (fun y : LocalConfig => (srwLaw (reconMult y) k).map fun w =>
          stoppedExitCurve V (interpPathCM (reconPoint y) zero_le_one w)) =
        fun y => ((srwLaw (reconMult y) k).map (interpPathCM (reconPoint y) zero_le_one)).map
          (stoppedExitCurve V) := by
      funext y
      exact (Measure.map_map hstop (measurable_interpPathCM _ zero_le_one)).symm
    rw [heq]
    exact h
  have hbm : ∀ k : ℕ, Measurable fun y : LocalConfig =>
      (planarBrownianMotion (y.2.1 k)).map (stoppedExitCurve V) := fun k =>
    (Measure.measurable_map _ hstop).comp
      (planarBrownianMotion.measurable.comp ((measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)))
  have hset : localLPGood V b ρ c = ⋂ k : ℕ, ({y : LocalConfig | k < y.1}ᶜ ∪
      ({y : LocalConfig | y.2.1 k ∉ ball (0 : ℂ) b}ᶜ ∪ ({y : LocalConfig | y.2.1 k ∈ closedBall (0 : ℂ) ρ}ᶜ ∪
        {y : LocalConfig | levyProkhorovEDist ((srwLaw (reconMult y) k).map fun w =>
            stoppedExitCurve V (interpPathCM (reconPoint y) zero_le_one w))
          ((planarBrownianMotion (y.2.1 k)).map (stoppedExitCurve V)) < ENNReal.ofReal c}))) := by
    ext y
    simp only [localLPGood, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
    refine forall_congr' fun k => ?_
    tauto
  rw [hset]
  refine MeasurableSet.iInter fun k => ?_
  have h1 : MeasurableSet {y : LocalConfig | k < y.1} :=
    measurable_fst (Set.to_countable {n : ℕ | k < n}).measurableSet
  have h2 : MeasurableSet {y : LocalConfig | y.2.1 k ∉ ball (0 : ℂ) b} :=
    (((measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)) measurableSet_ball).compl
  have h3 : MeasurableSet {y : LocalConfig | y.2.1 k ∈ closedBall (0 : ℂ) ρ} :=
    ((measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)) measurableSet_closedBall
  have h4 := measurableSet_levyProkhorovEDist_lt (hwalk k) (hbm k)
    (fun y => (Measure.isProbabilityMeasure_map_iff
      (hstop.comp (measurable_interpPathCM (reconPoint y) zero_le_one)).aemeasurable).2 inferInstance)
    (fun y => (Measure.isProbabilityMeasure_map_iff hstop.aemeasurable).2 inferInstance) (ENNReal.ofReal c)
  exact h1.compl.union (h2.compl.union (h3.compl.union h4))

/-! ### Transfer of vanishing probabilities -/

/-- **Lemma 3.3 of arXiv:1705.11161 for the local configurations near annuli.** For all `0 < α < R`, the laws of the
local configurations near the annulus `B_R(0) \ closedBall 0 α` of the embedded data `X₁ n` and `X₂ n` at mesh `1/n`
are uniformly mutually absolutely continuous as `n → ∞` (Definition 3.2). -/
def LocalConfigUniformlyMutuallyAbsolutelyContinuous {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (X₁ : ℕ → Ω₁ → C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) (P₂ : Measure Ω₂)
    (X₂ : ℕ → Ω₂ → C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : Prop :=
  ∀ α R : ℝ, 0 < α → α < R →
    UniformlyMutuallyAbsolutelyContinuous (Ω := fun _ => LocalConfig)
      (fun n => P₁.map fun ω => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α)
        (vertexData (1 / (n : ℝ)) (X₁ n ω)))
      (fun n => P₂.map fun ω => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α)
        (vertexData (1 / (n : ℝ)) (X₂ n ω)))

private theorem measure_preimage_le_map_apply_aemeasurable {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) {f : α → β} (hf : AEMeasurable f μ) (B : Set β) :
    μ (f ⁻¹' B) ≤ μ.map f B :=
  calc μ (f ⁻¹' B) ≤ μ (f ⁻¹' toMeasurable (μ.map f) B) :=
        measure_mono (preimage_mono (subset_toMeasurable _ _))
    _ = μ.map f (toMeasurable (μ.map f) B) :=
        (Measure.map_apply_of_aemeasurable hf (measurableSet_toMeasurable _ _)).symm
    _ = μ.map f B := measure_toMeasurable B

/-- **Transfer of the comparison at the vertices on an annulus by Lemma 3.3** (Gwynne–Miller–Sheffield,
arXiv:1705.11161, proof of Theorem 3.4, case 1). Let `X₁ n`, `X₂ n` be embedded data (curve and multiplicities) on two
probability spaces such that the laws of the local configurations near the annulus `V = B_R(0) \ closedBall 0 α` of
`X₂ n` are uniformly absolutely continuous with respect to those of `X₁ n`, and such that the vertices of `V` and their
neighbours for `X₁ n` are almost surely finitely many for large `n`. If the law of `X₂ n` gives vanishing mass to the
failure of the comparison at the vertices on `V`, so does the law of `X₁ n`. -/
theorem tendsto_map_vertexAnnulusLPData_compl_of_localConfig {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] {X₁ : ℕ → Ω₁ → C(ℝ, ℂ) × (ℤ → ℤ → ℕ)}
    {X₂ : ℕ → Ω₂ → C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} (hX₁ : ∀ n, AEMeasurable (X₁ n) P₁)
    (hX₂ : ∀ n, AEMeasurable (X₂ n) P₂) {α b ρ R c : ℝ} (hαb : α < b) (hρR : ρ < R)
    (hfin : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P₁,
      (localVertices (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) (X₁ n ω))).Finite)
    (hUAC : UniformlyAbsolutelyContinuous (Ω := fun _ => LocalConfig)
      (fun n => P₂.map fun ω => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α)
        (vertexData (1 / (n : ℝ)) (X₂ n ω)))
      (fun n => P₁.map fun ω => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α)
        (vertexData (1 / (n : ℝ)) (X₁ n ω))))
    (h₂ : Tendsto (fun n : ℕ => P₂.map (X₂ n) (vertexAnnulusLPData (1 / (n : ℝ)) α b ρ R c)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => P₁.map (X₁ n) (vertexAnnulusLPData (1 / (n : ℝ)) α b ρ R c)ᶜ) atTop (𝓝 0) := by
  have hV : IsOpen (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) := isOpen_ball.sdiff isClosed_closedBall
  have hrange : ∀ z : ℂ, z ∉ ball (0 : ℂ) b → z ∈ closedBall (0 : ℂ) ρ →
      z ∈ ball (0 : ℂ) R \ closedBall (0 : ℂ) α := by
    intro z hzb hzρ
    rw [mem_ball_zero_iff, not_lt] at hzb
    rw [mem_closedBall_zero_iff] at hzρ
    refine ⟨mem_ball_zero_iff.2 (by linarith), fun h => ?_⟩
    rw [mem_closedBall_zero_iff] at h
    linarith
  have hG := measurableSet_localLPGood hV b ρ c
  have hloc : ∀ n : ℕ, Measurable fun d =>
      localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) d) := fun n =>
    (measurable_localConfig hV.measurableSet).comp (measurable_vertexData (1 / (n : ℝ)))
  have hm₁ : ∀ n : ℕ, AEMeasurable (fun ω => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α)
      (vertexData (1 / (n : ℝ)) (X₁ n ω))) P₁ := fun n => (hloc n).comp_aemeasurable (hX₁ n)
  have hm₂ : ∀ n : ℕ, AEMeasurable (fun ω => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α)
      (vertexData (1 / (n : ℝ)) (X₂ n ω))) P₂ := fun n => (hloc n).comp_aemeasurable (hX₂ n)
  have hA : Tendsto (fun n : ℕ => P₂.map (fun ω => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α)
      (vertexData (1 / (n : ℝ)) (X₂ n ω))) (localLPGood (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) b ρ c)ᶜ)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h₂ (fun _ => zero_le) fun n => ?_
    rw [Measure.map_apply_of_aemeasurable (hm₂ n) hG.compl]
    refine le_trans (measure_mono ?_) (measure_preimage_le_map_apply_aemeasurable P₂ (hX₂ n) _)
    intro ω hω hgood
    have hgood' : vertexData (1 / (n : ℝ)) (X₂ n ω) ∈
        vertexLPGood (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) b ρ c := hgood
    exact hω (localConfig_mem_localLPGood_of_mem hV hrange hgood')
  have hB := UniformlyAbsolutelyContinuous.tendsto_measure_preimage_zero (S := fun _ => LocalConfig)
    hm₁ hm₂ hUAC (A := fun _ => (localLPGood (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) b ρ c)ᶜ) hA
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hfin] with n hn
  have hE : MeasurableSet {d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) |
      (localVertices (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) d)).Finite} :=
    (measurable_vertexData (1 / (n : ℝ))) (measurableSet_localVertices_finite hV.measurableSet)
  have hsub : (vertexAnnulusLPData (1 / (n : ℝ)) α b ρ R c)ᶜ ⊆
      {d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) |
        (localVertices (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) d)).Finite}ᶜ ∪
      (fun d => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) d)) ⁻¹'
        (localLPGood (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) b ρ c)ᶜ := by
    intro d hd
    by_cases hf : (localVertices (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) d)).Finite
    · right
      intro hgood
      have hgood' : vertexData (1 / (n : ℝ)) d ∈ vertexLPGood (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) b ρ c :=
        (mem_vertexLPGood_iff_localConfig hV hrange hf).2 hgood
      exact hd hgood'
    · exact Or.inl hf
  have hnull : P₁ (X₁ n ⁻¹' {d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) |
      (localVertices (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) d)).Finite}ᶜ) = 0 :=
    measure_mono_null (fun ω hω => hω) (ae_iff.1 hn)
  calc P₁.map (X₁ n) (vertexAnnulusLPData (1 / (n : ℝ)) α b ρ R c)ᶜ
      ≤ P₁.map (X₁ n) ({d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) |
          (localVertices (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) d)).Finite}ᶜ ∪
        (fun d => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) d)) ⁻¹'
          (localLPGood (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) b ρ c)ᶜ) := measure_mono hsub
    _ ≤ P₁.map (X₁ n) {d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) |
          (localVertices (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) d)).Finite}ᶜ +
        P₁.map (X₁ n)
          ((fun d => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) d)) ⁻¹'
            (localLPGood (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) b ρ c)ᶜ) := measure_union_le _ _
    _ = P₁ (X₁ n ⁻¹' ((fun d => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α)
          (vertexData (1 / (n : ℝ)) d)) ⁻¹' (localLPGood (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) b ρ c)ᶜ)) := by
        rw [Measure.map_apply_of_aemeasurable (hX₁ n) hE.compl, hnull, zero_add,
          Measure.map_apply_of_aemeasurable (hX₁ n) ((hloc n) hG.compl)]

end MatedCRT

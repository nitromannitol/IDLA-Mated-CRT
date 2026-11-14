import MatedCRT.FirstPass.Derived.MarkovTimeChangeAdaptedGood
import MatedCRT.FirstPass.Derived.MarkovTimeChangePCAF
import MatedCRT.FirstPass.Derived.MarkovTimeChangeGoodClock
import MatedCRT.FirstPass.Derived.MarkovTimeChangeAssembly

/-!
# Identification of a Markovian time-changed planar Brownian motion as a PCAF time change

For a Markovian time-changed planar Brownian motion `P` (Berestycki–Gwynne, Definition 7.2), the inverse crossing
clock of the time-changed path is read off the clock-read path by measurable functionals `F_s`
(`IsMarkovTCBM.exists_goodAdaptedClock`), and the regularized half-clock `A = regularize (rawClock F)` of planar
Brownian motion is the candidate positive continuous additive functional (`isPCAF_regularize_rawClock`).  This module
identifies the one-dimensional marginals of `P` with those of the time change `B ∘ τ` of planar Brownian motion by
`A`, where `τ_u = clockInverse A u` is the right inverse of the clock, and transfers invariant measures
(Definition 7.3) from `P` to the time change.  With the abstract assembly `exists_const_mul_of_invariant` this gives
the proportionality of the two clocks in Berestycki–Gwynne, Proposition 7.10.

* `measurable_clockInverse`, `measurable_eval_clockInverse`: for a measurable clock nondecreasing along every path,
  `ω ↦ τ_u ω` and `ω ↦ ω (τ_u ω)` are measurable (`τ_u < c` iff `u < A_s` for a rational `s < c`, or `A ≤ u`);
* `halfPathInv`: the inverse of the half-speed Euclidean reading `halfPath`;
* `measurableSpace_euclidPath_eq_comap`: the Borel `σ`-algebra of the Euclidean path space is induced by the
  product `σ`-algebra of the coordinates;
* `eval_clockInverse_halfPathInv`: the pathwise identity `B (τ_t) = X_t`, read on the clock-read path of a path with
  good crossing clock and strictly increasing inverse crossing clock;
* `measure_eval_eq_clockInverse`: `P_z [X_t ∈ S] = P_z^{BM} [B (τ_t) ∈ S]` for every Borel `S`;
* `IsMarkovTCBM.exists_marginal_eq_clockInverse`: the same, with the functionals `F` of the packaging theorem;
* `IsInvariantFor.isInvTC`: an invariant measure of `P` is invariant for the time change by `A`;
* `exists_const_mul_of_isInvariantFor`, `ae_eval_clockInverse_eq_of_isInvariantFor`: the assembly of Proposition 7.10
  for two Markovian time-changed planar Brownian motions with a common invariant measure.
-/

open MeasureTheory MarkovProcess Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open PlanarBrownianSpace

/-! ### Measurability of the time-changed path -/

/-- **The right inverse of a monotone measurable clock is measurable.**  If every `A t` is measurable and `A` is
nondecreasing in time along every path, then `ω ↦ τ_u ω = inf {t | u < A t ω}` is measurable. -/
theorem measurable_clockInverse {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t))
    (hmono : ∀ ω, Monotone fun t => A t ω) (u : ℝ≥0) : Measurable (clockInverse A u) := by
  have key : ∀ (c : ℝ≥0) (ω : ContinuousPath ℂ), clockInverse A u ω < c ↔
      (∃ q : ℚ≥0, (q : ℝ≥0) < c ∧ u < A q ω) ∨ (0 < c ∧ ∀ q : ℚ≥0, A q ω ≤ u) := by
    intro c ω
    unfold clockInverse
    constructor
    · intro h
      rcases Set.eq_empty_or_nonempty {t | u < A t ω} with hne | hne
      · refine Or.inr ⟨lt_of_le_of_lt zero_le h, fun q => not_lt.1 fun hq => ?_⟩
        exact (Set.mem_empty_iff_false _).1 (hne.subset (show (q : ℝ≥0) ∈ {t | u < A t ω} from hq))
      · obtain ⟨s, hs, hsc⟩ := exists_lt_of_csInf_lt hne h
        obtain ⟨q, hsq, hqc⟩ := LatticeProb.exists_nnrat_between_nnreal hsc
        have hs' : u < A s ω := hs
        exact Or.inl ⟨q, hqc, lt_of_lt_of_le hs' (hmono ω hsq.le)⟩
    · rintro (⟨q, hqc, hq⟩ | ⟨hc, hall⟩)
      · exact lt_of_le_of_lt (csInf_le (OrderBot.bddBelow _) (show (q : ℝ≥0) ∈ {t | u < A t ω} from hq)) hqc
      · have hempty : {t | u < A t ω} = ∅ := by
          by_contra hT
          obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.2 hT
          obtain ⟨q, hsq, -⟩ := LatticeProb.exists_nnrat_between_nnreal (lt_add_one s)
          have hs' : u < A s ω := hs
          exact absurd (lt_of_lt_of_le hs' (hmono ω hsq.le)) (not_lt.2 (hall q))
        rw [hempty, NNReal.sInf_empty]
        exact hc
  refine measurable_of_Iio fun c => ?_
  have hset : clockInverse A u ⁻¹' Set.Iio c =
      (⋃ q : ℚ≥0, ({ω | (q : ℝ≥0) < c} ∩ {ω | u < A q ω})) ∪
        ({ω | 0 < c} ∩ ⋂ q : ℚ≥0, {ω | A q ω ≤ u}) := by
    ext ω
    rw [Set.mem_preimage, Set.mem_Iio, key]
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  exact (MeasurableSet.iUnion fun q : ℚ≥0 =>
      (MeasurableSet.const _).inter (measurableSet_lt measurable_const (hA q))).union
    ((MeasurableSet.const _).inter
      (MeasurableSet.iInter fun q : ℚ≥0 => measurableSet_le (hA q) measurable_const))

/-- **The time-changed path is measurable**: for a measurable clock nondecreasing along every path,
`ω ↦ ω (τ_u ω)` is measurable. -/
theorem measurable_eval_clockInverse {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t))
    (hmono : ∀ ω, Monotone fun t => A t ω) (u : ℝ≥0) :
    Measurable fun ω : ContinuousPath ℂ => ω (clockInverse A u ω) := by
  have hc := (ContinuousPath.measurable_coordinateProcess (0 : ℝ≥0)).comp
    (ContinuousPath.measurable_shift_of_measurable (clockInverse A u) (measurable_clockInverse hA hmono u))
  convert hc using 1
  funext ω
  simp [ContinuousPath.shift_apply, ContinuousPath.coordinateProcess_apply]

/-! ### The inverse of the half-speed reading -/

/-- The planar path read back from a half-speed Euclidean path: `s ↦ toEuclid⁻¹ (f (2 s))`.  It inverts
`halfPath`. -/
noncomputable def halfPathInv (f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) : ContinuousPath ℂ :=
  (⟨toEuclid.symm, toEuclid.symm.continuous⟩ : C(EuclideanSpace ℝ (Fin 2), ℂ)).comp
    (f.comp ⟨fun s => 2 * s, continuous_const.mul continuous_id⟩)

@[simp] lemma halfPathInv_apply (f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) (s : ℝ≥0) :
    halfPathInv f s = toEuclid.symm (f (2 * s)) := rfl

lemma continuous_halfPathInv : Continuous halfPathInv :=
  (ContinuousMap.continuous_postcomp _).comp (ContinuousMap.continuous_precomp _)

lemma halfPathInv_halfPath (w : ContinuousPath ℂ) : halfPathInv (halfPath w) = w := by
  have h2 : (2 : ℝ≥0) ≠ 0 := two_ne_zero
  refine ContinuousMap.ext fun s => ?_
  show toEuclid.symm (toEuclid (w (2⁻¹ * (2 * s)))) = w s
  rw [inv_mul_cancel_left₀ h2, LinearIsometryEquiv.symm_apply_apply]

lemma halfRead_halfPathInv (f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) : halfRead (halfPathInv f) = ⇑f := by
  have h2 : (2 : ℝ≥0) ≠ 0 := two_ne_zero
  funext u
  show toEuclid (toEuclid.symm (f (2 * (2⁻¹ * u)))) = f u
  rw [mul_inv_cancel_left₀ h2, LinearIsometryEquiv.apply_symm_apply]

/-- **The Borel `σ`-algebra of the Euclidean path space is induced by the coordinates.** -/
theorem measurableSpace_euclidPath_eq_comap :
    (inferInstance : MeasurableSpace C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) =
      MeasurableSpace.comap
        (fun f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) => (f : ℝ≥0 → EuclideanSpace ℝ (Fin 2))) inferInstance := by
  change (ContinuousMap.measurableSpace : MeasurableSpace C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) = _
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

/-! ### The pathwise identification -/

lemma toNNReal_two_inv_mul_coe (r : ℝ≥0) : Real.toNNReal (2⁻¹ * (r : ℝ)) = 2⁻¹ * r := by
  rw [show (2⁻¹ : ℝ) * (r : ℝ) = ((2⁻¹ * r : ℝ≥0) : ℝ) by norm_num, Real.toNNReal_coe]

/-- The clock-read path of a path with good crossing clock is continuous. -/
theorem continuous_clockRead_of_goodClock {m : ℝ≥0∞} {x : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))}
    (hc : LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u)) :
    Continuous (LatticeProb.clockRead m x) := by
  show Continuous fun t => x ((LatticeProb.clockInv (LatticeProb.crossClock m fun u => x u) t).toNNReal)
  exact x.continuous.comp (hc.continuous_clockInv_toNNReal (LatticeProb.crossClock_mono m _))

/-- **The pathwise identification of the time change.**  Let `x` be a Euclidean path whose crossing clock is good
and whose inverse crossing clock `ι` is strictly increasing along the rationals, and let the functionals `F` read
`ι (2 q)` off the clock-read path `g = x ∘ ι` for all rationals `q`.  Then along the planar path `w` with
`halfRead w = g`, the right inverse `τ_t` of the regularized half-clock satisfies `w (τ_t) = x (2 t)` (in planar
coordinates): `τ_t = σ (2 t) / 2` where `σ` is the crossing clock of `x`, and `g (σ (2 t)) = x (2 t)`. -/
theorem eval_clockInverse_halfPathInv {m : ℝ≥0∞}
    {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ} {x : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))}
    (hc : LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u))
    (hs : LatticeProb.InvClockStrict m x)
    (hFA : ∀ q : ℚ≥0, (LatticeProb.pathClockInv m x (2 * (q : ℝ≥0))).toReal =
      F (2 * (q : ℝ≥0)) (LatticeProb.clockRead m x))
    {g : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))} (hg : ⇑g = LatticeProb.clockRead m x) (t : ℝ≥0) :
    halfPathInv g (clockInverse (regularize (rawClock F)) t (halfPathInv g)) = toEuclid.symm (x (2 * t)) := by
  have h2 : (2 : ℝ≥0) ≠ 0 := two_ne_zero
  have h2p : (0 : ℝ≥0) < 2 := two_pos
  have h2i : (0 : ℝ≥0) < 2⁻¹ := by positivity
  have hcm : Monotone (LatticeProb.crossClock m fun u => x u) := LatticeProb.crossClock_mono m _
  obtain ⟨ι, hι⟩ : ∃ ι : ℝ≥0 → ℝ≥0, ∀ s, ι s = (LatticeProb.pathClockInv m x s).toNNReal :=
    ⟨_, fun _ => rfl⟩
  have hfin : ∀ s, LatticeProb.pathClockInv m x s ≠ ⊤ := fun s => (hc.clockInv_lt_top s).ne
  have hmono : Monotone ι := fun r s hrs => by
    rw [hι, hι]
    exact hc.monotone_clockInv_toNNReal hrs
  have hstr : StrictMono ι := by
    intro r s hrs
    obtain ⟨p, hrp, hps⟩ := LatticeProb.exists_nnrat_between_nnreal hrs
    obtain ⟨q, hpq, hqs⟩ := LatticeProb.exists_nnrat_between_nnreal hps
    have hpq' : p < q := by exact_mod_cast hpq
    have hlt : ι p < ι q := by
      rw [hι, hι]
      exact (ENNReal.toNNReal_lt_toNNReal (hfin _) (hfin _)).2 (hs.1 p q hpq')
    exact (hmono hrp.le).trans_lt (hlt.trans_le (hmono hqs.le))
  obtain ⟨a, hca⟩ : ∃ a : ℝ≥0, LatticeProb.crossClock m (fun u => x u) (2 * t) = (a : ℝ≥0∞) :=
    ⟨_, (ENNReal.coe_toNNReal (hc.lt_top hcm (2 * t)).ne).symm⟩
  have hιa' : LatticeProb.clockInv (LatticeProb.crossClock m fun u => x u) a = ((2 * t : ℝ≥0) : ℝ≥0∞) :=
    hc.clockInv_eq hcm hca
  have hιa : ι a = 2 * t := by
    rw [hι]
    exact (congrArg ENNReal.toNNReal hιa').trans (ENNReal.toNNReal_coe _)
  have hread : halfRead (halfPathInv g) = LatticeProb.clockRead m x := by
    rw [halfRead_halfPathInv, hg]
  have hskel : ∀ q : ℚ≥0, clockSkel F (LatticeProb.clockRead m x) q = 2⁻¹ * ι (2 * (q : ℝ≥0)) := by
    intro q
    show Real.toNNReal (2⁻¹ * F (2 * (q : ℝ≥0)) (LatticeProb.clockRead m x)) = 2⁻¹ * ι (2 * (q : ℝ≥0))
    rw [← hFA q, hι, ← ENNReal.coe_toNNReal_eq_toReal, toNNReal_two_inv_mul_coe]
  have hskm : Monotone (clockSkel F (LatticeProb.clockRead m x)) := by
    intro p q hpq
    rw [hskel, hskel]
    have hpq' : (p : ℝ≥0) ≤ q := by exact_mod_cast hpq
    exact mul_le_mul_of_nonneg_left (hmono (mul_le_mul_of_nonneg_left hpq' h2p.le)) h2i.le
  have hraw : ∀ q : ℚ≥0, rawClock F (q : ℝ≥0) (halfPathInv g) = clockSkel F (LatticeProb.clockRead m x) q := by
    intro q
    simp only [rawClock, clockSkel, hread]
  have hA : ∀ v, regularize (rawClock F) v (halfPathInv g) =
      LatticeProb.nnratRightInf (clockSkel F (LatticeProb.clockRead m x)) v := by
    intro v
    unfold regularize
    split_ifs with hcond
    · exact iInf_congr fun q => hraw q.1
    · exact absurd (fun p q hpq => (hraw p).trans_le ((hskm hpq).trans_eq (hraw q).symm)) hcond
  have hτ : clockInverse (regularize (rawClock F)) t (halfPathInv g) = 2⁻¹ * a := by
    unfold clockInverse
    simp only [hA]
    have h1 : Set.Ioi (2⁻¹ * a) ⊆
        {v | t < LatticeProb.nnratRightInf (clockSkel F (LatticeProb.clockRead m x)) v} := by
      intro v hv
      obtain ⟨p, hbp, hpv⟩ := LatticeProb.exists_nnrat_between_nnreal (Set.mem_Ioi.1 hv)
      have hap : a < 2 * (p : ℝ≥0) := by
        calc a = 2 * (2⁻¹ * a) := (mul_inv_cancel_left₀ h2 a).symm
          _ < 2 * (p : ℝ≥0) := mul_lt_mul_of_pos_left hbp h2p
      have hlt : 2 * t < ι (2 * (p : ℝ≥0)) := by
        rw [← hιa]
        exact hstr hap
      have hpt : t < clockSkel F (LatticeProb.clockRead m x) p := by
        rw [hskel]
        calc t = 2⁻¹ * (2 * t) := (inv_mul_cancel_left₀ h2 t).symm
          _ < 2⁻¹ * ι (2 * (p : ℝ≥0)) := mul_lt_mul_of_pos_left hlt h2i
      exact hpt.trans_le (LatticeProb.le_nnratRightInf hskm hpv.le)
    have h2' : ∀ v ∈ {v | t < LatticeProb.nnratRightInf (clockSkel F (LatticeProb.clockRead m x)) v},
        2⁻¹ * a ≤ v := by
      intro v hv
      by_contra hlt
      obtain ⟨q, hvq, hqb⟩ := LatticeProb.exists_nnrat_between_nnreal (not_le.1 hlt)
      have hqa : 2 * (q : ℝ≥0) < a := by
        calc 2 * (q : ℝ≥0) < 2 * (2⁻¹ * a) := mul_lt_mul_of_pos_left hqb h2p
          _ = a := mul_inv_cancel_left₀ h2 a
      have hlt2 : ι (2 * (q : ℝ≥0)) < 2 * t := by
        rw [← hιa]
        exact hstr hqa
      have hqt : clockSkel F (LatticeProb.clockRead m x) q < t := by
        rw [hskel]
        calc 2⁻¹ * ι (2 * (q : ℝ≥0)) < 2⁻¹ * (2 * t) := mul_lt_mul_of_pos_left hlt2 h2i
          _ = t := inv_mul_cancel_left₀ h2 t
      have hv' : t < LatticeProb.nnratRightInf (clockSkel F (LatticeProb.clockRead m x)) v := hv
      exact absurd (hv'.trans_le (LatticeProb.nnratRightInf_le hvq)) (not_lt.2 hqt.le)
    exact le_antisymm ((csInf_le_csInf (OrderBot.bddBelow _) Set.nonempty_Ioi h1).trans csInf_Ioi.le)
      (le_csInf (Set.nonempty_Ioi.mono h1) h2')
  rw [hτ, halfPathInv_apply, mul_inv_cancel_left₀ h2, hg]
  show toEuclid.symm (x (LatticeProb.clockInv (LatticeProb.crossClock m fun u => x u) a).toNNReal) = _
  rw [hιa', ENNReal.toNNReal_coe]

/-! ### The one-dimensional marginals and the invariant measure -/

/-- **The one-dimensional marginals of a Markovian time-changed planar Brownian motion are those of the time
change of planar Brownian motion by the regularized half-clock.**  Under the conclusions of
`IsMarkovTCBM.exists_goodAdaptedClock` (the law identification `hmap`, the goodness of the crossing clock, the
strictness of the inverse crossing clock and the clock functionals `F`), for every `z`, `t` and Borel `S`,
`P_z [X_t ∈ S] = P_z^{BM} [B (τ_t) ∈ S]` with `τ_t = clockInverse (regularize (rawClock F)) t`. -/
theorem measure_eval_eq_clockInverse {P : PathLawFamily} {m : ℝ≥0∞}
    {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ} (hF : ∀ s, Measurable (F s))
    (hmap : ∀ z : ℂ, (euclidFamily P (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))).map
      (LatticeProb.clockRead m) = (planarLaw z).map halfRead)
    (hgood : ∀ y, ∀ᵐ x ∂(euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u))
    (hstrict : ∀ y, ∀ᵐ x ∂(euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      LatticeProb.InvClockStrict m x)
    (hFA : ∀ (s : ℝ≥0) y, ∀ᵐ x ∂(euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      (LatticeProb.pathClockInv m x s).toReal = F s fun t => LatticeProb.clockPath m (fun u => x u) t)
    (z : ℂ) (t : ℝ≥0) {S : Set ℂ} (hS : MeasurableSet S) :
    (P z : Measure (ContinuousPath ℂ)) {x | x t ∈ S} =
      planarLaw z {w | w (clockInverse (regularize (rawClock F)) t w) ∈ S} := by
  have h2 : (2 : ℝ≥0) ≠ 0 := two_ne_zero
  have hV : MeasurableSet {w : ContinuousPath ℂ | w (clockInverse (regularize (rawClock F)) t w) ∈ S} :=
    measurable_eval_clockInverse (fun s => measurable_regularize (measurable_rawClock hF) s)
      (regularize_monotone (rawClock F)) t hS
  have hW : MeasurableSet[MeasurableSpace.comap
      (fun f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) => (f : ℝ≥0 → EuclideanSpace ℝ (Fin 2))) inferInstance]
      (halfPathInv ⁻¹' {w : ContinuousPath ℂ | w (clockInverse (regularize (rawClock F)) t w) ∈ S}) := by
    rw [← measurableSpace_euclidPath_eq_comap]
    exact continuous_halfPathInv.measurable hV
  obtain ⟨W, hWm, hpre⟩ := hW
  have hmem : ∀ f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)), (f : ℝ≥0 → EuclideanSpace ℝ (Fin 2)) ∈ W ↔
      halfPathInv f ∈ {w : ContinuousPath ℂ | w (clockInverse (regularize (rawClock F)) t w) ∈ S} :=
    fun f => Iff.of_eq (congrArg (f ∈ ·) hpre)
  have h1 : {w : ContinuousPath ℂ | w (clockInverse (regularize (rawClock F)) t w) ∈ S} =
      halfRead ⁻¹' W := by
    ext w
    rw [Set.mem_preimage, show halfRead w =
      ((halfPath w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) : ℝ≥0 → EuclideanSpace ℝ (Fin 2)) from rfl,
      hmem, halfPathInv_halfPath]
  rw [h1, ← Measure.map_apply measurable_halfRead hWm, ← hmap z,
    Measure.map_apply (LatticeProb.measurable_clockRead (E := EuclideanSpace ℝ (Fin 2)) m) hWm]
  have hae : (LatticeProb.clockRead m ⁻¹' W : Set C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) =ᵐ[
      (euclidFamily P (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2)))]
      {x | toEuclid.symm (x (2 * t)) ∈ S} := by
    filter_upwards [hgood (toEuclid z), hstrict (toEuclid z),
      ae_all_iff.2 fun q : ℚ≥0 => hFA (2 * (q : ℝ≥0)) (toEuclid z)] with x hxc hxs hxF
    apply propext
    let g : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) :=
      ⟨LatticeProb.clockRead m x, continuous_clockRead_of_goodClock hxc⟩
    have key := eval_clockInverse_halfPathInv hxc hxs hxF (g := g) rfl t
    show LatticeProb.clockRead m x ∈ W ↔ toEuclid.symm (x (2 * t)) ∈ S
    rw [show LatticeProb.clockRead m x = ⇑g from rfl, hmem]
    show halfPathInv g (clockInverse (regularize (rawClock F)) t (halfPathInv g)) ∈ S ↔ _
    rw [key]
  rw [measure_congr hae]
  have hmeas : MeasurableSet {x : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) | toEuclid.symm (x (2 * t)) ∈ S} :=
    (toEuclid.symm.continuous.comp (continuous_eval_const (2 * t))).measurable hS
  rw [euclidFamily_apply, LinearIsometryEquiv.symm_apply_apply,
    Measure.map_apply continuous_halfPath.measurable hmeas]
  congr 1
  ext X
  show X t ∈ S ↔ toEuclid.symm (toEuclid (X (2⁻¹ * (2 * t)))) ∈ S
  rw [inv_mul_cancel_left₀ h2, LinearIsometryEquiv.symm_apply_apply]

/-- **The marginal identification for a Markovian time-changed planar Brownian motion**: there are measurable
functionals `F` of the clock-read path such that, for every `z`, `t` and Borel `S`,
`P_z [X_t ∈ S] = P_z^{BM} [B (τ_t) ∈ S]` with `τ` the right inverse of the regularized half-clock of `F`. -/
theorem IsMarkovTCBM.exists_marginal_eq_clockInverse {P : PathLawFamily} (h : IsMarkovTCBM P) :
    ∃ F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ, (∀ s, Measurable (F s)) ∧
      ∀ (z : ℂ) (t : ℝ≥0) (S : Set ℂ), MeasurableSet S →
        (P z : Measure (ContinuousPath ℂ)) {x | x t ∈ S} =
          planarLaw z {w | w (clockInverse (regularize (rawClock F)) t w) ∈ S} := by
  obtain ⟨m, -, -, hmap, hgood, hstrict, hF⟩ := h.exists_goodAdaptedClock
  choose F hF' using hF
  exact ⟨F, fun s => (hF' s).1, fun z t S hS =>
    measure_eval_eq_clockInverse (fun s => (hF' s).1) hmap hgood hstrict (fun s => (hF' s).2.1) z t hS⟩

/-- **Invariant measures transfer to the time change** (Definition 7.3): if `μ` is invariant for `P` and the
one-dimensional marginals of `P` are those of the time change of planar Brownian motion by the clock `A`, then
`μ` is invariant for that time change. -/
theorem IsInvariantFor.isInvTC {P : PathLawFamily} {μ : Measure ℂ} (h : IsInvariantFor P μ)
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hmarg : ∀ (z : ℂ) (t : ℝ≥0) (S : Set ℂ), MeasurableSet S →
      (P z : Measure (ContinuousPath ℂ)) {x | x t ∈ S} = planarLaw z {w | w (clockInverse A t w) ∈ S}) :
    IsInvTC planarLaw A μ := by
  intro u S hS
  rw [← h u S hS]
  exact lintegral_congr fun z => (hmarg z u S hS).symm

/-! ### The assembly of Proposition 7.10 -/

/-- **Two Markovian time-changed planar Brownian motions with a common invariant measure have proportional
clocks** (Berestycki–Gwynne, Proposition 7.10, up to the three Revuz inputs).  For `i = 1, 2` let `P_i` be a family
of path laws with the conclusions of `IsMarkovTCBM.exists_goodAdaptedClock` (threshold `m_i`, functionals `F_i`),
whose regularized half-clock `A_i = regularize (rawClock F_i)` is a PCAF, and let `μ ≠ 0` be a locally finite
measure invariant for `P₁` and `P₂`.  Then there is `c > 0` with `A₁ = c A₂` almost surely from every starting
point.  The clocks `A_i` are good clocks by `goodClock_regularize_rawClock`. -/
theorem exists_const_mul_of_isInvariantFor (hRU : RevuzUniquenessInput) (hRI : RevuzInvariantInput)
    (hTU : TimeChangeInvariantUniqueInput) {P₁ P₂ : PathLawFamily} {m₁ m₂ : ℝ≥0∞}
    {F₁ F₂ : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hF₁ : ∀ s, Measurable (F₁ s)) (hF₂ : ∀ s, Measurable (F₂ s))
    (hmap₁ : ∀ z : ℂ, (euclidFamily P₁ (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))).map
      (LatticeProb.clockRead m₁) = (planarLaw z).map halfRead)
    (hmap₂ : ∀ z : ℂ, (euclidFamily P₂ (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))).map
      (LatticeProb.clockRead m₂) = (planarLaw z).map halfRead)
    (hgood₁ : ∀ y, ∀ᵐ x ∂(euclidFamily P₁ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      LatticeProb.GoodClock (LatticeProb.crossClock m₁ fun u => x u))
    (hgood₂ : ∀ y, ∀ᵐ x ∂(euclidFamily P₂ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      LatticeProb.GoodClock (LatticeProb.crossClock m₂ fun u => x u))
    (hstrict₁ : ∀ y, ∀ᵐ x ∂(euclidFamily P₁ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      LatticeProb.InvClockStrict m₁ x)
    (hstrict₂ : ∀ y, ∀ᵐ x ∂(euclidFamily P₂ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      LatticeProb.InvClockStrict m₂ x)
    (hFA₁ : ∀ (s : ℝ≥0) y, ∀ᵐ x ∂(euclidFamily P₁ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      (LatticeProb.pathClockInv m₁ x s).toReal = F₁ s fun t => LatticeProb.clockPath m₁ (fun u => x u) t)
    (hFA₂ : ∀ (s : ℝ≥0) y, ∀ᵐ x ∂(euclidFamily P₂ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      (LatticeProb.pathClockInv m₂ x s).toReal = F₂ s fun t => LatticeProb.clockPath m₂ (fun u => x u) t)
    (hA₁ : IsPCAF planarLaw (regularize (rawClock F₁))) (hA₂ : IsPCAF planarLaw (regularize (rawClock F₂)))
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] (hμ : μ ≠ 0)
    (h₁ : IsInvariantFor P₁ μ) (h₂ : IsInvariantFor P₂ μ) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, ∀ᵐ ω ∂planarLaw z, ∀ t,
      regularize (rawClock F₁) t ω = c * regularize (rawClock F₂) t ω :=
  exists_const_mul_of_invariant hRU hRI hTU hA₁ hA₂
    (goodClock_regularize_rawClock
      (μ := fun z => (euclidFamily P₁ (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))))
      hF₁ hmap₁ (fun _ => hgood₁ _) (fun _ => hstrict₁ _) (fun _ s => hFA₁ s _))
    (goodClock_regularize_rawClock
      (μ := fun z => (euclidFamily P₂ (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))))
      hF₂ hmap₂ (fun _ => hgood₂ _) (fun _ => hstrict₂ _) (fun _ s => hFA₂ s _)) hμ
    (h₁.isInvTC fun z t _ hS => measure_eval_eq_clockInverse hF₁ hmap₁ hgood₁ hstrict₁ hFA₁ z t hS)
    (h₂.isInvTC fun z t _ hS => measure_eval_eq_clockInverse hF₂ hmap₂ hgood₂ hstrict₂ hFA₂ z t hS)

/-- **The identification of the time-changed paths** (Berestycki–Gwynne, Proposition 7.10, up to the three Revuz
inputs): under the hypotheses of `exists_const_mul_of_isInvariantFor` there is `c > 0` such that, from every
starting point, almost surely `B (τ¹_u) = B (τ²_{u / c})` for all `u`, where `τ^i` is the right inverse of the
regularized half-clock `A_i`. -/
theorem ae_eval_clockInverse_eq_of_isInvariantFor (hRU : RevuzUniquenessInput) (hRI : RevuzInvariantInput)
    (hTU : TimeChangeInvariantUniqueInput) {P₁ P₂ : PathLawFamily} {m₁ m₂ : ℝ≥0∞}
    {F₁ F₂ : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hF₁ : ∀ s, Measurable (F₁ s)) (hF₂ : ∀ s, Measurable (F₂ s))
    (hmap₁ : ∀ z : ℂ, (euclidFamily P₁ (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))).map
      (LatticeProb.clockRead m₁) = (planarLaw z).map halfRead)
    (hmap₂ : ∀ z : ℂ, (euclidFamily P₂ (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))).map
      (LatticeProb.clockRead m₂) = (planarLaw z).map halfRead)
    (hgood₁ : ∀ y, ∀ᵐ x ∂(euclidFamily P₁ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      LatticeProb.GoodClock (LatticeProb.crossClock m₁ fun u => x u))
    (hgood₂ : ∀ y, ∀ᵐ x ∂(euclidFamily P₂ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      LatticeProb.GoodClock (LatticeProb.crossClock m₂ fun u => x u))
    (hstrict₁ : ∀ y, ∀ᵐ x ∂(euclidFamily P₁ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      LatticeProb.InvClockStrict m₁ x)
    (hstrict₂ : ∀ y, ∀ᵐ x ∂(euclidFamily P₂ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      LatticeProb.InvClockStrict m₂ x)
    (hFA₁ : ∀ (s : ℝ≥0) y, ∀ᵐ x ∂(euclidFamily P₁ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      (LatticeProb.pathClockInv m₁ x s).toReal = F₁ s fun t => LatticeProb.clockPath m₁ (fun u => x u) t)
    (hFA₂ : ∀ (s : ℝ≥0) y, ∀ᵐ x ∂(euclidFamily P₂ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      (LatticeProb.pathClockInv m₂ x s).toReal = F₂ s fun t => LatticeProb.clockPath m₂ (fun u => x u) t)
    (hA₁ : IsPCAF planarLaw (regularize (rawClock F₁))) (hA₂ : IsPCAF planarLaw (regularize (rawClock F₂)))
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] (hμ : μ ≠ 0)
    (h₁ : IsInvariantFor P₁ μ) (h₂ : IsInvariantFor P₂ μ) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, ∀ᵐ ω ∂planarLaw z, ∀ u,
      ω (clockInverse (regularize (rawClock F₁)) u ω) =
        ω (clockInverse (regularize (rawClock F₂)) (u / c) ω) :=
  ae_eval_clockInverse_eq_of_invariant hRU hRI hTU hA₁ hA₂
    (goodClock_regularize_rawClock
      (μ := fun z => (euclidFamily P₁ (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))))
      hF₁ hmap₁ (fun _ => hgood₁ _) (fun _ => hstrict₁ _) (fun _ s => hFA₁ s _))
    (goodClock_regularize_rawClock
      (μ := fun z => (euclidFamily P₂ (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))))
      hF₂ hmap₂ (fun _ => hgood₂ _) (fun _ => hstrict₂ _) (fun _ s => hFA₂ s _)) hμ
    (h₁.isInvTC fun z t _ hS => measure_eval_eq_clockInverse hF₁ hmap₁ hgood₁ hstrict₁ hFA₁ z t hS)
    (h₂.isInvTC fun z t _ hS => measure_eval_eq_clockInverse hF₂ hmap₂ hgood₂ hstrict₂ hFA₂ z t hS)

end MatedCRT

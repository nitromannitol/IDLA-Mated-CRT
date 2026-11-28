import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Inversion
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Tail
import MatedCRT.Proofs.Field.WholePlaneExistence
import MatedCRT.Proofs.Field.LawTransferCovariance
import HarmonicBalls.Proofs.Sec8.OriginGermZeroOne

/-!
# The whole-plane GFF modulo constants has a trivial tail at infinity

This file proves `WholePlaneGFFExteriorTailTrivial` (Miller–Sheffield, Imaginary geometry IV,
arXiv:1302.4738, §2.2.1, (2.7)) by the standard reduction of the tail at infinity to the germ at
`0`:

* the inversion `x ↦ 1 / x` (`invPull`, `ZeroConeLemmaA1Inversion`) maps the mean-zero tests
  supported in `{|w| > k + 2}` to mean-zero tests supported in `B_{1 / (k + 1)}(0) \ {0}` and
  preserves the law of the pairing process of the whole-plane GFF
  (`IsWholePlaneGFF.map_pairing_inv`);
* the germ of a whole-plane GFF at `0` is trivial
  (`HarmonicBalls.IsWholePlaneGFF.origin_germ_trivial`), and a whole-plane GFF in the Harmonic-Balls
  interface exists (`MatedCRT.Field.wholePlaneGFF_exists`);
* triviality of a tail σ-algebra of a process is a property of its law
  (`isTrivialSigma_iInf_comap_of_map_eq`), and the pairing processes of two whole-plane GFFs have
  the same law (`MatedCRT.Field.map_pairings_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter

namespace MatedCRT

/-- **Triviality of a tail σ-algebra is a property of the law.** If `F : Ω → E` has law `Q`, the
`𝒜 k` are decreasing sub-σ-algebras of `E` and `⨅ 𝒜 k` is `Q`-trivial, then `⨅ (𝒜 k).comap F` is
trivial. -/
theorem isTrivialSigma_iInf_comap_of_map_eq {Ω E : Type*} [MeasurableSpace Ω]
    [mE : MeasurableSpace E] {P : Measure Ω} {Q : Measure E} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {F : Ω → E}
    (hF : Measurable F) (hQ : P.map F = Q) {𝒜 : ℕ → MeasurableSpace E} (hle : ∀ k, 𝒜 k ≤ mE)
    (hanti : Antitone 𝒜) (htriv : LatticeProb.IsTrivialSigma (⨅ k, 𝒜 k) Q) :
    LatticeProb.IsTrivialSigma (⨅ k, (𝒜 k).comap F) P := by
  intro s hs
  have hk : ∀ k, ∃ A : Set E, MeasurableSet[𝒜 k] A ∧ F ⁻¹' A = s := fun k =>
    (iInf_le (fun k => (𝒜 k).comap F) k) s hs
  choose A hA hAs using hk
  have hmeas : ∀ k, MeasurableSet (A k) := fun k => hle k _ (hA k)
  have hQeq : ∀ k, Q (A k) = P s := fun k => by
    rw [← hQ, Measure.map_apply hF (hmeas k), hAs k]
  have hset : ∀ k, A 0 =ᵐ[Q] A k := fun k => by
    rw [ae_eq_set]
    constructor
    · rw [← hQ, Measure.map_apply hF ((hmeas 0).diff (hmeas k)), preimage_sdiff, hAs, hAs]
      simp
    · rw [← hQ, Measure.map_apply hF ((hmeas k).diff (hmeas 0)), preimage_sdiff, hAs, hAs]
      simp
  have hver : ∀ k, ∃ g : E → ℝ, StronglyMeasurable[𝒜 k] g ∧
      (A 0).indicator (fun _ => (1 : ℝ)) =ᵐ[Q] g := fun k =>
    ⟨(A k).indicator fun _ => (1 : ℝ), stronglyMeasurable_const.indicator (hA k),
      indicator_ae_eq_of_ae_eq_set (hset k)⟩
  obtain ⟨g, hgm, hg⟩ := LatticeProb.exists_iInf_version (P := Q) hanti hver
  have hT : MeasurableSet[⨅ k, 𝒜 k] {x | (1 / 2 : ℝ) < g x} := hgm measurableSet_Ioi
  have hseq : A 0 =ᵐ[Q] {x | (1 / 2 : ℝ) < g x} := by
    filter_upwards [hg] with x hx
    show (x ∈ A 0) = ((1 / 2 : ℝ) < g x)
    by_cases hxs : x ∈ A 0
    · rw [Set.indicator_of_mem hxs] at hx
      rw [← hx]
      exact propext ⟨fun _ => by norm_num, fun _ => hxs⟩
    · rw [Set.indicator_of_notMem hxs] at hx
      rw [← hx]
      exact propext ⟨fun h => absurd h hxs, fun h => by norm_num at h⟩
  rw [← hQeq 0, measure_congr hseq]
  exact htriv _ hT

/-- The index set of the pairing processes used below: mean-zero test functions whose support avoids
`0`. -/
abbrev AvoidOrigin : Type := {ψ : LQGMetric.TestC0 // (0 : ℂ) ∉ tsupport (ψ.1 : ℂ → ℝ)}

/-- The exterior `{|w| > k + 2}` of the closed disc of radius `k + 2`, as in `fieldSigma0On`. -/
abbrev extSet (k : ℕ) : Set ℂ := {w : ℂ | ((k + 2 : ℕ) : ℝ) < ‖w‖}

/-- The test functions supported in `{|w| > k + 2}` avoid the origin. -/
lemma zero_notMem_tsupport_of_subset_extSet {k : ℕ} {φ : ℂ → ℝ} (h : tsupport φ ⊆ extSet k) :
    (0 : ℂ) ∉ tsupport φ := fun h0 => by
  have := h h0
  simp only [mem_ofPred_eq, norm_zero] at this
  have : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  linarith

/-- **The whole-plane GFF modulo additive constants has a trivial tail at infinity**
(Miller–Sheffield, Imaginary geometry IV, arXiv:1302.4738, §2.2.1, (2.7)): by the inversion
`x ↦ 1 / x` the tail at infinity is carried to the germ at `0` of a whole-plane GFF, which is
trivial by Harmonic Balls. -/
theorem wholePlaneGFFExteriorTailTrivial : WholePlaneGFFExteriorTailTrivial := by
  intro Ω _ P X hP hX
  obtain ⟨Ω', mΩ', P', hC, hcirc, hP', hY⟩ := Field.wholePlaneGFF_exists
  have htf : ∀ s : AvoidOrigin, HarmonicBalls.IsTestFunction univ ⇑s.1.1 := fun s =>
    Field.isTestFunction_of_TestC s.1.1
  -- the pairing processes of `X` and of a Harmonic-Balls GFF `hC`, and its inversion
  let F : Ω → AvoidOrigin → ℝ := fun ω s => X ω s.1.1
  let G : Ω' → AvoidOrigin → ℝ := fun ω s => hC ω ⇑s.1.1
  let H : Ω' → AvoidOrigin → ℝ := fun ω s => hC ω (invPull ⇑s.1.1)
  have hFm : Measurable F := Measurable.of_eval fun s =>
    (LQGMetric.GFFInv.measurable_pair s.1.1).comp hX.measurable
  have hHm : Measurable H := Measurable.of_eval fun s =>
    hY.measurable_pairing _ (isTestFunction_invPull (htf s) s.2)
  have hFlaw : P.map F = P'.map G := by
    have hr : Measurable fun (u : LQGMetric.TestC0 → ℝ) (s : AvoidOrigin) => u s.1 :=
      Measurable.of_eval fun s => measurable_pi_apply _
    have hXm : Measurable fun ω (φ : LQGMetric.TestC0) => X ω φ.1 :=
      Measurable.of_eval fun φ => (LQGMetric.GFFInv.measurable_pair φ.1).comp hX.measurable
    have h1 : P.map F = (P.map fun ω (φ : LQGMetric.TestC0) => X ω φ.1).map
        fun (u : LQGMetric.TestC0 → ℝ) (s : AvoidOrigin) => u s.1 := by
      rw [Measure.map_map hr hXm]
      rfl
    have hCm : Measurable fun ω (φ : LQGMetric.TestC0) => hC ω φ.1 :=
      Measurable.of_eval fun φ => hY.measurable_pairing _ (Field.isTestFunction_of_TestC φ.1)
    have h2 : P'.map G = (P'.map fun ω (φ : LQGMetric.TestC0) => hC ω φ.1).map
        fun (u : LQGMetric.TestC0 → ℝ) (s : AvoidOrigin) => u s.1 := by
      rw [Measure.map_map hr hCm]
      rfl
    rw [h1, h2, Field.map_pairings_eq P' P hC hcirc X hY hX]
  have hGH : P'.map G = P'.map H :=
    IsWholePlaneGFF.map_pairing_inv hY (fun s : AvoidOrigin => ⇑s.1.1) htf fun s => s.2
  -- the σ-algebras of the pairings with tests supported in `{|w| > k + 2}`
  let J : ℕ → Type := fun k => {ψ : LQGMetric.TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ extSet k}
  let g : ∀ k, (AvoidOrigin → ℝ) → J k → ℝ := fun k u ψ =>
    u ⟨ψ.1, zero_notMem_tsupport_of_subset_extSet ψ.2⟩
  let 𝒜 : ℕ → MeasurableSpace (AvoidOrigin → ℝ) := fun k =>
    MeasurableSpace.comap (g k) inferInstance
  have hgm : ∀ k, Measurable (g k) := fun k =>
    Measurable.of_eval fun ψ => measurable_pi_apply _
  have hle : ∀ k, 𝒜 k ≤ (inferInstance : MeasurableSpace (AvoidOrigin → ℝ)) := fun k =>
    (hgm k).comap_le
  have hanti : Antitone 𝒜 := by
    intro a b hab
    have hsub : ∀ ψ : J b, tsupport (ψ.1.1 : ℂ → ℝ) ⊆ extSet a := fun ψ =>
      ψ.2.trans fun w (hw : ((b + 2 : ℕ) : ℝ) < ‖w‖) =>
        (lt_of_le_of_lt (by exact_mod_cast (by omega : a + 2 ≤ b + 2)) hw :
          ((a + 2 : ℕ) : ℝ) < ‖w‖)
    let h : (J a → ℝ) → J b → ℝ := fun v ψ => v ⟨ψ.1, hsub ψ⟩
    have hh : Measurable h := Measurable.of_eval fun ψ => measurable_pi_apply _
    have hb : 𝒜 b = (MeasurableSpace.comap h inferInstance).comap (g a) := by
      rw [MeasurableSpace.comap_comp]
      rfl
    rw [hb]
    exact MeasurableSpace.comap_mono hh.comap_le
  have hsigma : ∀ k, LQGMetric.Blueprint.fieldSigma0On X (extSet k) = (𝒜 k).comap F := by
    intro k
    unfold LQGMetric.Blueprint.fieldSigma0On
    rw [MeasurableSpace.comap_comp]
    rfl
  have hgerm : LatticeProb.IsTrivialSigma (⨅ k, 𝒜 k) (P'.map H) := by
    intro A hA
    have hAk : ∀ k, MeasurableSet[𝒜 k] A := fun k => (iInf_le 𝒜 k) A hA
    rw [Measure.map_apply hHm (hle 0 _ (hAk 0))]
    refine HarmonicBalls.IsWholePlaneGFF.origin_germ_trivial hY 0 (H ⁻¹' A) fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    have hcmp : (𝒜 k).comap H ≤
        HarmonicBalls.Section6.fieldSigmaAlgebraModConst 0 hC (ball 0 ε) := by
      rw [MeasurableSpace.comap_comp, ← measurable_iff_comap_le]
      refine @Measurable.of_eval _ _ _
        (HarmonicBalls.Section6.fieldSigmaAlgebraModConst 0 hC (ball 0 ε)) _ _ fun ψ => ?_
      have hφ := htf ⟨ψ.1, zero_notMem_tsupport_of_subset_extSet ψ.2⟩
      have hψ0 : (0 : ℂ) ∉ tsupport (ψ.1.1 : ℂ → ℝ) := zero_notMem_tsupport_of_subset_extSet ψ.2
      have hr : (((k + 2 : ℕ) : ℝ))⁻¹ < ε := by
        refine lt_trans ?_ (by simpa using hk)
        push_cast
        exact inv_strictAnti₀ (by positivity) (by linarith)
      have htest : HarmonicBalls.IsTestFunction (ball 0 ε) (invPull ⇑ψ.1.1) ∧
          ∫ x, invPull ⇑ψ.1.1 x = 0 := by
        have h1 := isTestFunction_invPull hφ hψ0
        have h2 := tsupport_invPull_subset (k := ((k + 2 : ℕ) : ℝ)) (by positivity) ψ.2
        refine ⟨⟨h1.1, h1.2.1, h2.trans (closedBall_subset_ball hr)⟩, ?_⟩
        rw [integral_invPull]
        exact ψ.1.2
      have heq : (fun ω => hC ω (invPull ⇑ψ.1.1)) =
          fun ω => HarmonicBalls.fieldPairing 0 (hC ω) (invPull ⇑ψ.1.1) := by
        funext ω
        simp [HarmonicBalls.fieldPairing]
      show Measurable[HarmonicBalls.Section6.fieldSigmaAlgebraModConst 0 hC (ball 0 ε)]
        fun ω => hC ω (invPull ⇑ψ.1.1)
      rw [heq]
      refine measurable_iff_comap_le.2 ?_
      exact le_iSup₂ (f := fun (φ : ℂ → ℝ)
        (_ : HarmonicBalls.IsTestFunction (ball 0 ε) φ ∧ ∫ x, φ x = 0) =>
          MeasurableSpace.comap (fun ω => HarmonicBalls.fieldPairing 0 (hC ω) φ) inferInstance)
        (invPull ⇑ψ.1.1) htest
    exact hcmp _ ⟨A, hAk k, rfl⟩
  have hmain := isTrivialSigma_iInf_comap_of_map_eq (P := P) (Q := P'.map H) hFm (hFlaw.trans hGH)
    hle hanti hgerm
  refine LatticeProb.IsTrivialSigma.mono hmain (le_iInf fun k => ?_)
  rw [← hsigma k]
  exact iInf_le (fun j : ℕ => LQGMetric.Blueprint.fieldSigma0On X {w : ℂ | (j : ℝ) < ‖w‖}) (k + 2)

end MatedCRT

import MatedCRT.Proofs.Sec5.StoppedActualSurplus
import MatedCRT.Proofs.Sec5.StoppedMarginContinuousDecoder

/-!
# Borel versions of the stopped actual surplus values and their continuous decoder (steps2-r3:3374-3388)

Source: `notes/wpn-steps2/steps2-r3.tex`, lines 3374-3388 (sha256 `88dfb1f9…`). For each point `a n` of a fixed countable
dense subset of the margin domain `A = marginDomain s (ρ/2)`, the actual surplus `v_ρ(μ,t)(a n) + tG_ρ(0,a n)` is the real
infimum of the evaluations at `a n` of the traces of the supersolutions of the obstacle problem, shifted by `tG_ρ(0,a n)`
(`hId_marginEval`; `G_ρ(0,·)` is the Green function of the disk, in the sense of Armitage-Gardiner). The source takes this
infimum on the good field set, where the supersolutions contain zero and are bounded below by `-tG_ρ` at the nonzero points.
Here the good set is made total: the section relation `𝒜` of `CodeSectionStmt` is replaced by

  `(𝒜 ∩ {(x, w) | ∀ n, -tG_ρ(0, a n) ≤ w (a n)}) ∪ {(x, 0)}`  (`lowerZeroRelation`).

Its sections contain zero and are bounded below at each dense point `a n` in every state (`lowerZero_sections`). On the
almost-sure event where `relSection 𝒜 (c ω) = superTraces (μ ω) ρ t`, they equal the trace sets
(`relSection_lowerZero_eq`). Then:

* `exists_actualSurplus_borel_values`: the Borel infimum versions of `exists_measurable_infimum_versions` are built on the
  state space with the law `P.map c`, transported to `Ω` by `ae_of_ae_map` (the direction that needs no measurability of a
  bad set), and shifted by `tG_ρ(0, a n)`. Their almost-sure values are the actual surplus at `a n`. No continuity is used.
* `exists_actualSurplus_decoder`: the dense decoder `denseDecoder` applied to these Borel values is a Borel map
  `D : PosCircleFns → C(A, ℝ)`. Almost surely on the event `F = {t < T}` (`T = clusterExitTime`), its pullback `D ∘ c` equals
  the actual surplus on `A`. The only continuity input is the almost-sure cone-family hypothesis `hfam`, which gives the
  continuity of the actual surplus on `A` on `F` (`continuousOn_actualSurplus_marginDomain`).

The two printed Preston inputs stay explicit as `hCantor : PrestonAnalyticCantorStmt` (Preston, Theorem 7.1, printed p. 39)
and `hT61 : PrestonTheorem61Stmt` (Preston, Theorem 6.1(1), printed p. 35). The code section enters through
`exists_relSection_ae_eq_superTraces` (`CodeSectionStmt`). The desired version is never assumed as `hId`: the identity
`D (c ω) = actualSurplus (μ ω)` is derived from the infimum identity `hId_marginEval`. No numbered result is claimed here.
-/

namespace MatedCRT.StoppedActualValueVersions

open MeasureTheory Filter Topology Set Metric
open MatedCRT.ConeOriginNull (BallFns superTraces)
open MatedCRT.StoppedInteriorMargin (marginDomain)
open MatedCRT.StoppedMarginValueVersions (relSection exists_measurable_infimum_versions marginDomain_compactSpace)
open MatedCRT.StoppedMarginDecoder (denseDecoder denseDecoder_eq_of measurable_denseDecoder marginDomain_denseDecoder)
open MatedCRT.StoppedActualSurplus (marginEval continuous_marginEval actualSurplus hId_marginEval zero_mem_superTraces
  lower_of_mem_superTraces mem_closedBall_of_mem_marginDomain_half ne_zero_of_mem_marginDomain
  exists_relSection_ae_eq_superTraces continuousOn_actualSurplus_marginDomain marginDomain_nonempty)
open MatedCRT.CircleProcessSpace (PosCircleFns PosCircleIndex)

/-! ### The lower-bounded section relation -/

/-- **Lower-bounded section relation.** The code section `𝒜` restricted to the traces that satisfy the lower bounds
`-tG_ρ(0, a n) ≤ w (a n)` at the dense points `a n`, together with the zero trace in every state. -/
def lowerZeroRelation {s ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) (a : ℕ → marginDomain s (ρ / 2))
    (𝒜 : Set (PosCircleFns × BallFns ρ)) : Set (PosCircleFns × BallFns ρ) :=
  (𝒜 ∩ {p | ∀ n, -t * HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 (a n).1 ≤ marginEval hρ (a n) p.2}) ∪
    {p | p.2 = 0}

/-- The lower-bounded section relation is measurable when `𝒜` is: the lower bounds are closed conditions in the trace. -/
theorem measurableSet_lowerZeroRelation {s ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) (a : ℕ → marginDomain s (ρ / 2))
    {𝒜 : Set (PosCircleFns × BallFns ρ)} (h𝒜 : MeasurableSet 𝒜) :
    MeasurableSet (lowerZeroRelation hρ t a 𝒜) := by
  refine MeasurableSet.union (h𝒜.inter ?_) ?_
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      measurableSet_le measurable_const ((continuous_marginEval hρ (a n)).measurable.comp measurable_snd)
  · exact (measurableSet_singleton (0 : BallFns ρ)).preimage measurable_snd

/-- **Total sections.** In every state the section of `lowerZeroRelation` is nonempty and bounded below under the evaluation
at each dense point `a n`, with no almost-sure input. The lower bound is `-tG_ρ(0, a n)`, which is `≤ 0`. -/
theorem lowerZero_sections {s ρ : ℝ} (hρ : 0 < ρ) {t : ℝ} (ht : 0 ≤ t) (a : ℕ → marginDomain s (ρ / 2))
    (𝒜 : Set (PosCircleFns × BallFns ρ)) (n : ℕ) (x : PosCircleFns) :
    (relSection (lowerZeroRelation hρ t a 𝒜) x).Nonempty ∧
      BddBelow (marginEval hρ (a n) '' relSection (lowerZeroRelation hρ t a 𝒜) x) := by
  have hle0 : -t * HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 (a n).1 ≤ 0 := by
    rw [neg_mul]
    exact neg_nonpos.2 (mul_nonneg ht (HarmonicBalls.greenFunction_nonneg Metric.isBounded_ball 0 (a n).1))
  have hzero : (0 : BallFns ρ) ∈ relSection (lowerZeroRelation hρ t a 𝒜) x := Or.inr rfl
  refine ⟨⟨0, hzero⟩, -t * HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 (a n).1, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  rcases hw with ⟨-, hL⟩ | hw0
  · exact hL n
  · rw [show w = 0 from hw0]
    simpa [marginEval] using hle0

/-- **Almost-sure identification of the sections.** If `relSection 𝒜 x` is the trace set `superTraces μ ρ t`, then the
section of `lowerZeroRelation` at `x` is the same set: the traces already satisfy the lower bounds
(`lower_of_mem_superTraces`) and the zero trace belongs to `superTraces` (`zero_mem_superTraces`). -/
theorem relSection_lowerZero_eq {s ρ : ℝ} (hρ : 0 < ρ) (hs : 0 < s) {t : ℝ} (ht : 0 ≤ t)
    (a : ℕ → marginDomain s (ρ / 2)) {μ : Measure ℂ} (𝒜 : Set (PosCircleFns × BallFns ρ))
    (x : PosCircleFns) (hx : relSection 𝒜 x = superTraces μ ρ t) :
    relSection (lowerZeroRelation hρ t a 𝒜) x = superTraces μ ρ t := by
  ext w
  constructor
  · rintro (⟨hw𝒜, -⟩ | hw0)
    · have hmem : w ∈ relSection 𝒜 x := hw𝒜
      rwa [hx] at hmem
    · rw [show w = 0 from hw0]
      exact zero_mem_superTraces μ ht
  · intro hw
    have hmem : w ∈ relSection 𝒜 x := by
      rw [hx]
      exact hw
    exact Or.inl ⟨hmem, fun n => lower_of_mem_superTraces hw
      (mem_closedBall_of_mem_marginDomain_half hρ (a n).2) (ne_zero_of_mem_marginDomain hs (a n).2)⟩

/-! ### Borel versions of the actual surplus values -/

/-- **Almost-surely Borel versions of the actual surplus at a countable dense set.** There are a dense sequence `a` of the
margin domain and Borel maps `W n` on the state space with `W n (c ω) = actualSurplus (S.μ ω) ρ t (a n)` almost surely:
the countably many Borel infimum versions of `exists_measurable_infimum_versions` on the law `P.map c`, shifted by
`tG_ρ(0, a n)` and transported to `Ω` by `ae_of_ae_map`. No continuity hypothesis is needed. -/
theorem exists_actualSurplus_borel_values (hCantor : PrestonAnalyticCantorStmt) (hT61 : PrestonTheorem61Stmt)
    (𝒮 : SpaceFillingSLEModel) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (c : Ω → PosCircleFns)
    (hc : Measurable c)
    (hcirc : ∀ᵐ ω ∂S.P, ∀ p : PosCircleIndex, c ω p = S.hcirc ω (p.1 : ℝ) p.2)
    {s ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (hs : 0 < s) (hsρ : s ≤ ρ / 2) :
    ∃ (a : ℕ → marginDomain s (ρ / 2)) (W : ℕ → PosCircleFns → ℝ),
      DenseRange a ∧ (∀ n, Measurable (W n)) ∧
        ∀ᵐ ω ∂S.P, ∀ n, W n (c ω) = actualSurplus (S.μ ω) ρ t (a n).1 := by
  obtain ⟨𝒜, h𝒜, hsec⟩ := exists_relSection_ae_eq_superTraces 𝒮 hγ hγ2 Ω S hS c hc hcirc hρ ht
  obtain ⟨a, ha, -, -⟩ := marginDomain_denseDecoder s (ρ / 2) (marginDomain_nonempty hs hsρ)
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have : IsProbabilityMeasure (S.P.map c) :=
    (Measure.isProbabilityMeasure_map_iff hc.aemeasurable).2 inferInstance
  obtain ⟨v, hvm, hva⟩ := exists_measurable_infimum_versions hCantor hT61
    (measurableSet_lowerZeroRelation hρ t a h𝒜) (g := fun n => marginEval hρ (a n))
    (fun n => continuous_marginEval hρ (a n)) (G := fun _ => univ) (fun _ => MeasurableSet.univ)
    (fun n x _ => lowerZero_sections hρ ht.le a 𝒜 n x) (S.P.map c)
  have hV : ∀ᵐ ω ∂S.P, ∀ n,
      v n (c ω) = sInf (marginEval hρ (a n) '' relSection (lowerZeroRelation hρ t a 𝒜) (c ω)) :=
    ae_of_ae_map (p := fun y => ∀ n, v n y = sInf (marginEval hρ (a n) '' relSection (lowerZeroRelation hρ t a 𝒜) y))
      hc.aemeasurable (hva.mono fun x hx n => hx n (mem_univ x))
  refine ⟨a, fun n x => v n x + t * HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 (a n).1, ha,
    fun n => (hvm n).add measurable_const, ?_⟩
  filter_upwards [hV, hsec] with ω hω hωsec n
  have hrel : relSection (lowerZeroRelation hρ t a 𝒜) (c ω) = superTraces (S.μ ω) ρ t :=
    relSection_lowerZero_eq hρ hs ht.le a 𝒜 (c ω) hωsec
  show v n (c ω) + t * HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 (a n).1 =
    actualSurplus (S.μ ω) ρ t (a n).1
  rw [hω n, hrel]
  exact hId_marginEval hρ (a n)

/-! ### The continuous decoder -/

/-- **Continuous decoder of the actual surplus (steps2-r3:3374-3388).** Decoding the shifted Borel values along the dense
sequence `a` with `denseDecoder` gives a Borel map `D` from the state space to `C(A, ℝ)`, `A = marginDomain s (ρ/2)`. Almost
surely on the event `F = {t < clusterExitTime Λ ρ}`, its pullback `D ∘ c` equals `x ↦ v_ρ(μ,t)(x) + tG_ρ(0,x)` on `A`. The
only continuity input is the almost-sure cone-family hypothesis `hfam`, which gives the continuity of the actual surplus on
`A` on `F` (`coneFamily_leastSupersolution_continuous`). -/
theorem exists_actualSurplus_decoder (hCantor : PrestonAnalyticCantorStmt) (hT61 : PrestonTheorem61Stmt)
    (𝒮 : SpaceFillingSLEModel) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (c : Ω → PosCircleFns)
    (hc : Measurable c)
    (hcirc : ∀ᵐ ω ∂S.P, ∀ p : PosCircleIndex, c ω p = S.hcirc ω (p.1 : ℝ) p.2)
    {s ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (hs : 0 < s) (hsρ : s ≤ ρ / 2)
    (Λ : Ω → ℝ → Set ℂ)
    (hfam : ∀ᵐ ω ∂S.P, MatedCRT.IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) :
    ∃ (a : ℕ → marginDomain s (ρ / 2)) (D : PosCircleFns → C(marginDomain s (ρ / 2), ℝ)),
      DenseRange a ∧
        @Measurable PosCircleFns C(marginDomain s (ρ / 2), ℝ) _ (borel C(marginDomain s (ρ / 2), ℝ)) D ∧
        ∀ᵐ ω ∂S.P, t < MatedCRT.clusterExitTime (Λ ω) ρ →
          ∀ x : marginDomain s (ρ / 2), D (c ω) x = actualSurplus (S.μ ω) ρ t x.1 := by
  obtain ⟨a, W, ha, hWm, hW⟩ :=
    exists_actualSurplus_borel_values hCantor hT61 𝒮 hγ hγ2 Ω S hS c hc hcirc hρ ht hs hsρ
  have : CompactSpace (marginDomain s (ρ / 2)) := marginDomain_compactSpace s (ρ / 2)
  have hcont : ∀ᵐ ω ∂S.P, t < MatedCRT.clusterExitTime (Λ ω) ρ →
      ContinuousOn (actualSurplus (S.μ ω) ρ t) (marginDomain s (ρ / 2)) :=
    hfam.mono fun ω hω hT => continuousOn_actualSurplus_marginDomain hω hρ ht hT hs
  refine ⟨a, fun x => denseDecoder a (fun n => W n x), ha, ?_, ?_⟩
  · exact (measurable_denseDecoder ha).comp (Measurable.of_eval fun n => hWm n)
  · filter_upwards [hW, hcont] with ω hωW hωc hF x
    have hf : denseDecoder a (fun n => W n (c ω)) =
        ⟨Set.domRestrict (marginDomain s (ρ / 2)) (actualSurplus (S.μ ω) ρ t),
          continuousOn_iff_continuous_domRestrict.mp (hωc hF)⟩ :=
      denseDecoder_eq_of ha fun n => (hωW n).symm
    show denseDecoder a (fun n => W n (c ω)) x = actualSurplus (S.μ ω) ρ t x.1
    rw [hf]
    rfl

end MatedCRT.StoppedActualValueVersions

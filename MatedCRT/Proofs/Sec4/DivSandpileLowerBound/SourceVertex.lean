import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells
import MatedCRT.Defs.Setting

/-! # The source vertex in the discrete Green kernel -/

namespace MatedCRT

open Set Filter Topology MeasureTheory

/-- If the curve has not visited the origin by time `-ε`, the least-index cell
containing the origin is cell zero. This is a deterministic sufficient condition;
the area-parametrization hypotheses alone do not assert it. -/
theorem vertexOf_zero_eq_zero_of_no_visit_before_mesh {ε : ℝ} {η : ℝ → ℂ}
    (hε : 0 < ε) (hzero : η 0 = 0) (hno : ∀ s ≤ -ε, η s ≠ 0) :
    vertexOf ε η 0 = 0 := by
  unfold vertexOf
  apply IsLeast.csInf_eq
  constructor
  · change (0 : ℂ) ∈ cell ε η 0
    exact ⟨0, by simp [hε.le], hzero⟩
  · intro k hk
    by_contra hn
    have hkneg : k < 0 := lt_of_not_ge hn
    obtain ⟨s, hs, hszero⟩ := hk
    have hkint : k ≤ -1 := by omega
    have hkreal : (k : ℝ) ≤ -1 := by exact_mod_cast hkint
    have hsneg : s ≤ -ε := by nlinarith [hs.2]
    exact hno s hsneg hszero

/-- In particular, no earlier return to the origin identifies the sources at
every positive mesh. -/
theorem vertexOf_zero_eq_zero_of_no_earlier_visit {ε : ℝ} {η : ℝ → ℂ}
    (hε : 0 < ε) (hzero : η 0 = 0) (hno : ∀ s < 0, η s ≠ 0) :
    vertexOf ε η 0 = 0 :=
  vertexOf_zero_eq_zero_of_no_visit_before_mesh hε hzero
    (fun s hs => hno s (lt_of_le_of_lt hs (neg_neg_of_pos hε)))

/-- For a continuous proper curve, the no-visit condition is also necessary:
an earlier visit belongs to a negative-index cell. -/
theorem vertexOf_zero_eq_zero_iff_no_visit_before_mesh {ε : ℝ} {η : ℝ → ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (hzero : η 0 = 0) :
    vertexOf ε η 0 = 0 ↔ ∀ s ≤ -ε, η s ≠ 0 := by
  constructor
  · intro hv s hs hszero
    have hfinite : {k : ℤ | (0 : ℂ) ∈ cell ε η k}.Finite :=
      (Tightness.cellVertices_finite hη hp hε
        (Bornology.isBounded_singleton (x := (0 : ℂ)))).subset
        (fun k hk => ⟨0, hk, rfl⟩)
    have hmem : (⌈s / ε⌉ : ℤ) ∈ {k : ℤ | (0 : ℂ) ∈ cell ε η k} := by
      simpa [hszero] using Tightness.mem_cell_ceil (η := η) hε s
    have hle : vertexOf ε η 0 ≤ ⌈s / ε⌉ := csInf_le hfinite.bddBelow hmem
    have hceil : (⌈s / ε⌉ : ℤ) ≤ -1 := by
      apply Int.ceil_le.mpr
      have : s / ε ≤ -1 := (div_le_iff₀ hε).2 (by linarith)
      simpa using this
    rw [hv] at hle
    omega
  · exact vertexOf_zero_eq_zero_of_no_visit_before_mesh hε hzero

/-- Identification of the sources at all positive meshes is equivalent to
the curve having no negative-time visit to the origin. -/
theorem vertexOf_zero_eq_zero_all_meshes_iff_no_earlier_visit {η : ℝ → ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hzero : η 0 = 0) :
    (∀ ε : ℝ, 0 < ε → vertexOf ε η 0 = 0) ↔ ∀ s < 0, η s ≠ 0 := by
  constructor
  · intro h s hs
    have hε : 0 < -s := neg_pos.mpr hs
    have hno := (vertexOf_zero_eq_zero_iff_no_visit_before_mesh hη hp hε hzero).1 (h (-s) hε)
    exact hno s (by simp)
  · intro h ε hε
    exact vertexOf_zero_eq_zero_of_no_earlier_visit hε hzero h

/-- A proper curve rooted at the origin whose first-hit shift fixes the curve
has no negative-time visit to the origin. -/
theorem no_earlier_visit_of_firstHit_shift {c : C(ℝ, ℂ)}
    (hp : Tendsto c (cocompact ℝ) (cocompact ℂ)) (hc0 : c 0 = 0)
    (hshift : ∀ t, c t = c (MatedCRTHarmonic.MatedCRT.firstHit c 0 + t)) :
    ∀ s < 0, c s ≠ 0 := by
  let A : Set ℝ := {s | c s = 0}
  have hcompact : IsCompact A :=
    (isProperMap_iff_tendsto_cocompact.2 ⟨c.continuous, hp⟩).isCompact_preimage
      (isCompact_singleton : IsCompact ({(0 : ℂ)} : Set ℂ))
  have hbelow : BddBelow A := hcompact.isBounded.bddBelow
  let τ : ℝ := MatedCRTHarmonic.MatedCRT.firstHit c 0
  have hτ0 : τ ≤ 0 := csInf_le hbelow hc0
  have hτ : c τ = 0 := by simpa [τ, hc0] using (hshift 0).symm
  have h2τ : c (τ + τ) = 0 := by simpa [τ, hτ] using (hshift τ).symm
  have hτ2τ : τ ≤ τ + τ := csInf_le hbelow h2τ
  have hτeq : τ = 0 := by linarith
  intro s hs hcs
  have hs' : τ ≤ s := csInf_le hbelow hcs
  linarith

/-- The identity coordinate-change rule of the mating-of-trees coupling forces
the area-parametrized curve to visit the origin first at time zero. -/
theorem MatedCRTEnv.IsValid.ae_no_earlier_origin_visit
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ s < 0, S.η ω s ≠ 0 := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hc, hbridge⟩ := hS.matingOfTrees
  obtain ⟨Φ, _, _, hΦ, hcoord, _⟩ := hc.igMap
  have hcoord' := hcoord 0 1 0 zero_lt_one
  filter_upwards [hΦ, hcoord', hc.spaceFilling, hc.areaParam, hbridge] with ω hΦω hcoordω hsf harea hη
  have hident : MatedCRTHarmonic.MatedCRT.igPullback γ 0 1 0
      (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω) =
        (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω) := by
    funext ρ w
    simp [MatedCRTHarmonic.MatedCRT.igPullback]
  rw [hident, ← hΦω] at hcoordω
  have hshift : ∀ t, ηL ω t = ηL ω (MatedCRTHarmonic.MatedCRT.firstHit (ηL ω) 0 + t) := by
    intro t
    have ht := congrArg (fun c : C(ℝ, ℂ) => c t) hcoordω
    simpa [MatedCRTHarmonic.MatedCRT.affineReroot] using ht
  have hnoret := no_earlier_visit_of_firstHit_shift hsf.2.1 hsf.2.2.1 hshift
  obtain ⟨φ, hφ0, hφ⟩ := harea.1
  intro s hs
  have hs' : φ s < 0 := by simpa [hφ0] using φ.strictMono hs
  rw [← congrFun hη.1 s, hφ]
  exact hnoret (φ s) hs'

/-- The source vertex in the discrete Green-function estimate is the origin
vertex almost surely, simultaneously for all positive meshes. -/
theorem MatedCRTEnv.IsValid.ae_vertexOf_zero_eq_zero
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → vertexOf ε (S.η ω) 0 = 0 := by
  filter_upwards [hS.ae_no_earlier_origin_visit, hS.isAreaParametrized] with ω hno harea
  intro ε hε
  exact vertexOf_zero_eq_zero_of_no_earlier_visit hε harea.2.1 hno

end MatedCRT

import MatedCRT.FirstPass.S3i.QuenchedBoundsCorrected
import MatedCRT.FirstPass.S3i.LensFloored
import MatedCRT.FirstPass.S3i.LensFlooredGeom
import MatedCRT.FirstPass.S3i.LensFlooredLens
import MatedCRT.FirstPass.S3i.LensFlooredClosed

/-!
# The quenched start and far-exit bounds for the floored good environment

Floored copies (for `FP36GoodEnvFloored`, S3i/LensFloored.lean) of the Lemma 7 clauses of S3i/QuenchedBoundsCorrected.lean:
`quenchedStart_null_of_exit_fp36` (line 35) and, below, `quenchedBoundsOnGood_fp36_of_exit`. The bodies are those of the
originals; the helper lemmas that do not take the environment are reused.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **Plan Lemma 7, clause 1, floored good environment** (copy of `quenchedStart_null_of_exit_fp36`,
S3i/QuenchedBoundsCorrected.lean:35). -/
theorem quenchedStart_null_of_exit_fp36_floored
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A β r ε : ℝ} {z y : ℂ} {ω : Ω}
    (hexit : ∀ {m : ℤ → ℤ → ℕ} {A' : Set ℤ}, FiniteExitData m A' →
      ∀ a ∈ A', srwLaw m a {x | vExitTime A' x < ⊤} = 1)
    (hε : 0 < ε) (hmpos : 0 < S.mε ε)
    (houter : closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀)
    (hgood : FP36GoodEnvFloored S ρ₀ ρ₁ b ν A β r z y ε ω) :
    srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) {x | ¬ SameWalkGood S r z ε ω x} = 0 := by
  obtain ⟨hA, -, -, hfin, hvin, -⟩ := hgood
  have hη : Continuous (S.η ω) := hA.1
  set a := vertexOf ε (S.η ω) y with ha
  set V := cellVertices ε (S.η ω) (ball z (r + 4 * ε ^ b)) with hV
  have hδ : 0 ≤ ε ^ b := Real.rpow_nonneg hε.le b
  have hball : ball z r ⊆ ball z (r + 4 * ε ^ b) := ball_subset_ball (by linarith)
  have haV : a ∈ V := by
    obtain ⟨c, hc1, hc2⟩ := hvin.1
    exact ⟨c, hc1, hball hc2⟩
  have hfinV : FiniteExitData (S.mult ε ω) V := (hfin _ houter).1
  have hE' : srwLaw (S.mult ε ω) a {x | vExitTime V x < ⊤} = 1 := hexit hfinV a haV
  have hnull2 : srwLaw (S.mult ε ω) a {x | vExitTime V x < ⊤}ᶜ = 0 :=
    (prob_compl_eq_zero_iff (measurableSet_vExitTime_lt_top_fp36 V)).2 hE'
  have hnull1 : srwLaw (S.mult ε ω) a {x | x 0 ≠ a} = 0 := by
    have h := ae_iff.1 (srwLaw_ae_start (S.mult ε ω) a)
    simpa [ne_eq] using h
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hnull1 hnull2)
  by_contra hxn
  simp only [mem_union, Set.mem_ofPred_eq, mem_compl_iff, not_or, not_not] at hxn hx
  obtain ⟨h0, hT⟩ := hxn
  apply hx
  unfold SameWalkGood
  refine ⟨?_, ?_⟩
  · rw [interpolatedWalk_zero_fp36, h0]
    exact vertexPoint_mem_ball_of_interior_fp36 hε.le hη hvin
  · exact pathExitTime_lt_top_of_vertex_not_mem_fp36 hmpos
      (fun h => vertexPoint_not_mem_of_not_mem_cellVertices_fp36 hε.le
        (vExitTime_toNat_not_mem_fp36 hT) (hball h))

/-- **Plan Lemma 7, clauses 1-2, floored good environment** (copy of `quenchedBoundsOnGood_fp36_of_exit`,
S3i/QuenchedBoundsCorrected.lean:117). The floored lens bound needs `ε ≤ 1` and `b ≤ β` (MQ-li-9 step 2). -/
theorem quenchedBoundsOnGood_fp36_of_exit_floored
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A β r ε : ℝ} {z y : ℂ} {ω : Ω}
    (hexit : ∀ {m : ℤ → ℤ → ℕ} {A' : Set ℤ}, FiniteExitData m A' →
      ∀ a ∈ A', srwLaw m a {x | vExitTime A' x < ⊤} = 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 0 < b) (hβb : b ≤ β) (hν : 0 < ν)
    (hA : 0 < A) (hr : 0 < r) (hρ : ρ₀ < ρ₁)
    (hmpos : 0 < S.mε ε)
    (hscale : 64 * ε ^ b ≤ ε ^ (b / 2))
    (houter : closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀)
    (hgood : FP36GoodEnvFloored S ρ₀ ρ₁ b ν A β r z y ε ω) :
    let μ := srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
    μ {x | ¬ SameWalkGood S r z ε ω x} = 0 ∧
    μ {x | SameWalkGood S r z ε ω x ∧
      ε ^ (b / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)}
      ≤ ENNReal.ofReal (A * (96 : ℝ) ^ ν * ε ^ (ν * b / 2)) := by
  refine ⟨quenchedStart_null_of_exit_fp36_floored hexit hε hmpos houter hgood, ?_⟩
  show srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
      {x | SameWalkGood S r z ε ω x ∧
        ε ^ (b / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)}
      ≤ ENNReal.ofReal (A * (96 : ℝ) ^ ν * ε ^ (ν * b / 2))
  obtain ⟨hA', hadj, hdiam3, hfin, hvin, -⟩ := id hgood
  have hη : Continuous (S.η ω) := hA'.1
  have hδ : 0 < ε ^ b := Real.rpow_pos_of_pos hε b
  have hsub1 : ball z (r + 4 * ε ^ b) ⊆ ball 0 ρ₁ :=
    (subset_closure.trans houter).trans (ball_subset_ball hρ.le)
  have hball : ball z r ⊆ ball 0 ρ₁ := (ball_subset_ball (by linarith)).trans hsub1
  have hdiam : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball z (r + 4 * ε ^ b)).Nonempty →
      diam (cell ε (S.η ω) k) ≤ ε ^ b :=
    fun k ⟨c, hc1, hc2⟩ => hdiam3 k ⟨c, hc1, hsub1 hc2⟩
  have hfinI : FiniteExitData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r)) :=
    (hfin (ball z r) ((closure_mono (ball_subset_ball (by linarith))).trans houter)).2
  set a := vertexOf ε (S.η ω) y with ha
  set I := interiorCellVertices ε (S.η ω) (ball z r) with hI
  -- almost surely: the walk starts at `a`, every step is trivial or an edge of positive multiplicity
  -- (`H2.ae_step_adjacent`), and the walk exits the finite set `I` in finite time (`hexit`)
  have hs0 : ∀ᵐ x ∂srwLaw (S.mult ε ω) a, x 0 = a := srwLaw_ae_start (S.mult ε ω) a
  have hsteps : ∀ᵐ x ∂srwLaw (S.mult ε ω) a,
      ∀ n : ℕ, x (n + 1) = x n ∨ S.mult ε ω (x n) (x (n + 1)) ≠ 0 :=
    H2.ae_step_adjacent (S.mult ε ω) a
  have hfinE : ∀ᵐ x ∂srwLaw (S.mult ε ω) a, vExitTime I x < ⊤ :=
    ae_iff.2 ((prob_compl_eq_zero_iff (measurableSet_vExitTime_lt_top_fp36 I)).2 (hexit hfinI a hvin))
  have hAE := hs0.and (hsteps.and hfinE)
  have hnull : srwLaw (S.mult ε ω) a
      {x : ℕ → ℤ | ¬ (x 0 = a ∧ (∀ n : ℕ, x (n + 1) = x n ∨ S.mult ε ω (x n) (x (n + 1)) ≠ 0) ∧
        vExitTime I x < ⊤)} = 0 :=
    ae_iff.1 hAE
  have hcontain : {x : ℕ → ℤ | SameWalkGood S r z ε ω x ∧
      ε ^ (b / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)} ⊆
      {x : ℕ → ℤ | vExitTime I x < ⊤ ∧
        (let n := (vExitTime I x).toNat
         let v := vExitPosition I x
         vExitTime (interiorCellVertices ε (S.η ω)
            (fp36LensDomain z r (ε ^ b) (ballRetraction z r (vertexPoint ε (S.η ω) v)) (ε ^ (b / 2))))
           (shiftedPath n x) < ⊤ ∧
         vExitPosition (interiorCellVertices ε (S.η ω)
            (fp36LensDomain z r (ε ^ b) (ballRetraction z r (vertexPoint ε (S.η ω) v)) (ε ^ (b / 2))))
           (shiftedPath n x) ∈ fp36LensFarCells ε (S.η ω) (ballRetraction z r (vertexPoint ε (S.η ω) v)) (ε ^ (b / 2)))} ∪
      {x : ℕ → ℤ | ¬ (x 0 = a ∧ (∀ n : ℕ, x (n + 1) = x n ∨ S.mult ε ω (x n) (x (n + 1)) ≠ 0) ∧
        vExitTime I x < ⊤)} := by
    intro x hx
    by_cases hxP : x 0 = a ∧ (∀ n : ℕ, x (n + 1) = x n ∨ S.mult ε ω (x n) (x (n + 1)) ≠ 0) ∧
        vExitTime I x < ⊤
    · left
      obtain ⟨hx0eq, hedgeAll, hfinx⟩ := hxP
      obtain ⟨hxG, hxfar⟩ := hx
      obtain ⟨-, hTfin⟩ := hxG
      have hNe : vExitTime I x = ((vExitTime I x).toNat : ℕ∞) :=
        (ENat.natCast_toNat hfinx.ne).symm
      have hN1 : ∀ k < (vExitTime I x).toNat, x k ∈ I :=
        fun k hk => mem_of_lt_vExitTime_fp36 hNe hk
      have hN2 : x (vExitTime I x).toNat ∉ I :=
        vExitTime_toNat_not_mem_fp36 hfinx
      have hN0 : 0 < (vExitTime I x).toNat :=
        Nat.pos_of_ne_zero (fun h0 => hN2 (by rw [h0, hx0eq]; exact hvin))
      -- the exit step is an edge: a trivial step would keep the walk inside `I`
      have hedgeN : S.mult ε ω (x ((vExitTime I x).toNat - 1)) (x (vExitTime I x).toNat) ≠ 0 := by
        have h := hedgeAll ((vExitTime I x).toNat - 1)
        rw [Nat.sub_add_cancel hN0] at h
        rcases h with h | h
        · exfalso
          apply hN2
          rw [h]
          exact hN1 _ (by omega)
        · exact h
      have hvb : x (vExitTime I x).toNat ∈ vBoundary (S.mult ε ω) I :=
        ⟨hN2, _, hN1 _ (by omega), hedgeN⟩
      obtain ⟨-, -, hq, hent4⟩ := H4.boundaryVertexGeometry_fp36_of_ball_floored hε hr hball hgood hvb
      have hent := hent4 _ (hN1 _ (by omega)) hedgeN
      have hvU := (H5.lensGeometry_fp36_floored hε hb hr hρ hscale houter hgood hvb).1
      refine ⟨hfinx, ?_⟩
      exact farExit_pathwise_step_fp36 (M := S.mult ε ω) (N := (vExitTime I x).toNat)
        hε hη hmpos hr hδ hscale hN0 hN1 hN2
        hedgeAll hadj hdiam hq hent hvU hTfin hxfar
    · right
      exact hxP
  refine (measure_mono hcontain).trans ((measure_union_le _ _).trans ?_)
  rw [hnull, add_zero]
  refine (H2.srwLaw_strongMarkov_vExitTime hfinI hvin
    (fun v => interiorCellVertices ε (S.η ω)
      (fp36LensDomain z r (ε ^ b) (ballRetraction z r (vertexPoint ε (S.η ω) v)) (ε ^ (b / 2))))
    (fun v => fp36LensFarCells ε (S.η ω) (ballRetraction z r (vertexPoint ε (S.η ω) v)) (ε ^ (b / 2)))).trans ?_
  exact iSup₂_le fun v hv => ENNReal.ofReal_le_ofReal
    (lensProb_le_fp36_closed_floored hε hε1 hb hβb hν hA hr hρ hscale houter hgood hv)

end FirstPass36
end MatedCRT

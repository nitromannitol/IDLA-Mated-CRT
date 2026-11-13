import MatedCRT.FirstPass.S3i.Proof
import MatedCRT.Defs.WalkDisconnection
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusBarriers
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AdmissibleAnnulusScales
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BoundaryCellAnnulusGeometry
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BoundarySurvival
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.DiscreteExitExcursion
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RateTailReduction
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.DiskDecompositionGeometry

/-!
# Lemma 3.6, boundary-excursion half of `hLens` (fp-S3i-hLens-excursion, owner z1)

Source: `docs/campaign/LEMMA36-REPLACEMENT.md`, Lemma `lem:excursion` (l.259-339), exponents `eq:exponents`
(l.182-258), inputs (l.122-181). With `b = min a β`, `d = ε^a`, `ℓ = 100 d + ε^β` and `s = ε^{b/2}`, the lemma bounds the
far-exit event of `QuenchedLensStep` (`FirstPass36.QuenchedLensStep`, `Proof.lean:240`) by `C (ℓ/s)^ν = C ε^{νb/2}`,
with `ν = -log(1-p)/log 2`.

Terminology: quenched law `srwLaw (S.mult ε ω) v` of the walk from `v` (Armstrong-Kuusi-Mourrat); one-stage annulus
barrier and disconnection (Gwynne-Miller-Sheffield, arXiv:1807.07511, Lemma 3.11, (3.35)); interior cell vertices
`V^ε(D) \ V^ε(∂D)` on the disc `D = ball z r` (Armitage-Gardiner).

Pointwise good-event properties (the part of `E_ε` used by the proof). Not the event itself: `E_ε` and its probability
bound are the business of the good-event file (q4). The two properties:
* cell size: every cell meeting `B_{ρ₁}(0)` has diameter at most `ε^a` (LEMMA36 (b));
* annulus disconnection (LEMMA36 (c), GMS (3.35)), in the form of `GMSUniformRate.lean:13`: every vertex of the
  disc `B_s(c)` (`ε^β ≤ s`, `B_{2s}(c) ⊆ B_{ρ₁}`) starts a walk that disconnects the inner vertices from the outer
  ones with probability at least `p`.

Proof route (not yet written; the pieces exist in `Proofs/Sec3/ConvergenceHarmonicFunctions`): the displacement tail
is `srwLaw_discrete_exit_excursion_le` (`DiscreteExitExcursion.lean:13`) with threshold `R = ε^{b/2}/2`, whose boundary
hypothesis `hbound` is the nested-disk survival `measure_nested_disk_survival_le_of_disconnection`
(`AnnulusBarriers.lean:335`, product `(1-p)^{n+1}`) over dyadic radii `2^j ℓ`. The planar observation sits inside the
geometric hypothesis `hgeom` of that lemma. The reduction `srwLaw_sameWalkExitDiscrepancy_le_of_excursion_tail`
(`RateTailReduction.lean:117`) is the discrepancy form. The statement's event is a subset of the discrete excursion
event, so the `SameWalkGood` conjunct and the a.s. finiteness of the exit time are not needed.

Status: STATEMENT ONLY in this file. The proof of `QuenchedLensExcursionStmt` is open (see the report).
Note: the excursion proof of LEMMA36 l.259-339 uses the annulus input (c) and the strong Markov property.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- Explicit dyadic survival exponent (eq:exponents): if `distance ≤ factor · cutoff · 2^n`, then
`q ^ n ≤ (factor · cutoff / distance) ^ ν_q` with `ν_q = -log q / log 2`, so `2^(-ν_q) = q`. -/
theorem dyadic_survival_le_explicit_ratio {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (n : ℕ)
    {cutoff distance factor : ℝ} (hdist : 0 < distance)
    (hscale : distance ≤ factor * cutoff * (2 : ℝ) ^ n) :
    q ^ n ≤ (factor * cutoff / distance) ^ (-Real.log q / Real.log 2) := by
  set ν : ℝ := -Real.log q / Real.log 2 with hνdef
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogq : Real.log q < 0 := Real.log_neg hq hq1
  have hν : 0 ≤ ν := div_nonneg (by linarith) hlog2.le
  have hlog2' : Real.log 2 ≠ 0 := hlog2.ne'
  have h2 : (2 : ℝ) ^ (-ν) = q := by
    have e : Real.log 2 * -ν = Real.log q := by
      rw [hνdef]; field_simp
    rw [Real.rpow_def_of_pos two_pos, e, Real.exp_log hq]
  have hratio : (1 / (2 : ℝ) ^ n) * distance ≤ factor * cutoff := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    calc distance ≤ factor * cutoff * (2 : ℝ) ^ n := hscale
      _ = (2 : ℝ) ^ n * (factor * cutoff) := by ring
  have hx : 1 / (2 : ℝ) ^ n ≤ factor * cutoff / distance := by
    rw [le_div_iff₀ hdist]; exact hratio
  have hpow : (1 / (2 : ℝ) ^ n) ^ ν = q ^ n := by
    calc (1 / (2 : ℝ) ^ n) ^ ν = ((2 : ℝ) ^ (-(n : ℝ))) ^ ν := by
          rw [Real.rpow_neg two_pos.le, Real.rpow_natCast, one_div]
      _ = (2 : ℝ) ^ (-(n : ℝ) * ν) := by rw [← Real.rpow_mul two_pos.le]
      _ = (2 : ℝ) ^ (-ν * (n : ℝ)) := by congr 1; ring
      _ = ((2 : ℝ) ^ (-ν)) ^ (n : ℝ) := by rw [← Real.rpow_mul two_pos.le]
      _ = q ^ n := by rw [h2, Real.rpow_natCast]
  calc q ^ n = (1 / (2 : ℝ) ^ n) ^ ν := hpow.symm
    _ ≤ (factor * cutoff / distance) ^ ν := Real.rpow_le_rpow (by positivity) hx hν

/-- Nested-annulus survival with the explicit exponent `ν = -log(1-p)/log 2` (eq:exponents): the
pure bound `(1-p)^(n+1)` of `measure_nested_disk_survival_le_of_disconnection`, converted by
`dyadic_survival_le_explicit_ratio` with `n + 1` dyadic scales. -/
theorem measure_nested_disk_survival_le_explicit_power {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ}
    {z : ℂ} {a : ℤ} (hη : Continuous η) (r : ℕ → ℝ) (hr : Antitone r) (n : ℕ)
    (I U S : ℕ → Set ℤ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (cutoff distance factor : ℝ) (hdist : 0 < distance)
    (hscale : distance ≤ factor * cutoff * (2 : ℝ) ^ (n + 1))
    (hpos : ∀ i ≤ n, 0 < r i)
    (ha : a ∈ interiorCellVertices ε η (Metric.ball z (r n))) (haS : a ∈ S n)
    (hadj : ∀ v w, m v w ≠ 0 → (cell ε η v ∩ cell ε η w).Nonempty)
    (hnb : ∀ i ≤ n, ∀ v ∈ interiorCellVertices ε η (Metric.ball z (r i)), ∀ w,
      m v w ≠ 0 → w ∈ interiorCellVertices ε η (Metric.ball z (r i)) ∪
        cellVertices ε η (Metric.sphere z (r i)))
    (hfin : ∀ᵐ x ∂srwLaw m a, vExitTime (interiorCellVertices ε η (Metric.ball z (r 0))) x ≠ ⊤)
    (hnext : ∀ i < n, cellVertices ε η (Metric.sphere z (r (i + 1))) ∩
      cellVertices ε η (Metric.ball z (r (i + 1))) ⊆ S i)
    (hgeom : ∀ i ≤ n, ∃ y b, y ∈ I i ∧ b ∈ cellVertices ε η (Metric.sphere z (r i)) ∧
      ∃ w : (adjGraph m).Walk y b, ∀ u ∈ w.support, u ∉ U i)
    (hdisc : ∀ i ≤ n, ∀ v, v ∈ S i → ENNReal.ofReal p ≤ srwLaw m v
      {x | ∀ y ∈ I i, walkDisconnectsBeforeHit m
        (cellVertices ε η (Metric.sphere z (r i))) y x}) :
    srwLaw m a {x | ∀ i ≤ n, ∀ j : ℕ, (j : ℕ∞) <
      vHitTime (cellVertices ε η (Metric.sphere z (r i))) x → x j ∈ U i} ≤
      ENNReal.ofReal ((factor * cutoff / distance) ^ (-Real.log (1 - p) / Real.log 2)) := by
  have hq : 0 < 1 - p := by linarith
  have hq1 : 1 - p < 1 := by linarith
  calc _ ≤ ENNReal.ofReal (1 - p) ^ (n + 1) :=
        MatedCRT.measure_nested_disk_survival_le_of_disconnection hη r hr n I U S p hp.le hpos ha haS
          hadj hnb hfin hnext hgeom hdisc
    _ = ENNReal.ofReal ((1 - p) ^ (n + 1)) := (ENNReal.ofReal_pow hq.le _).symm
    _ ≤ ENNReal.ofReal ((factor * cutoff / distance) ^ (-Real.log (1 - p) / Real.log 2)) :=
        ENNReal.ofReal_le_ofReal (dyadic_survival_le_explicit_ratio hq hq1 (n + 1) hdist hscale)

/-- Pointwise GMS nested-annulus survival with the explicit exponent: the annulus disconnection in the
GMS (3.35) form `hgood` (LEMMA36 (c)) gives the disconnection hypothesis of
`measure_nested_disk_survival_le_explicit_power` at the radii `r i / 2`, with `I i = B_{r i / 4}` and
`S i = B_{r i / 2}`, so that the survival bound is `(factor · cutoff / distance) ^ ν`. Pointwise port of
`GMSAnnulusSurvival.lean:57` (no `∀ᵐ`). -/
theorem measure_nested_disk_survival_le_explicit_gms {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {m : ℤ → ℤ → ℕ} {ε β ρ : ℝ} {η : ℝ → ℂ} {z : ℂ} {a : ℤ} {r : ℕ → ℝ} {n : ℕ}
    {U : ℕ → Set ℤ} (cutoff distance factor : ℝ) (hdist : 0 < distance)
    (hscale : distance ≤ factor * cutoff * (2 : ℝ) ^ (n + 1))
    (hη : Continuous η) (hr : Antitone r) (hpos : ∀ i ≤ n, 0 < r i)
    (ha : a ∈ interiorCellVertices ε η (Metric.ball z (r n)))
    (haS : a ∈ cellVertices ε η (Metric.ball z (r n / 2)))
    (hadj : ∀ v w, m v w ≠ 0 → (cell ε η v ∩ cell ε η w).Nonempty)
    (hnb : ∀ i ≤ n, ∀ v ∈ interiorCellVertices ε η (Metric.ball z (r i)), ∀ w,
      m v w ≠ 0 → w ∈ interiorCellVertices ε η (Metric.ball z (r i)) ∪
        cellVertices ε η (Metric.sphere z (r i)))
    (hfin : ∀ᵐ x ∂srwLaw m a, vExitTime (interiorCellVertices ε η (Metric.ball z (r 0))) x ≠ ⊤)
    (hnext : ∀ i < n, cellVertices ε η (Metric.sphere z (r (i + 1))) ∩
      cellVertices ε η (Metric.ball z (r (i + 1))) ⊆ cellVertices ε η (Metric.ball z (r i / 2)))
    (hgeom : ∀ i ≤ n, ∃ y b, y ∈ cellVertices ε η (Metric.sphere z (r i / 4)) ∧
      b ∈ cellVertices ε η (Metric.sphere z (r i)) ∧
      ∃ w : (adjGraph m).Walk y b, ∀ u ∈ w.support, u ∉ U i)
    (hz : z ∈ Metric.ball (0 : ℂ) ρ)
    (hadmiss : ∀ i ≤ n, ε ^ β ≤ r i / 2 ∧ r i / 2 ≤ ρ ∧ Metric.ball z (2 * (r i / 2)) ⊆ Metric.ball 0 ρ)
    (hgood : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
      Metric.ball z (2 * s) ⊆ Metric.ball 0 ρ → ∀ v ∈ cellVertices ε η (Metric.ball z s),
      ENNReal.ofReal p ≤ srwLaw m v
        {x | ∀ y ∈ cellVertices ε η (Metric.sphere z (s / 2)),
          walkDisconnectsBeforeHit m (cellVertices ε η (Metric.sphere z (2 * s))) y x}) :
    srwLaw m a {x | ∀ i ≤ n, ∀ j : ℕ, (j : ℕ∞) <
      vHitTime (cellVertices ε η (Metric.sphere z (r i))) x → x j ∈ U i} ≤
      ENNReal.ofReal ((factor * cutoff / distance) ^ (-Real.log (1 - p) / Real.log 2)) := by
  have hdisc : ∀ i ≤ n, ∀ v ∈ cellVertices ε η (Metric.ball z (r i / 2)),
      ENNReal.ofReal p ≤ srwLaw m v {x | ∀ y ∈ cellVertices ε η (Metric.sphere z (r i / 4)),
        walkDisconnectsBeforeHit m (cellVertices ε η (Metric.sphere z (r i))) y x} := by
    intro i hi v hv
    obtain ⟨hlow, hhigh, hball⟩ := hadmiss i hi
    have h := hgood z hz (r i / 2) hlow hhigh hball v hv
    convert h using 1
    congr 2
    ring
  exact measure_nested_disk_survival_le_explicit_power hη r hr n
    (fun i => cellVertices ε η (Metric.sphere z (r i / 4))) U
    (fun i => cellVertices ε η (Metric.ball z (r i / 2))) hp hp1 cutoff distance factor hdist hscale
    hpos ha haS hadj hnb hfin hnext hgeom hdisc

/-- Separating walks in nested annuli (pointwise body of
`MatedCRTEnv.IsValid.ae_nested_annulus_separating_walks_of_cell_size`, `SafeRadialWalk.lean:127`): at scale `ε`
with cell graph `η` and multiplicities `M ε`, for every annulus `B_{r i}(z)` with clearance from the disc
`B_{radius i}(x)` and cell-size bound `bound` on `B_ρ`, there is an adjacency walk from `∂B_{r i/4}(z)` to
`∂B_{r i}(z)` avoiding the cells of `B_{radius i}(x)`. -/
def SeparatingWalkGeom (η : ℝ → ℂ) (M : ℝ → ℤ → ℤ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ (z x : ℂ) (r radius : ℕ → ℝ) (n : ℕ) (margin bound ρ : ℝ),
    bound ≤ margin →
    (∀ i ≤ n, 0 < r i ∧ radius i - dist z x + margin < r i / 4 ∧
      Metric.ball z (2 * r i) ⊆ Metric.ball 0 ρ) →
    (∀ i, (cell ε η i ∩ Metric.ball 0 ρ).Nonempty → Metric.diam (cell ε η i) ≤ bound) →
    ∀ i ≤ n, ∃ y b, y ∈ cellVertices ε η (Metric.sphere z (r i / 4)) ∧
      b ∈ cellVertices ε η (Metric.sphere z (r i)) ∧
      ∃ w : (adjGraph (M ε)).Walk y b,
        ∀ v ∈ w.support, v ∉ cellVertices ε η (Metric.ball x (radius i))

/-- Pointwise port of `GMSSafeSurvival.lean:14`: the survival of the walk from `a` through the nested annuli
`B_{r i}(z)` (not leaving the interior cells of `B_{radius i}(x)`), with the explicit exponent. The
separating walks come from `SeparatingWalkGeom`, the disconnection from `hgood` (LEMMA36 (c)). -/
theorem safe_survival_le_explicit_gms {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {M : ℝ → ℤ → ℤ → ℕ} {η : ℝ → ℂ} (hη : Continuous η) (hwalk : SeparatingWalkGeom η M)
    {ε β ρ : ℝ} {z x : ℂ} {a : ℤ} {r radius : ℕ → ℝ} {n : ℕ} {buffer margin bound : ℝ}
    (cutoff distance factor : ℝ) (hdist : 0 < distance)
    (hscale : distance ≤ factor * cutoff * (2 : ℝ) ^ (n + 1))
    (hε : 0 < ε) (hbuffer : 0 < buffer) (hmargin : bound ≤ margin) (hr : Antitone r)
    (hgeometry : ∀ i ≤ n, 0 < r i ∧ radius i + buffer - dist z x + margin < r i / 4 ∧
      Metric.ball z (2 * r i) ⊆ Metric.ball 0 ρ)
    (hsize : ∀ i, (cell ε η i ∩ Metric.ball 0 ρ).Nonempty → Metric.diam (cell ε η i) ≤ bound)
    (ha : a ∈ interiorCellVertices ε η (Metric.ball z (r n)))
    (haS : a ∈ cellVertices ε η (Metric.ball z (r n / 2)))
    (hadj : ∀ v w, M ε v w ≠ 0 → (cell ε η v ∩ cell ε η w).Nonempty)
    (hnb : ∀ i ≤ n, ∀ v ∈ interiorCellVertices ε η (Metric.ball z (r i)), ∀ w,
      M ε v w ≠ 0 → w ∈ interiorCellVertices ε η (Metric.ball z (r i)) ∪
        cellVertices ε η (Metric.sphere z (r i)))
    (hfin : ∀ᵐ x' ∂srwLaw (M ε) a, vExitTime (interiorCellVertices ε η (Metric.ball z (r 0))) x' ≠ ⊤)
    (hnext : ∀ i < n, cellVertices ε η (Metric.sphere z (r (i + 1))) ∩
      cellVertices ε η (Metric.ball z (r (i + 1))) ⊆ cellVertices ε η (Metric.ball z (r i / 2)))
    (hz : z ∈ Metric.ball (0 : ℂ) ρ)
    (hadmiss : ∀ i ≤ n, ε ^ β ≤ r i / 2 ∧ r i / 2 ≤ ρ ∧ Metric.ball z (2 * (r i / 2)) ⊆ Metric.ball 0 ρ)
    (hgood : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
      Metric.ball z (2 * s) ⊆ Metric.ball 0 ρ → ∀ v ∈ cellVertices ε η (Metric.ball z s),
      ENNReal.ofReal p ≤ srwLaw (M ε) v
        {x' | ∀ y ∈ cellVertices ε η (Metric.sphere z (s / 2)),
          walkDisconnectsBeforeHit (M ε) (cellVertices ε η (Metric.sphere z (2 * s))) y x'}) :
    srwLaw (M ε) a {path | ∀ i ≤ n, ∀ j : ℕ, (j : ℕ∞) <
      vHitTime (cellVertices ε η (Metric.sphere z (r i))) path →
        path j ∈ interiorCellVertices ε η (Metric.ball x (radius i))} ≤
      ENNReal.ofReal ((factor * cutoff / distance) ^ (-Real.log (1 - p) / Real.log 2)) := by
  have hgeom : ∀ i ≤ n, ∃ y b, y ∈ cellVertices ε η (Metric.sphere z (r i / 4)) ∧
      b ∈ cellVertices ε η (Metric.sphere z (r i)) ∧
      ∃ w : (adjGraph (M ε)).Walk y b,
        ∀ u ∈ w.support, u ∉ interiorCellVertices ε η (Metric.ball x (radius i)) := by
    intro i hi
    obtain ⟨y, b, hy, hb, w, hw⟩ := hwalk ε hε z x r (fun i => radius i + buffer) n margin bound ρ
      hmargin hgeometry hsize i hi
    refine ⟨y, b, hy, hb, w, ?_⟩
    intro v hv hinside
    apply hw v hv
    obtain ⟨q, hq, hqball⟩ := hinside.1
    refine ⟨q, hq, Metric.mem_ball.mpr ?_⟩
    have hdist' := Metric.mem_ball.mp hqball
    linarith
  exact measure_nested_disk_survival_le_explicit_gms hp hp1 cutoff distance factor hdist hscale hη hr
    (fun i hi => (hgeometry i hi).1) ha haS hadj hnb hfin hnext hgeom hz hadmiss hgood

/-- Pointwise port of `GMSBoundaryHit.lean:13`: the walk from `a` near the centre `x` of the ball `B_R(x)`
reaches `∂B_{r 0}(z)` after `∂B_R(x)` only with probability at most the explicit survival bound. -/
theorem boundary_hit_le_explicit_gms {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {M : ℝ → ℤ → ℤ → ℕ} {η : ℝ → ℂ} (hη : Continuous η) (hwalk : SeparatingWalkGeom η M)
    {ε β ρ : ℝ} {z x : ℂ} {a : ℤ} {r : ℕ → ℝ} {n : ℕ} {R buffer margin bound : ℝ}
    (cutoff distance factor : ℝ) (hdist : 0 < distance)
    (hscale : distance ≤ factor * cutoff * (2 : ℝ) ^ (n + 1))
    (hε : 0 < ε) (hR : 0 < R) (hbuffer : 0 < buffer) (hmargin : bound ≤ margin) (hr : Antitone r)
    (hgeometry : ∀ i ≤ n, 0 < r i ∧ R + buffer - dist z x + margin < r i / 4 ∧
      Metric.ball z (2 * r i) ⊆ Metric.ball 0 ρ)
    (hsize : ∀ i, (cell ε η i ∩ Metric.ball 0 ρ).Nonempty → Metric.diam (cell ε η i) ≤ bound)
    (ha : a ∈ interiorCellVertices ε η (Metric.ball z (r n)))
    (haS : a ∈ cellVertices ε η (Metric.ball z (r n / 2)))
    (hatarget : a ∈ interiorCellVertices ε η (Metric.ball x R))
    (hadj : ∀ v w, M ε v w ≠ 0 → (cell ε η v ∩ cell ε η w).Nonempty)
    (hnb : ∀ i ≤ n, ∀ v ∈ interiorCellVertices ε η (Metric.ball z (r i)), ∀ w,
      M ε v w ≠ 0 → w ∈ interiorCellVertices ε η (Metric.ball z (r i)) ∪
        cellVertices ε η (Metric.sphere z (r i)))
    (htargetnb : ∀ v ∈ interiorCellVertices ε η (Metric.ball x R), ∀ w, M ε v w ≠ 0 →
      w ∈ interiorCellVertices ε η (Metric.ball x R) ∪ cellVertices ε η (Metric.sphere x R))
    (hfin : ∀ᵐ path ∂srwLaw (M ε) a, vExitTime (interiorCellVertices ε η (Metric.ball z (r 0))) path ≠ ⊤)
    (hnext : ∀ i < n, cellVertices ε η (Metric.sphere z (r (i + 1))) ∩
      cellVertices ε η (Metric.ball z (r (i + 1))) ⊆ cellVertices ε η (Metric.ball z (r i / 2)))
    (hz : z ∈ Metric.ball (0 : ℂ) ρ)
    (hadmiss : ∀ i ≤ n, ε ^ β ≤ r i / 2 ∧ r i / 2 ≤ ρ ∧ Metric.ball z (2 * (r i / 2)) ⊆ Metric.ball 0 ρ)
    (hgood : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
      Metric.ball z (2 * s) ⊆ Metric.ball 0 ρ → ∀ v ∈ cellVertices ε η (Metric.ball z s),
      ENNReal.ofReal p ≤ srwLaw (M ε) v
        {x' | ∀ y ∈ cellVertices ε η (Metric.sphere z (s / 2)),
          walkDisconnectsBeforeHit (M ε) (cellVertices ε η (Metric.sphere z (2 * s))) y x'}) :
    srwLaw (M ε) a {path | vHitTime (cellVertices ε η (Metric.sphere z (r 0))) path ≤
      vHitTime (cellVertices ε η (Metric.sphere x R)) path} ≤
      ENNReal.ofReal ((factor * cutoff / distance) ^ (-Real.log (1 - p) / Real.log 2)) := by
  calc _ ≤ srwLaw (M ε) a {path | ∀ i ≤ n,
        vHitTime (cellVertices ε η (Metric.sphere z (r i))) path ≤
          vHitTime (cellVertices ε η (Metric.sphere x R)) path} := by
        apply measure_mono_ae
        filter_upwards [ae_nestedSphereCellHit_data hη r hr n
          (fun i hi => (hgeometry i hi).1) ha hnb hfin] with path hordered
        intro houter i hi
        exact (hordered.2 0 i (Nat.zero_le i) hi).trans houter
    _ ≤ _ := (srwLaw_sphere_hit_order_le_nested_interior_survival hR hatarget htargetnb
        (fun i => cellVertices ε η (Metric.sphere z (r i))) n).trans
        (safe_survival_le_explicit_gms (radius := fun _ => R) hp hp1 hη hwalk cutoff distance factor
          hdist hscale hε hbuffer hmargin hr hgeometry hsize ha haS hadj hnb hfin hnext hz hadmiss hgood)

/-- Pointwise port of `GMSDyadicBoundaryHit.lean:14`: the dyadic annuli between `cutoff` and `distance` are
chosen by `exists_admissible_dyadic_annulus_scales`, and the boundary-hit bound is applied with factor `1`. -/
theorem dyadic_boundary_hit_le_explicit_gms {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {M : ℝ → ℤ → ℤ → ℕ} {η : ℝ → ℂ} (hη : Continuous η) (hwalk : SeparatingWalkGeom η M)
    {ε β ρ : ℝ} {z x : ℂ} {a : ℤ} {R buffer margin bound cutoff distance : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hbuffer : 0 < buffer) (hmargin : bound ≤ margin)
    (hc : 0 < cutoff) (hd : cutoff ≤ distance) (hmesh : 2 * ε ^ β ≤ cutoff)
    (hclear : 4 * (R + buffer - dist z x + margin) < cutoff)
    (hcontain : 2 * distance + dist z 0 ≤ ρ) (hz : z ∈ Metric.ball (0 : ℂ) ρ)
    (hsize : ∀ i, (cell ε η i ∩ Metric.ball 0 ρ).Nonempty → Metric.diam (cell ε η i) ≤ bound)
    (ha : a ∈ interiorCellVertices ε η (Metric.ball z cutoff))
    (haS : a ∈ cellVertices ε η (Metric.ball z (cutoff / 2)))
    (hatarget : a ∈ interiorCellVertices ε η (Metric.ball x R))
    (hadj : ∀ v w, M ε v w ≠ 0 → (cell ε η v ∩ cell ε η w).Nonempty)
    (hnb : ∀ s : ℝ, ∀ v ∈ interiorCellVertices ε η (Metric.ball z s), ∀ w,
      M ε v w ≠ 0 → w ∈ interiorCellVertices ε η (Metric.ball z s) ∪
        cellVertices ε η (Metric.sphere z s))
    (htargetnb : ∀ v ∈ interiorCellVertices ε η (Metric.ball x R), ∀ w, M ε v w ≠ 0 →
      w ∈ interiorCellVertices ε η (Metric.ball x R) ∪ cellVertices ε η (Metric.sphere x R))
    (hfin : ∀ᵐ path ∂srwLaw (M ε) a, vExitTime (interiorCellVertices ε η (Metric.ball z distance)) path ≠ ⊤)
    (hgood : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
      Metric.ball z (2 * s) ⊆ Metric.ball 0 ρ → ∀ v ∈ cellVertices ε η (Metric.ball z s),
      ENNReal.ofReal p ≤ srwLaw (M ε) v
        {x' | ∀ y ∈ cellVertices ε η (Metric.sphere z (s / 2)),
          walkDisconnectsBeforeHit (M ε) (cellVertices ε η (Metric.sphere z (2 * s))) y x'}) :
    srwLaw (M ε) a {path | vHitTime (cellVertices ε η (Metric.sphere z distance)) path ≤
      vHitTime (cellVertices ε η (Metric.sphere x R)) path} ≤
      ENNReal.ofReal ((cutoff / distance) ^ (-Real.log (1 - p) / Real.log 2)) := by
  obtain ⟨n, r, hr, hlast, hfirst, hscale, hgeometry, hadmiss, hnext⟩ :=
    exists_admissible_dyadic_annulus_scales (η := η) (x := x) hc hd hmesh hclear hcontain
  have ha' : a ∈ interiorCellVertices ε η (Metric.ball z (r n)) := by simpa [hlast] using ha
  have haS' : a ∈ cellVertices ε η (Metric.ball z (r n / 2)) := by simpa [hlast] using haS
  have hsub := interiorCellVertices_concentric_ball_mono (ε := ε) hη z hfirst
  have hfin' : ∀ᵐ path ∂srwLaw (M ε) a,
      vExitTime (interiorCellVertices ε η (Metric.ball z (r 0))) path ≠ ⊤ := by
    filter_upwards [hfin] with path hpath
    exact ne_top_of_le_ne_top hpath (vExitTime_mono_domain hsub path)
  have ha0 := interiorCellVertices_concentric_ball_mono (ε := ε) hη z (hr (Nat.zero_le n)) ha'
  have hdist : 0 < distance := lt_of_lt_of_le hc hd
  have hscale' : distance ≤ 1 * cutoff * (2 : ℝ) ^ (n + 1) := by simpa using hscale
  calc _ ≤ srwLaw (M ε) a {path | vHitTime (cellVertices ε η (Metric.sphere z (r 0))) path ≤
        vHitTime (cellVertices ε η (Metric.sphere x R)) path} :=
        srwLaw_sphere_hit_order_le_of_radius_le hη (hgeometry 0 (Nat.zero_le n)).1 hfirst ha0
          (fun s _ => hnb s) hfin _
    _ ≤ ENNReal.ofReal ((cutoff / distance) ^ (-Real.log (1 - p) / Real.log 2)) := by
        simpa only [one_mul] using
          boundary_hit_le_explicit_gms hp hp1 hη hwalk cutoff distance 1 hdist hscale' hε hR hbuffer
            hmargin hr hgeometry hsize ha' haS' hatarget hadj (fun i _ => hnb (r i)) htargetnb hfin'
            hnext hz hadmiss hgood

/-- Pointwise port of `GMSBoundaryCellHit.lean:15`: the boundary cell `a` of `∂B_r(z)` (cell size `d`) hits
`∂B_{distance}(vertexPoint a)` before `∂B_{r+3d}(z)` with the explicit survival bound. The geometry of the disc
`B_{r+3d}(z)` and of `B_{cutoff}(vertexPoint a)` comes from `disk_dirichlet_decomposition_geometry`. -/
theorem boundary_cell_hit_le_explicit_gms {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {M : ℝ → ℤ → ℤ → ℕ} {η : ℝ → ℂ} (hη : Continuous η)
    (hproper : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hwalk : SeparatingWalkGeom η M)
    {ε β ρ : ℝ} {z : ℂ} {a : ℤ} {r d cutoff distance : ℝ}
    (hadj : ∀ v w, M ε v w ≠ 0 → (cell ε η v ∩ cell ε η w).Nonempty)
    (hlf : IsLocallyFiniteMult (M ε)) (hsucc : ∀ k : ℤ, M ε k (k + 1) ≠ 0)
    (hε : 0 < ε) (hr : 0 < r) (hd : 0 < d) (hcut : 24 * d < cutoff) (hcd : cutoff ≤ distance)
    (hmesh : 2 * ε ^ β ≤ cutoff)
    (hcontain : 2 * distance + dist (vertexPoint ε η a) 0 ≤ ρ)
    (hcenter : vertexPoint ε η a ∈ Metric.ball (0 : ℂ) ρ)
    (hsize : ∀ i, (cell ε η i ∩ Metric.ball 0 ρ).Nonempty → Metric.diam (cell ε η i) ≤ d)
    (hdiam : Metric.diam (cell ε η a) ≤ d)
    (ha : a ∈ cellVertices ε η (Metric.sphere z r))
    (hgood : ∀ z' ∈ Metric.ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
      Metric.ball z' (2 * s) ⊆ Metric.ball 0 ρ → ∀ v ∈ cellVertices ε η (Metric.ball z' s),
      ENNReal.ofReal p ≤ srwLaw (M ε) v
        {x' | ∀ y ∈ cellVertices ε η (Metric.sphere z' (s / 2)),
          walkDisconnectsBeforeHit (M ε) (cellVertices ε η (Metric.sphere z' (2 * s))) y x'}) :
    srwLaw (M ε) a {path | vHitTime (cellVertices ε η (Metric.sphere (vertexPoint ε η a) distance)) path ≤
      vHitTime (cellVertices ε η (Metric.sphere z (r + 3 * d))) path} ≤
      ENNReal.ofReal ((cutoff / distance) ^ (-Real.log (1 - p) / Real.log 2)) := by
  obtain ⟨hstart, hstartS, htarget, hclear⟩ :=
    boundary_cell_annulus_geometry hε.le hη hd hcut hdiam ha
  have hc : 0 < cutoff := by linarith
  have hdist : 0 < distance := lt_of_lt_of_le hc hcd
  have hR : 0 < r + 3 * d := by linarith
  have hnb : ∀ s : ℝ, ∀ v ∈ interiorCellVertices ε η (Metric.ball (vertexPoint ε η a) s), ∀ w,
      M ε v w ≠ 0 → w ∈ interiorCellVertices ε η (Metric.ball (vertexPoint ε η a) s) ∪
        cellVertices ε η (Metric.sphere (vertexPoint ε η a) s) := by
    intro s v hv w hvw
    obtain ⟨q, _, hq⟩ := hv.1
    have hs : 0 < s := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hq)
    exact (disk_dirichlet_decomposition_geometry hε hs hη hproper hadj hlf hsucc
      (z := vertexPoint ε η a)).2.2.1 v hv w hvw
  have hsub := interiorCellVertices_concentric_ball_mono (ε := ε) hη (vertexPoint ε η a) hcd
  have hfin := (disk_dirichlet_decomposition_geometry hε hdist hη hproper hadj hlf hsucc
    (z := vertexPoint ε η a)).2.2.2.2 a (hsub hstart)
  have htargetnb := (disk_dirichlet_decomposition_geometry hε hR hη hproper hadj hlf hsucc
    (z := z)).2.2.1
  exact dyadic_boundary_hit_le_explicit_gms hp hp1 hη hwalk hε hR hd le_rfl hc hcd hmesh hclear
    hcontain hcenter hsize hstart hstartS htarget hadj hnb htargetnb hfin hgood

/-- Pointwise port of `GMSMesoscopicHit.lean:13`, the boundary-cell hit estimate of the discrete excursion lemma
`srwLaw_discrete_exit_excursion_le` (`hbound`), with cell size `d = ε^a`, disconnection exponent `b`, and
mesoscopic scale `ℓ = 100 ε^a + ε^b`: the boundary cell `j` of `∂B_r(z)` reaches `∂B_{distance}(vertexPoint j)`
before `∂B_{r+3ε^a}(z)` with probability at most `(2ℓ/distance)^ν`, `ν = -log(1-p)/log 2`. -/
theorem mesoscopic_boundary_cell_hit_le_explicit_gms {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {M : ℝ → ℤ → ℤ → ℕ} {η : ℝ → ℂ} (hη : Continuous η)
    (hproper : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hwalk : SeparatingWalkGeom η M)
    {ε a b ρ : ℝ} {z : ℂ} {j : ℤ} {r distance : ℝ}
    (hadj : ∀ v w, M ε v w ≠ 0 → (cell ε η v ∩ cell ε η w).Nonempty)
    (hlf : IsLocallyFiniteMult (M ε)) (hsucc : ∀ k : ℤ, M ε k (k + 1) ≠ 0)
    (hε : 0 < ε) (hr : 0 < r) (hscale : 2 * (100 * ε ^ a + ε ^ b) ≤ distance)
    (hcontain : 2 * distance + dist (vertexPoint ε η j) 0 ≤ ρ)
    (hcenter : vertexPoint ε η j ∈ Metric.ball (0 : ℂ) ρ)
    (hsize : ∀ i, (cell ε η i ∩ Metric.ball 0 ρ).Nonempty → Metric.diam (cell ε η i) ≤ ε ^ a)
    (hdiam : Metric.diam (cell ε η j) ≤ ε ^ a)
    (hj : j ∈ cellVertices ε η (Metric.sphere z r))
    (hgood : ∀ z' ∈ Metric.ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ b ≤ s → s ≤ ρ →
      Metric.ball z' (2 * s) ⊆ Metric.ball 0 ρ → ∀ v ∈ cellVertices ε η (Metric.ball z' s),
      ENNReal.ofReal p ≤ srwLaw (M ε) v
        {x' | ∀ y ∈ cellVertices ε η (Metric.sphere z' (s / 2)),
          walkDisconnectsBeforeHit (M ε) (cellVertices ε η (Metric.sphere z' (2 * s))) y x'}) :
    srwLaw (M ε) j {path | vHitTime (cellVertices ε η (Metric.sphere (vertexPoint ε η j) distance)) path ≤
      vHitTime (cellVertices ε η (Metric.sphere z (r + 3 * ε ^ a))) path} ≤
      ENNReal.ofReal ((2 * (100 * ε ^ a + ε ^ b) / distance) ^ (-Real.log (1 - p) / Real.log 2)) := by
  have ha : 0 < ε ^ a := Real.rpow_pos_of_pos hε _
  have hb : 0 < ε ^ b := Real.rpow_pos_of_pos hε _
  exact boundary_cell_hit_le_explicit_gms (β := b) (cutoff := 2 * (100 * ε ^ a + ε ^ b))
    (distance := distance) (d := ε ^ a) hp hp1 hη hproper hwalk hadj hlf hsucc hε hr ha
    (by linarith) hscale (by linarith) hcontain hcenter hsize hdiam hj hgood

/-- The pointwise good-event properties at scale `ε` and environment `ω` used by the excursion lemma: the cell-size
bound (LEMMA36 (b)), and the simultaneous annulus disconnection (LEMMA36 (c), GMS (3.35), in the form of
`GMSUniformRate.lean:13`): for every disc `B_s(c)` with `c ∈ B_{ρ₁}`, `ε^β ≤ s`, `B_{2s}(c) ⊆ B_{ρ₁}`, and every
vertex `v` of `B_s(c)`, the walk from `v` disconnects `V(∂B_{s/2}(c))` from `V(∂B_{2s}(c))` with probability `≥ p`. -/
def LensExcursionGood {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ₁ a β p : ℝ) (ε : ℝ) (ω : Ω) :
    Prop :=
  (∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ₁).Nonempty → diam (cell ε (S.η ω) k) ≤ ε ^ a) ∧
  (∀ (c : ℂ) (s : ℝ), c ∈ ball 0 ρ₁ → ε ^ β ≤ s → ball c (2 * s) ⊆ ball 0 ρ₁ →
    ∀ v ∈ cellVertices ε (S.η ω) (ball c s),
      ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) v {path |
        ∀ y ∈ cellVertices ε (S.η ω) (sphere c (s / 2)),
          walkDisconnectsBeforeHit (S.mult ε ω)
            (cellVertices ε (S.η ω) (sphere c (2 * s))) y path})

/-- **Boundary-excursion half of `hLens` (statement).** For a disc `ball z r ⊆ ball 0 ρ` with `ρ < ρ₁ < 1`, and
`p ≤ 1/2`, there are `C, ε₀` such that for `0 < ε < ε₀` and every environment `ω` with the good-event properties
`LensExcursionGood` at scale `ε`, and with the start vertex `vertexOf ε (S.η ω) y` an interior cell vertex of `ball z r`,
the quenched probability that the walk has a same-walk good exit with displacement `> ε^{b/2}/2` from the projected
exit point is at most `C ε^{νb/2}`, where `b = min a β` and `ν = -log(1-p)/log 2`. -/
def QuenchedLensExcursionStmt : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ ρ₁ a β p r : ℝ) (z y : ℂ),
    0 < ρ → ρ < ρ₁ → ρ₁ < 1 → 0 < r → ball z r ⊆ ball 0 ρ → 0 < a → 0 < β → 0 < p → p ≤ 1 / 2 →
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ ω : Ω,
      LensExcursionGood S ρ₁ a β p ε ω →
      vertexOf ε (S.η ω) y ∈ interiorCellVertices ε (S.η ω) (ball z r) →
      srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
          {x | SameWalkGood S r z ε ω x ∧
            ε ^ (min a β / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)} ≤
        ENNReal.ofReal (C * ε ^ ((-Real.log (1 - p) / Real.log 2) * min a β / 2))

end FirstPass36
end MatedCRT

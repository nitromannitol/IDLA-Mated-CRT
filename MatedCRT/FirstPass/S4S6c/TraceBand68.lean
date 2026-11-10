import MatedCRT.FirstPass.S4S6c.ConfigBound68
import MatedCRT.FirstPass.S4S6c.BandInduction68
import MatedCRT.FirstPass.S4S6c.HcPrinted68
import MatedCRT.FirstPass.S4S6c.StartBand68

/-!
# First pass, Lemma 6.8: the trace bound on the test band (q2, fp-S4S6c-envscaling-6-7-6-8)

Deterministic wrapper of `ConfigBound68.trace_half` for the sphere band. The test band is
`Y = testBand = band ∩ bandSet` (`BandInduction68.band`, `HcPrinted68.bandSet`), the window family is `testWt`
(`HcPrinted68.bandWt Y`, the inner window `I(B_{2R_v}(z_v))` on `Y` and `univ` off `Y`) and the region family is
`testAof` (`S' \ Θ` on `Y`, `∅` off `Y`).

The one-test bound `hc` is `HcPrinted68.hc_band_var` on the sphere band, transferred to `Y`: the stay region of
`SuccessiveExitStop.stayInRegionOf W Aof y` depends only on `W y` and `Aof y`, and `Y ⊆ bandSet`.

The walk of a Good path `x` starts at `x 0`; the band induction (`BandInduction68.band_induction`) gives the test
times and their positions, and `StartBand68.start_mem_band_inter` puts each test position in `Y`, so the windows used
are the inner windows. Probabilistic inputs (almost sure exit finiteness on the windows, the one-test local bound,
the start geometry of the Good paths, the frontier good event) are explicit hypotheses.

Terminology: stopping times of the walk killed on leaving the window (Berestycki-Gwynne; Armitage-Gardiner potential
theory for the window Green bound used in `hloc`).
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRT
namespace TraceBand68

/-- The test band `Y = band ∩ bandSet`: the vertices of the printed band whose own test window contains them. -/
def testBand (H : ℤ → Set ℂ) (P ctr : ℤ → ℂ) (rad : ℤ → ℝ) (F : Set ℂ) (r d : ℝ) : Set ℤ :=
  BandInduction68.band P F r d ∩ HcPrinted68.bandSet H ctr rad

/-- The window family of the trace argument on the test band: `I(B_{2R_v}(z_v))` on `Y`, `univ` off `Y`. -/
noncomputable def testWt (H : ℤ → Set ℂ) (P ctr : ℤ → ℂ) (rad : ℤ → ℝ) (F : Set ℂ) (r d : ℝ) : ℤ → Set ℤ :=
  HcPrinted68.bandWt (testBand H P ctr rad F r d) (fun v => innerVertices H (ball (ctr v) (2 * rad v)))

/-- The region family of the trace argument on the test band: `A` on `Y`, `∅` off `Y`. -/
noncomputable def testAof (H : ℤ → Set ℂ) (P ctr : ℤ → ℂ) (rad : ℤ → ℝ) (F : Set ℂ) (r d : ℝ) (A : Set ℤ) :
    ℤ → Set ℤ :=
  HcPrinted68.bandAof (testBand H P ctr rad F r d) A

/-- On a vertex `v` whose start `P v` is within `3r/100` of the start `P b`, the test window is the inner window. -/
theorem testWt_eq {H : ℤ → Set ℂ} {P ctr : ℤ → ℂ} {rad : ℤ → ℝ} {F : Set ℂ} {r d g : ℝ} {v b : ℤ}
    (hd : 0 ≤ d) (hstart : |Metric.infDist (P b) F - r / 2| ≤ d) (hv : dist (P v) (P b) ≤ 3 * r / 100)
    (hPv : P v ∈ H v)
    (hsm : ∀ v', (closure (H v') ∩ closedBall (ctr v) (2 * rad v)).Nonempty →
      ∀ x ∈ closure (H v'), ∀ y' ∈ closure (H v'), dist x y' ≤ d)
    (hctr : dist (ctr v) (P v) ≤ g) (hR0 : 0 ≤ rad v) (hlt : g + d < 4 * rad v / 3) :
    testWt H P ctr rad F r d v = innerVertices H (ball (ctr v) (2 * rad v)) := by
  have hmem : v ∈ testBand H P ctr rad F r d :=
    StartBand68.start_mem_band_inter hd hstart hv hPv hsm hctr hR0 hlt
  simp only [testWt, HcPrinted68.bandWt_of_mem hmem]

/-- **Centre and radius of a band vertex lie in `ball 0 ρ`.** For `y` in the band `BandInduction68.band`, the start
`P y` is within `r` of `F ⊆ ball 0 (ρ/2)` (Metric.infDist_lt_iff), `dist (ctr y) (P y) ≤ g`, `rad y ≤ s`, and
`g < s ≤ r/1000`, `r ≤ ρ/100`; hence `closedBall (ctr y) (2 * rad y) ⊆ ball 0 ρ`. -/
theorem closedBall_sub_of_band {P ctr : ℤ → ℂ} {rad : ℤ → ℝ} {F : Set ℂ} {r d g s ρ : ℝ} {y : ℤ}
    (hr : 0 < r) (hd0 : 0 ≤ d) (hdr : d ≤ r / 1000) (hsr : s ≤ r / 1000) (hgd : g + d < s)
    (hrρ : r ≤ ρ / 100) (hFne : F.Nonempty) (hFball : F ⊆ ball (0 : ℂ) (ρ / 2))
    (hctr : ∀ v, dist (ctr v) (P v) ≤ g) (hrad : ∀ v ∈ BandInduction68.band P F r d, rad v ≤ s)
    (hy : y ∈ BandInduction68.band P F r d) :
    closedBall (ctr y) (2 * rad y) ⊆ ball (0 : ℂ) ρ := by
  have hy' : |Metric.infDist (P y) F - r / 2| ≤ 3 * r / 100 + 2 * d := hy
  have hinf : Metric.infDist (P y) F < r := by
    have := (abs_le.1 hy').2
    linarith
  obtain ⟨f, hfF, hPf⟩ := (Metric.infDist_lt_iff hFne).1 hinf
  have hf : ‖f‖ < ρ / 2 := mem_ball_zero_iff.1 (hFball hfF)
  have hPy : ‖P y‖ < ρ / 2 + r := by
    have h1 := norm_sub_norm_le (P y) f
    rw [← dist_eq_norm] at h1
    linarith
  have hcP : ‖ctr y‖ - ‖P y‖ ≤ ‖ctr y - P y‖ := norm_sub_norm_le (ctr y) (P y)
  have hcg : ‖ctr y - P y‖ ≤ g := by
    rw [← dist_eq_norm]
    exact hctr y
  have hrady : rad y ≤ s := hrad y hy
  intro z hz
  have hz' : dist z (ctr y) ≤ 2 * rad y := hz
  rw [dist_eq_norm] at hz'
  have hzn : ‖z‖ - ‖ctr y‖ ≤ ‖z - ctr y‖ := norm_sub_norm_le z (ctr y)
  rw [mem_ball_zero_iff]
  linarith

/-- **Diameter bound on the band** (the centre-restricted form of the cell-size input `hsmC`). For `y` in the band,
every cell meeting `closedBall (ctr y) (2 * rad y)` meets `ball 0 ρ` (`closedBall_sub_of_band`), so the cell-size
hypothesis `hsm0` gives its diameter bound `d`. -/
theorem cell_sm_of_band {H : ℤ → Set ℂ} {P ctr : ℤ → ℂ} {rad : ℤ → ℝ} {F : Set ℂ} {r d g s ρ : ℝ} {y : ℤ}
    (hr : 0 < r) (hd0 : 0 ≤ d) (hdr : d ≤ r / 1000) (hsr : s ≤ r / 1000) (hgd : g + d < s)
    (hrρ : r ≤ ρ / 100) (hFne : F.Nonempty) (hFball : F ⊆ ball (0 : ℂ) (ρ / 2))
    (hctr : ∀ v, dist (ctr v) (P v) ≤ g) (hrad : ∀ v ∈ BandInduction68.band P F r d, rad v ≤ s)
    (hsm0 : ∀ v, (H v ∩ ball (0 : ℂ) ρ).Nonempty → ∀ u ∈ closure (H v), ∀ u' ∈ closure (H v), dist u u' ≤ d)
    (hy : y ∈ BandInduction68.band P F r d) (v : ℤ)
    (hv : (closure (H v) ∩ closedBall (ctr y) (2 * rad y)).Nonempty) :
    ∀ x ∈ closure (H v), ∀ y' ∈ closure (H v), dist x y' ≤ d := by
  obtain ⟨z, hzc, hzb⟩ := hv
  have hzB : z ∈ ball (0 : ℂ) ρ :=
    closedBall_sub_of_band hr hd0 hdr hsr hgd hrρ hFne hFball hctr hrad hy hzb
  obtain ⟨w, hwB, hwH⟩ := _root_.mem_closure_iff.1 hzc (ball (0 : ℂ) ρ) isOpen_ball hzB
  exact hsm0 v ⟨w, hwH, hwB⟩

/-- **Trace bound on the test band** (the printed one-test bound `hc` and the window inputs of
`ConfigBound68.trace_half`, derived from the band geometry). Under the cluster geometry of `trace_half`, the
radius and step bounds of `BandInduction68.band_induction`, the Good-path property `hGoodPath` and the local
probabilistic bounds `hfinBS`, `hloc`, the walk from `a` visits `V(U₂) \ (S' ∪ Θ)` before exiting `V(U₂)` with
probability at least `1/2`. -/
theorem trace_band
    {H : ℤ → Set ℂ} {m : ℤ → ℤ → ℕ} {F : Set ℂ} {Θ S' : Set ℤ} {a : ℤ} {r ρ s d g : ℝ} {N : ℕ}
    {P ctr : ℤ → ℂ} {rad : ℤ → ℝ}
    -- cluster geometry (`ConfigBound68.trace_half`)
    (hr : 0 < r) (hd : d < r / 2)
    (hbdd : ∀ v, Bornology.IsBounded (H v)) (hdiamA : Metric.diam (H a) ≤ d)
    (hconn : ∀ v, IsPreconnected (H v)) (hne : ∀ v, (H v).Nonempty)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (H u) ∩ closure (H v)).Nonempty)
    (hF : ∀ k ∈ Θ, H k ⊆ F) (ha : a ∈ vClosure m Θ)
    (hexit : ∀ᵐ x ∂srwLaw m a,
      vExitTime (FrontierSeparation.meetVerts H (Metric.thickening r F)) x ≠ ⊤)
    -- the band and its geometry
    (hFne : F.Nonempty) (hFball : F ⊆ ball (0 : ℂ) (ρ / 2))
    (hPmem : ∀ v, P v ∈ H v) (hctr : ∀ v, dist (ctr v) (P v) ≤ g)
    (hsm0 : ∀ v, (H v ∩ ball (0 : ℂ) ρ).Nonempty → ∀ u ∈ closure (H v), ∀ u' ∈ closure (H v), dist u u' ≤ d)
    (hρ : ∀ y, d < rad y / 4) (hgeo : ∀ y, 4 * rad y / 3 + d + rad y / 4 + d < 2 * rad y)
    (hlt : ∀ y, g + d < 4 * rad y / 3)
    (hrad0 : ∀ v ∈ BandInduction68.band P F r d, 0 ≤ rad v)
    (hrad : ∀ v ∈ BandInduction68.band P F r d, rad v ≤ s)
    (hd0 : 0 ≤ d) (hg : 0 ≤ g) (hs : 0 < s) (hsr : s ≤ r / 1000) (hdr : d ≤ r / 1000)
    (hgd : g + d < s) (hrρ : r ≤ ρ / 100) (hNs : (N : ℝ) * s ≤ r / 100)
    -- the parameters of `trace_half`
    {q0 ζ : ℝ} (hq0 : 0 < q0) (hq0' : q0 ≤ 1) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2) (hr1 : r ≤ 1)
    (hrA : r ≤ (q0 / 200 * ζ ^ 2 / (16 * Real.log 2)) ^ (2 / ζ))
    (hN : r ^ (-ζ) / 200 ≤ N)
    -- probabilistic inputs
    (Good : Set (ℕ → ℤ))
    (hGood : ∀ b ∈ FrontierSeparation.frontierVerts H (Metric.thickening (r / 2) F), srwLaw m b Goodᶜ = 0)
    (hGoodPath : ∀ x ∈ Good, |Metric.infDist (P (x 0)) F - r / 2| ≤ d ∧
      (∀ n : ℕ, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0) ∧
      ∀ i : ℕ, dist (P (x i)) (P (x 0)) ≤ 3 * r / 100 →
        vExitTime (innerVertices H (ball (ctr (x i)) (2 * rad (x i)))) (WalkPotential.pathShift i x) ≠ ⊤)
    (hfinBS : ∀ y ∈ HcPrinted68.bandSet H ctr rad,
      ∀ᵐ x ∂srwLaw m y, vExitTime (innerVertices H (ball (ctr y) (4 * rad y / 3))) x ≠ ⊤)
    (hloc : ∀ y ∈ HcPrinted68.bandSet H ctr rad,
      ∀ b ∈ {b : ℤ | (closure (H b) ∩ Metric.sphere (ctr y) (4 * rad y / 3)).Nonempty},
      srwLaw m b (TestBound68.stayIn (fun b => innerVertices H (ball (P b) (rad y / 4))) (S' \ Θ) b) ≤
        ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2))
    -- the successive exit times and stay sets
    (τ : ℕ → (ℕ → ℤ) → ℕ∞) (S : ℕ → Set (ℕ → ℤ))
    (hτ0 : ∀ x, τ 0 x = 0)
    (hτsucc : ∀ (M : ℕ) (x : ℕ → ℤ) (i : ℕ), τ M x = (i : ℕ∞) →
      τ (M + 1) x = (i : ℕ∞) + vExitTime (testWt H P ctr rad F r d (x i)) (WalkPotential.pathShift i x))
    (hτtop : ∀ M x, τ M x = ⊤ → τ (M + 1) x = ⊤)
    (hS0 : S 0 = univ)
    (hSsucc : ∀ M, S (M + 1) = S M ∩ {x | ∃ k : ℕ, τ M x = k ∧
      WalkPotential.pathShift k x ∈ SuccessiveExitStop.stayInRegionOf (testWt H P ctr rad F r d)
        (testAof H P ctr rad F r d (S' \ Θ)) (x k)}) :
    ENNReal.ofReal (1 / 2) ≤ srwLaw m a
      {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime {v | (H v ∩ Metric.thickening r F).Nonempty} x ∧
        x n ∈ {v | (H v ∩ Metric.thickening r F).Nonempty} \ (S' ∪ Θ)} := by
  -- the diameter bound at every band centre (`closedBall_sub_of_band`, `cell_sm_of_band`)
  have hsmB : ∀ y ∈ BandInduction68.band P F r d, ∀ v, (closure (H v) ∩ closedBall (ctr y) (2 * rad y)).Nonempty →
      ∀ x ∈ closure (H v), ∀ y' ∈ closure (H v), dist x y' ≤ d :=
    fun y hy v hv => cell_sm_of_band hr hd0 hdr hsr hgd hrρ hFne hFball hctr hrad hsm0 hy v hv
  -- the path property: finite test times and test positions in the test band
  have hpath : ∀ x ∈ Good, (∀ j < N, τ j x ≠ ⊤) ∧
      (∀ j < N, ∀ k : ℕ, τ j x = (k : ℕ∞) → x k ∈ testBand H P ctr rad F r d) := by
    intro x hx
    obtain ⟨hstart, hlegal, hfinW⟩ := hGoodPath x hx
    have hWt : ∀ v, dist (P v) (P (x 0)) ≤ 3 * r / 100 →
        testWt H P ctr rad F r d v = innerVertices H (ball (ctr v) (2 * rad v)) :=
      fun v hv => testWt_eq hd0 hstart hv (hPmem v) (hsmB v (BandInduction68.mem_band_of_dist hd0 hstart hv))
        (hctr v) (by linarith [hρ v]) (hlt v)
    have hfinW' : ∀ i : ℕ, dist (P (x i)) (P (x 0)) ≤ 3 * r / 100 →
        vExitTime (testWt H P ctr rad F r d (x i)) (WalkPotential.pathShift i x) ≠ ⊤ := by
      intro i hi
      rw [testWt_eq hd0 hstart hi (hPmem (x i)) (hsmB (x i) (BandInduction68.mem_band_of_dist hd0 hstart hi))
        (hctr (x i)) (by linarith [hρ (x i)]) (hlt (x i))]
      exact hfinW i hi
    have key := BandInduction68.band_induction (b := x 0) (x := x) (τ := τ) hconn hadj hPmem hsm0 hFne hFball
      hctr hWt hrad0 hrad hr hrρ hs hsr hd0 hdr hg hgd hNs hstart hτ0 hτsucc rfl hlegal hfinW'
    refine ⟨fun j hj => ?_, fun j hj k hk => ?_⟩
    · obtain ⟨i, hi, -⟩ := key j (by omega)
      rw [hi]
      exact ENat.natCast_ne_top i
    · obtain ⟨i, hi, hdist⟩ := key j (by omega)
      rw [hi] at hk
      have hik : i = k := by exact_mod_cast hk
      have hdist' : dist (P (x k)) (P (x 0)) ≤ 3 * r / 100 := by
        rw [← hik]
        exact le_trans hdist (BandInduction68.js_bound hs (by omega) hNs)
      exact StartBand68.start_mem_band_inter hd0 hstart hdist' (hPmem (x k))
        (hsmB (x k) (BandInduction68.mem_band_of_dist hd0 hstart hdist')) (hctr (x k))
        (by linarith [hρ (x k)]) (hlt (x k))
  -- the one-test bound on the test band
  have hc : ∀ y ∈ testBand H P ctr rad F r d,
      srwLaw m y (SuccessiveExitStop.stayInRegionOf (testWt H P ctr rad F r d)
        (testAof H P ctr rad F r d (S' \ Θ)) y) ≤ ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2) := by
    intro y hy
    have hy' : y ∈ BandInduction68.band P F r d ∧ y ∈ HcPrinted68.bandSet H ctr rad := hy
    -- the local one-test bound at the band centre `y` (`HcAssembly68.hc_of_local`, with `hsmB y`)
    have h := HcAssembly68.hc_of_local (A := S' \ Θ)
      (c := ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2)) hconn hne hd0 (hsmB y hy'.1) hadj hPmem
      (hgeo y) (hρ y) hy'.2 (hfinBS y hy'.2) (hloc y hy'.2)
    simp only [SuccessiveExitStop.stayInRegionOf, testWt, testAof, HcPrinted68.bandWt_of_mem hy,
      HcPrinted68.bandAof_of_mem hy]
    exact h
  have hAY : ∀ y ∉ testBand H P ctr rad F r d, testAof H P ctr rad F r d (S' \ Θ) y = ∅ :=
    fun y hy => HcPrinted68.bandAof_of_not_mem hy
  have hWY : ∀ y ∉ testBand H P ctr rad F r d, testWt H P ctr rad F r d y = univ :=
    fun y hy => HcPrinted68.bandWt_of_not_mem hy
  have hAof : ∀ y ∈ testBand H P ctr rad F r d, testAof H P ctr rad F r d (S' \ Θ) y = S' \ Θ :=
    fun y hy => HcPrinted68.bandAof_of_mem hy
  have hWU : ∀ y ∈ testBand H P ctr rad F r d,
      testWt H P ctr rad F r d y ⊆ FrontierSeparation.meetVerts H (Metric.thickening r F) \ Θ := by
    intro y hy
    have hy' : y ∈ BandInduction68.band P F r d ∧ y ∈ HcPrinted68.bandSet H ctr rad := hy
    have hw := BandInduction68.window_sub (Wt := fun v => innerVertices H (ball (ctr v) (2 * rad v)))
      hconn hne hF hFne hctr (fun v => rfl) hrad hr hsr hd0 hdr hg hgd y hy'.1
    have e : testWt H P ctr rad F r d y = innerVertices H (ball (ctr y) (2 * rad y)) := by
      simp only [testWt, HcPrinted68.bandWt_of_mem hy]
    rw [e]
    exact hw
  exact ConfigBound68.trace_half hr hd hbdd hdiamA hconn hne hadj hF ha hexit
    (testWt H P ctr rad F r d) (testAof H P ctr rad F r d (S' \ Θ)) (testBand H P ctr rad F r d) τ S hτ0 hτsucc
    hτtop hS0 hSsucc hq0 hq0' hζ hζ' hr1 hrA hc hAY hWY N hN Good hGood (fun x hx => (hpath x hx).1)
    (fun x hx => (hpath x hx).2) hWU hAof

end TraceBand68
end MatedCRT

#print axioms MatedCRT.TraceBand68.testWt_eq
#print axioms MatedCRT.TraceBand68.trace_band

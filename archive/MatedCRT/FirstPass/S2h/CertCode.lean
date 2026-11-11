import MatedCRT.FirstPass.S2h.CertForward2

/-!
# The certificate code: test family and the forward direction

The moment code `localCode φs ν` of a locally finite measure against the countable test family `φs` of the certificate.
Coordinate `certIdx k J n` carries the restricted moment `D_k θ_{J,n}`: `D_k` times the cutoff of the
union of the charged balls `U i`, `i ∈ J`. The forward direction: a certificate of `CertReal` gives a witness of
`CertRel` for its code (clauses C1-C4 of `certRel_clauses_C1_C3` and `certC4_of_cert`), so a plateau pair of
certificates puts the code in the analytic set `B` of `analyticSet_certCodes`.
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

/-- Moment code of a measure on the test family `φs`: `k ↦ ∫ φs k dν`. -/
noncomputable def localCode (φs : ℕ → ℂ → ℝ) (ν : Measure ℂ) : ℕ → ℝ := fun k => ∫ x, φs k x ∂ν

/-- A measure with finite mass on every closed disc `B̄_n` has finite mass on compact sets. -/
theorem isFiniteMeasureOnCompacts_of_locFin {ν : Measure ℂ} (h : ∀ n : ℕ, ν (closedBall (0 : ℂ) n) < ⊤) :
    IsFiniteMeasureOnCompacts ν := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  exact lt_of_le_of_lt (measure_mono (hr.trans (closedBall_subset_closedBall (Nat.le_ceil r)))) (h ⌈r⌉₊)

/-- The coordinates of the certificate code: `(k, J, n)` is coded by `Encodable.encode`. -/
noncomputable def certIdx : ℕ → Finset ℕ → ℕ → ℕ := fun k J n => Encodable.encode (k, J, n)

/-- The test family of the certificate code: the coordinate `p` decodes to `(k, J, n)` and carries
`D k` times the cutoff `θ_{J,n}` of the charged balls `⋃ i ∈ J, U i ∩ B_1`; the other coordinates vanish. -/
noncomputable def certPhi (D : ℕ → ℂ → ℝ) (U : ℕ → Set ℂ) (p : ℕ) : ℂ → ℝ :=
  match (Encodable.decode p : Option (ℕ × Finset ℕ × ℕ)) with
  | some (k, J, n) => fun x => D k x * cutoffBall (⋃ i ∈ J, U i ∩ ball (0 : ℂ) 1) n x
  | none => fun _ => 0

theorem certPhi_certIdx (D : ℕ → ℂ → ℝ) (U : ℕ → Set ℂ) (k : ℕ) (J : Finset ℕ) (n : ℕ) :
    certPhi D U (certIdx k J n) = fun x => D k x * cutoffBall (⋃ i ∈ J, U i ∩ ball (0 : ℂ) 1) n x := by
  simp only [certPhi, certIdx, Encodable.encodek]

/-- The Laplacian pairing of a witness against the test family `D`: the functional `L k` of `CertRel`. -/
noncomputable def certL (D : ℕ → ℂ → ℝ) (k : ℕ) (w : DiscW) : ℝ :=
  ∫ x, extW w x * Laplacian.laplacian (D k) x

/-- The Laplacian pairings are continuous in the witness (`continuous_laplacian_pairing`). -/
theorem certL_continuous {D : ℕ → ℂ → ℝ} (hD : ∀ k, IsTestFunction (ball (0 : ℂ) (3 / 4)) (D k)) (k : ℕ) :
    Continuous (certL D k) :=
  continuous_laplacian_pairing (hD k)

/-- **Forward direction.** A certificate `v` of `CertReal ν t` at a positive time gives a witness of
`CertRel` for the code of `ν`, with witness `discOfCert` of `v` on `B̄_{3/4}`. -/
theorem certRel_of_certReal {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν] (hpole : FrozenGreenDiscPole)
    {z : ℕ → closedBall (0 : ℂ) (3 / 4)} (hz : ∀ j, (z j : ℂ) ∈ ball (0 : ℂ) (3 / 4) \ {0})
    (hzd : ∀ O : Set ℂ, IsOpen O → (O ∩ (ball (0 : ℂ) (3 / 4) \ {0})).Nonempty → ∃ j, (z j : ℂ) ∈ O)
    {b : ℕ → closedBall (0 : ℂ) (3 / 4)} (hb : ∀ j, ‖(b j : ℂ)‖ = 3 / 4)
    {U : ℕ → Set ℂ} (hopen : ∀ V, IsOpen (U V)) (hne : ∀ V, (U V).Nonempty)
    (hreg : ∀ O : Set ℂ, IsOpen O → ∀ x ∈ O, ∃ V, x ∈ U V ∧ closure (U V) ⊆ O)
    {D : ℕ → ℂ → ℝ} (hD : ∀ k, IsTestFunction (ball (0 : ℂ) (3 / 4)) (D k)) (hD0 : ∀ k x, 0 ≤ D k x)
    {t : ℝ} (ht : 0 < t) {v : ℂ → ℝ} (hv : CertReal ν t v) :
    CertRel z b U certIdx (certL D) (localCode (certPhi D U) ν) t (discOfCert hv.1) := by
  have hm : ∀ k J n, localCode (certPhi D U) ν (certIdx k J n) =
      ∫ x, D k x * cutoffBall (⋃ i ∈ J, U i ∩ ball (0 : ℂ) 1) n x ∂ν := fun k J n => by
    simp only [localCode, certPhi_certIdx]
  obtain ⟨c1, c2, c3, c4⟩ := certRel_clauses_C1_C3 hpole ht hv hz hzd hb (discOfCert hv.1) (fun _ => rfl)
  unfold CertRel
  exact ⟨c1, c2, c3, c4, fun k => certC4_of_cert (idx := certIdx) (m := localCode (certPhi D U) ν) hpole ht hv
    hz hzd hopen hne hreg hD hD0 hm (fun _ => rfl) k⟩

/-- **Plateau pairs give the code set.** If `ν` carries a
rational plateau pair of certificates, its code lies in the set `B` of the relation witnesses of `analyticSet_certCodes`. -/
theorem localCode_mem_of_plateau {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν] (hpole : FrozenGreenDiscPole)
    {z : ℕ → closedBall (0 : ℂ) (3 / 4)} (hz : ∀ j, (z j : ℂ) ∈ ball (0 : ℂ) (3 / 4) \ {0})
    (hzd : ∀ O : Set ℂ, IsOpen O → (O ∩ (ball (0 : ℂ) (3 / 4) \ {0})).Nonempty → ∃ j, (z j : ℂ) ∈ O)
    {b : ℕ → closedBall (0 : ℂ) (3 / 4)} (hb : ∀ j, ‖(b j : ℂ)‖ = 3 / 4)
    {U : ℕ → Set ℂ} (hopen : ∀ V, IsOpen (U V)) (hne : ∀ V, (U V).Nonempty)
    (hreg : ∀ O : Set ℂ, IsOpen O → ∀ x ∈ O, ∃ V, x ∈ U V ∧ closure (U V) ⊆ O)
    {D : ℕ → ℂ → ℝ} (hD : ∀ k, IsTestFunction (ball (0 : ℂ) (3 / 4)) (D k)) (hD0 : ∀ k x, 0 ≤ D k x)
    (hplat : HasRatPlateauCert ν) :
    localCode (certPhi D U) ν ∈ {m : ℕ → ℝ | ∃ p q : ℚ, 0 < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧
      ∃ w : DiscW, CertRel z b U certIdx (certL D) m (p : ℝ) w ∧
        ∃ w' : DiscW, CertRel z b U certIdx (certL D) m (q : ℝ) w'} := by
  obtain ⟨p, q, hp, hpq, ⟨v, hv⟩, ⟨v', hv'⟩⟩ := hplat
  exact ⟨p, q, hp, hpq, discOfCert hv.1.1,
    certRel_of_certReal hpole hz hzd hb hopen hne hreg hD hD0 hp hv.1, discOfCert hv'.1.1,
    certRel_of_certReal hpole hz hzd hb hopen hne hreg hD hD0 (lt_trans hp hpq) hv'.1⟩

/-- Coordinates of the certificate code: the moment of `D k` against the cutoff `θ_{J,n}` is `localCode` of `certPhi`. -/
theorem localCode_certIdx (D : ℕ → ℂ → ℝ) (U : ℕ → Set ℂ) (ν : Measure ℂ) (k : ℕ) (J : Finset ℕ) (n : ℕ) :
    localCode (certPhi D U) ν (certIdx k J n) =
      ∫ x, D k x * cutoffBall (⋃ i ∈ J, U i ∩ ball (0 : ℂ) 1) n x ∂ν := by
  simp only [localCode, certPhi_certIdx]

/-- Coordinates which do not decode to a triple carry the zero test function. -/
theorem certPhi_of_decode_none (D : ℕ → ℂ → ℝ) (U : ℕ → Set ℂ) {p : ℕ}
    (h : Encodable.decode (α := ℕ × Finset ℕ × ℕ) p = none) : certPhi D U p = fun _ => 0 := by
  simp only [certPhi, h]

/-- Coordinates decoding to `(k, J, n)` carry `D k` times the cutoff `θ_{J,n}`. -/
theorem certPhi_of_decode_some (D : ℕ → ℂ → ℝ) (U : ℕ → Set ℂ) {p k : ℕ} {J : Finset ℕ} {n : ℕ}
    (h : Encodable.decode (α := ℕ × Finset ℕ × ℕ) p = some (k, J, n)) :
    certPhi D U p = fun x => D k x * cutoffBall (⋃ i ∈ J, U i ∩ ball (0 : ℂ) 1) n x := by
  simp only [certPhi, h]

end MatedCRT

import MatedCRT.Proofs.Sec2.CellSizeHalf.Main
import MatedCRT.FirstPass.Derived.CellDiamLowerOfVolumeGrowth
import MatedCRT.FirstPass.Derived.CoreExitTimeFromBG20

/-!
# Lemma 2.8 (BG20 Lemma 2.4) from the coupling of the quantum cone with a whole-plane GFF

The cell size estimate `CellSizeEstimateStmt` (Lemma 2.8, lemma:cell-size-estimate, line 669; BG20 Lemma 2.4) has two
halves.
* The lower half `ε^{2/(2-γ)² + ζ} ≤ diam(H^ε_a)` follows from the volume growth estimate of Lemma 2.7
  (`MatedCRTEnv.IsValid.polyHighProb_cellDiam_lower`), and Lemma 2.7 is the theorem `volumeGrowthStmt_holds`.
* The upper half `diam(H^ε_a) ≤ ε^{2/(2+γ)² - ζ}` (GMS19 Lemma 2.7) is `cellSizeUpperStmt_of_coupling`: Leonardo
  Bonanno's formalization of GMS19 Lemma 2.7 (as ported to Lattice-Probability), applied with the segment-ball field
  of the mating-of-trees coupling, the GHM15 Lemma 3.12 lower tail and the comparison `μ_{h̃} ≤ μ_h` on `B_1`, which
  is proved from the coupling `ConeWholePlaneCouplingStep` of the quantum cone with a whole-plane GFF on `B_1`
  (DMS14 Definition 4.10).

So Lemma 2.8 holds for every space-filling SLE model, given only that coupling step.
-/

namespace MatedCRT.FirstPass.Derived

/-- **Lemma 2.8** (BG20 Lemma 2.4) from the coupling of the `γ`-quantum cone on `B_1` with a whole-plane GFF minus
`γ log |·|` (`ConeWholePlaneCouplingStep`): with polynomially high probability as `ε → 0`, every cell `H^ε_a` which
meets `B_ρ` has `ε^{2/(2-γ)² + ζ} ≤ diam(H^ε_a) ≤ ε^{2/(2+γ)² - ζ}`. -/
theorem cellSizeEstimateStmt_of_coneCoupling (hcpl : MatedCRT.ConeWholePlaneCouplingStep)
    (𝒮 : MatedCRT.SpaceFillingSLEModel) : MatedCRT.CellSizeEstimateStmt 𝒮 :=
  MatedCRT.cellSizeEstimateStmt_of_volumeGrowth volumeGrowthStmt_holds
    (MatedCRT.cellSizeUpperStmt_of_coupling hcpl 𝒮)

end MatedCRT.FirstPass.Derived

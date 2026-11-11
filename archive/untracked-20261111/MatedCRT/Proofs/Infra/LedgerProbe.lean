import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Final
import MatedCRT.Proofs.Sec6.AnnulusHit.Main
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Main

/-! PROBE (worker A, not to be committed): theorems of the directly imported modules concluding a `...Stmt`/`...Step`,
with their named hypotheses and the number `+k` of other explicit hypotheses. -/

open Lean Elab Command

partial def ledgerHyps : Expr → List String × Nat
  | .forallE _ t b bi =>
    let (hs, k) := ledgerHyps b
    match t.getAppFn.constName? with
    | some c =>
      if ["Stmt", "Step", "Input"].any (c.toString.endsWith ·) then
        ((c.componentsRev.headD Name.anonymous).toString :: hs, k)
      else if bi.isExplicit && c != `MatedCRT.SpaceFillingSLEModel then (hs, k + 1) else (hs, k)
    | none => if bi.isExplicit then (hs, k + 1) else (hs, k)
  | _ => ([], 0)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.imports.map (·.module)
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless ci matches .thmInfo _ do continue
    let some mn ← findModuleOf? n | continue
    unless mods.contains mn do continue
    let some c := ci.type.getForallBody.getAppFn.constName? | continue
    unless ["Stmt", "Step"].any (c.toString.endsWith ·) do continue
    let (hs, k) := ledgerHyps ci.type
    out := out.push s!"{n}: {hs} +{k} ⊢ {(c.componentsRev.headD Name.anonymous).toString}"
  for s in out.qsort (· < ·) do logInfo s

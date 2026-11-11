import Lean

/-! PROBE (worker A, not to be committed): a grep over MatedCRT/. -/

partial def probeWalk (p : System.FilePath) : IO (Array System.FilePath) := do
  let mut acc := #[]
  for d in (← p.readDir) do
    if (← d.path.isDir) then acc := acc ++ (← probeWalk d.path)
    else if d.path.extension == some "lean" then acc := acc.push d.path
  return acc

def probeHas (l p : String) : Bool := (l.splitOn p).length > 1

/-- Lines of `.lean` files under `MatedCRT/` whose path contains one of `fileSubs` (all files if empty) and which
contain one of `pats`. -/
def probeGrep (pats : List String) (fileSubs : List String := []) (maxHits : Nat := 60) : IO Unit := do
  let files ← probeWalk "MatedCRT"
  let mut hits := 0
  for f in files.qsort (·.toString < ·.toString) do
    unless fileSubs.isEmpty || fileSubs.any (probeHas f.toString) do continue
    if probeHas f.toString "SourceProbe" then continue
    let ls := (← IO.FS.readFile f).splitOn "\n"
    let mut i := 0
    for l in ls do
      i := i + 1
      if pats.any (probeHas l) then
        hits := hits + 1
        if hits ≤ maxHits then IO.println s!"{(f.toString.drop 9).toString}:{i}: {(l.take 140).toString}"
  IO.println s!"-- {hits} hits for {pats}"

/-- For each pattern, the files (outside the declaring line) using it, with counts. -/
def probeUses (pats : List String) : IO Unit := do
  let files ← probeWalk "MatedCRT"
  for p in pats do
    let mut acc : Array String := #[]
    for f in files.qsort (·.toString < ·.toString) do
      if probeHas f.toString "SourceProbe" then continue
      let ls := (← IO.FS.readFile f).splitOn "\n"
      let n := (ls.filter (probeHas · p)).length
      if n > 0 then acc := acc.push s!"{(f.toString.drop 16).toString}({n})"
    IO.println s!"{p}: {acc.toList}"

-- Usage (add temporarily, remove before leaving the file): `#eval probeGrep ["pat"] ["path-substring"] 60`,
-- `#eval probeUses ["name"]`.

/-- In files modified after `since` (Unix seconds), each line matching `pats` (not a `have`/`show`), printed with the
nearest preceding top-level `theorem`/`lemma` line. -/
def probeRecent (since : Int) (pats : List String) (fileSubs : List String := []) (maxHits : Nat := 200) :
    IO Unit := do
  let files ← probeWalk "MatedCRT"
  let mut hits := 0
  for f in files.qsort (·.toString < ·.toString) do
    if probeHas f.toString "SourceProbe" then continue
    unless fileSubs.isEmpty || fileSubs.any (probeHas f.toString) do continue
    let md ← f.metadata
    if md.modified.sec ≤ since then continue
    IO.println s!"## {(f.toString.drop 9).toString}"
    let ls := (← IO.FS.readFile f).splitOn "\n"
    let mut i := 0
    let mut decl := ""
    for l in ls do
      i := i + 1
      if l.startsWith "theorem " || l.startsWith "lemma " || l.startsWith "private theorem " ||
          l.startsWith "protected theorem " then
        decl := s!"{i}: {(l.take 90).toString}"
      if pats.any (probeHas l) && !(probeHas l "have ") && !(probeHas l "show ") then
        hits := hits + 1
        if hits ≤ maxHits then IO.println s!"  {decl}  =>  {i}: {(l.take 60).toString}"
  IO.println s!"-- {hits} hits"

/-- The identifier before `:=` on a conclusion line (dropping a trailing `𝒮`). -/
def probeConclName (l : String) : String :=
  let pre := (l.splitOn ":=").headD ""
  let toks := (pre.splitOn " ").filter (· ≠ "")
  let toks := if toks.getLast? == some "𝒮" then toks.dropLast else toks
  (toks.getLast?.getD "?")

/-- One line per file: `decl@line⊢Concl` for each top-level theorem whose conclusion line names an identifier ending
in one of `ends`. -/
def probeConcl (ends : List String) (fileSubs : List String := []) : IO Unit := do
  let files ← probeWalk "MatedCRT"
  for f in files.qsort (·.toString < ·.toString) do
    let fs := f.toString
    if ["SourceProbe", "Scratch", "NameCheck", "Audit/"].any (probeHas fs) then continue
    unless fileSubs.isEmpty || fileSubs.any (probeHas fs) do continue
    let ls := (← IO.FS.readFile f).splitOn "\n"
    let mut i := 0
    let mut decl := ""
    let mut out : Array String := #[]
    let mut last := ""
    for l in ls do
      i := i + 1
      if l.startsWith "theorem " || l.startsWith "lemma " || l.startsWith "private theorem " ||
          l.startsWith "protected theorem " then
        let ts := (l.splitOn " ").filter (· ≠ "")
        decl := s!"{(ts.dropWhile (fun t => t != "theorem" && t != "lemma")).drop 1 |>.headD "?"}@{i}"
      if probeHas l ":=" && !(probeHas l "have ") && !(probeHas l "show ") && !(probeHas l "def ") &&
          !(probeHas l "let ") then
        let c := probeConclName l
        if ends.any (c.endsWith ·) && decl != last then
          out := out.push s!"{decl}⊢{c}"
          last := decl
    unless out.isEmpty do IO.println s!"{(fs.drop 9).toString}: {", ".intercalate out.toList}"

/-- Lines starting with one of `starts` (after trimming) that contain one of `pats`. -/
def probeDefs (starts pats : List String) (maxHits : Nat := 120) : IO Unit := do
  let files ← probeWalk "MatedCRT"
  let mut hits := 0
  for f in files.qsort (·.toString < ·.toString) do
    let fs := f.toString
    if ["SourceProbe", "LedgerProbe", "Scratch", "NameCheck", "PrintScratch"].any (probeHas fs) then continue
    let ls := (← IO.FS.readFile f).splitOn "\n"
    let mut i := 0
    for l in ls do
      i := i + 1
      let t : String := String.ofList (l.toList.dropWhile (· == ' '))
      if starts.any (fun s => t.startsWith s) && pats.any (probeHas l) then
        hits := hits + 1
        if hits ≤ maxHits then IO.println s!"{(fs.drop 9).toString}:{i}: {(l.take 110).toString}"
  IO.println s!"-- {hits} hits"

/-- Lines of the file `f` containing one of `pats`. -/
def probeFile (f : System.FilePath) (pats : List String) (maxHits : Nat := 80) : IO Unit := do
  let ls := (← IO.FS.readFile f).splitOn "\n"
  let mut i := 0
  let mut hits := 0
  for l in ls do
    i := i + 1
    if pats.any (probeHas l) then
      hits := hits + 1
      if hits ≤ maxHits then IO.println s!"{i}: {(l.take 120).toString}"
  IO.println s!"-- {f}: {hits} hits"

#eval probeDefs ["theorem ", "lemma ", "def ", "noncomputable def "] ["greenKernel", "LeastSupersolution",
  "leastSupersolution", "GreenKernelHarmonicStep", "IsVConnected m {", "isVConnected_singleton"] 70

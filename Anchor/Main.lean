import Anchor.Signoff

/-!
# `lake exe anchor`

    anchor sign --module M --decl D --reviewer R --sentence S [--date YYYY-MM-DD] [--file F]
    anchor check [--file F]
    anchor surface --module M --decl D [--json]
    anchor hash --module M --decl D

`sign` appends a sign-off to `F` (default `signoffs.jsonl`). `check` recomputes the surface of
every sign-off in `F` and prints `current` or `STALE` with what changed; it exits 1 when any
sign-off is stale and 2 when `F` holds none, so an empty file never passes. The modules named
must already be built. The executable links only the Lean-only part of Anchor; the modules it
checks are loaded from their compiled files, as `lean` loads them.
-/

open Lean Meta Anchor

/-- The value following `--flag`, if present. -/
def flag (args : List String) (name : String) : Option String :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => some v
  | _ => none

/-- Import `mods` and run `x` in the resulting environment. -/
def runIn {α : Type} (mods : Array Name) (x : MetaM α) : IO α := do
  let env ← importModules (mods.map fun m => { module := m }) {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<anchor>", fileMap := default, maxHeartbeats := 0 }
  let (a, _) ← (x.run' {} {}).toIO ctx { env }
  return a

/-- The value of a required flag, or an error naming it. -/
def need (args : List String) (name : String) : IO String := do
  let some v := flag args name | throw <| IO.userError s!"missing {name}"
  return v

/-- Today's date in UTC, from the system clock. -/
def today : IO String := do
  let out ← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%d"] }
  return out.stdout.trim

/-- Read every sign-off in `path`. -/
def readRecords (path : System.FilePath) : IO (Array Signoff.Record) := do
  unless ← path.pathExists do return #[]
  let mut out := #[]
  for line in (← IO.FS.lines path) do
    if line.trim.isEmpty then continue
    match Json.parse line >>= Signoff.Record.fromJson? with
    | .ok r => out := out.push r
    | .error e => throw <| IO.userError s!"{path}: unreadable sign-off: {e}"
  return out

/-- `anchor sign`. -/
def cmdSign (args : List String) : IO UInt32 := do
  let m := (← need args "--module").toName
  let d := (← need args "--decl").toName
  let reviewer ← need args "--reviewer"
  let sentence ← need args "--sentence"
  let date ← match flag args "--date" with
    | some v => pure v
    | none => today
  let file := (flag args "--file").getD "signoffs.jsonl"
  let r ← runIn #[m] do
    unless (← getEnv).contains d do throwError "{d} is not declared in {m}"
    Signoff.sign d m sentence reviewer date
  IO.FS.withFile file .append fun h => h.putStrLn r.toJson.compress
  IO.println s!"signed {d} ({r.entries.size} constants, sha256 {r.sha256})"
  return 0

/-- `anchor check`. -/
def cmdCheck (args : List String) : IO UInt32 := do
  let file := (flag args "--file").getD "signoffs.jsonl"
  let rs ← readRecords file
  if rs.isEmpty then
    IO.println s!"no sign-offs in {file}: nothing checked"
    return 2
  let mods := rs.foldl (init := #[]) fun a r => if a.contains r.module then a else a.push r.module
  let lines ← runIn mods do
    rs.mapM fun r => do
      let d ← Signoff.check r
      if d.isEmpty then
        return (false, s!"current  {r.decl}  ({r.reviewer}, {r.date})")
      else
        return (true, s!"STALE    {r.decl}  ({r.reviewer}, {r.date}): {d.render}")
  for (_, l) in lines do IO.println l
  let stale := (lines.filter (·.1)).size
  IO.println s!"{rs.size} sign-offs, {rs.size - stale} current, {stale} stale"
  return if stale == 0 then 0 else 1

/-- `anchor surface`. -/
def cmdSurface (args : List String) : IO UInt32 := do
  let m := (← need args "--module").toName
  let d := (← need args "--decl").toName
  let out ← runIn #[m] do
    let es ← Surface.compute d
    if args.contains "--json" then
      return (Surface.renderJson #[d] {} es).pretty
    else
      return Surface.render #[d] es
  IO.println out
  return 0

/-- `anchor hash`. -/
def cmdHash (args : List String) : IO UInt32 := do
  let m := (← need args "--module").toName
  let d := (← need args "--decl").toName
  let hs ← runIn #[m] (Signoff.surfaceHashes d)
  for (n, h) in hs do IO.println s!"{h}  {n}"
  IO.println s!"{Signoff.surfaceHash hs}  (surface)"
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  try
    match args with
    | "sign" :: rest => cmdSign rest
    | "check" :: rest => cmdCheck rest
    | "surface" :: rest => cmdSurface rest
    | "hash" :: rest => cmdHash rest
    | _ =>
      IO.println "usage: anchor (sign | check | surface | hash) ..."
      return (64 : UInt32)
  catch e =>
    IO.eprintln s!"anchor: {e}"
    return (3 : UInt32)

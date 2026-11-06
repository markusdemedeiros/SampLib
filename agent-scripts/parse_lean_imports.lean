import Lean.Elab.Import

/-- Read dependency names with Lean's actual header parser. -/
def main (paths : List String) : IO Unit := do
  for path in paths do
    let source ← IO.FS.readFile path
    let (imports, _, messages) ← Lean.Elab.parseImports source (some path)
    if messages.hasErrors then
      throw <| IO.userError s!"Invalid Lean import header: {path}"
    let output := Lean.Json.mkObj [
      ("path", .str path),
      ("imports", .arr (imports.map fun entry => .str entry.module.toString))]
    IO.println output.compress

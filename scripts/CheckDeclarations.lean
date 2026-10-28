module

public import Lean

@[expose] public section

/-! # Blueprint declaration validation without a native Lake executable -/

open Lean

def main (args : List String) : IO UInt32 := do
  let [filename] := args
    | IO.eprintln "Usage: lake env lean --run scripts/CheckDeclarations.lean FILE"; return 1
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Sidon }] {}
  let mut ok := true
  for line in ← IO.FS.lines filename do
    let name := line.trimAscii.toString.toName
    unless env.contains name do
      IO.eprintln s!"Missing declaration: {name}"
      ok := false
  return if ok then 0 else 1

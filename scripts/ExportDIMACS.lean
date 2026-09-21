import JSP000746.DIMACS

open JSP000746.DIMACS

/-!
Executable-only deterministic exporter.  It serializes the proved Lean value
`renderCoreDIMACS`; it does not invoke a SAT solver.
-/

def main : IO Unit := do
  IO.FS.createDirAll "certificates"
  IO.FS.writeFile "certificates/core.cnf" renderCoreDIMACS

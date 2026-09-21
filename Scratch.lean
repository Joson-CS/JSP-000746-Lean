import JSP000746.LRAT

open JSP000746 JSP000746.DIMACS JSP000746.SATEncoding

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

@[simp] theorem edgeToVar_val_closed (e : EdgeVar) :
    (edgeToVar e).1 =
      ((e.1.1.1 - 1) * (36 - e.1.1.1)) / 2 + (e.1.2.1 - e.1.1.1) := by
  decide +revert

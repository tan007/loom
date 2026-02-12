import Loom.SMT

set_option trace.loom.smt.debug true
set_option trace.loom.smt.result true
set_option loom.solver.smt.timeout 10

-- Non-linear: multiplication
example (x y : Int) (h : x * y = 12) (h2 : x = 3) : y = 4 := by
  loom_smt [h, h2]

-- Division (may fail)
-- example (x y : Int) (h : x / y = 3) (h2 : y = 4) : x = 12 := by
--   loom_smt [h, h2]



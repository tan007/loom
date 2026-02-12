import Loom.SMT

set_option trace.loom.smt.debug true
set_option trace.loom.smt.result true
set_option trace.loom.smt.query true

-- Simple arithmetic test for loom_smt
example (x y : Int) (h : x + y = 10) (h2 : x = 3) : y = 7 := by
  loom_smt [h, h2]

-- Linear arithmetic
example (a b c : Int) (h1 : a + b = c) (h2 : a = 5) (h3 : b = 3) : c = 8 := by
  loom_smt [h1, h2, h3]

-- Inequality
example (x : Int) (h : x > 0) (h2 : x < 10) : x ≤ 9 := by
  loom_smt [h, h2]

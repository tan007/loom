import Loom.SMT

set_option trace.loom.smt.debug true
set_option trace.loom.smt.result true
set_option loom.solver.smt.timeout 30

-- Division uniqueness: q*d + r = n ∧ 0 ≤ r < d → q = n/d
example (n d q r : Int)
    (hd_pos : d > 0)
    (h_recon : q * d + r = n)
    (h_rem_lo : 0 ≤ r)
    (h_rem_hi : r < d) :
    q = n / d := by
  loom_smt [hd_pos, h_recon, h_rem_lo, h_rem_hi]

-- Simpler: n = q*d + r with remainder bounds
example (n d q r : Int)
    (hd_pos : d > 0)
    (h_recon : q * d + r = n)
    (h_rem_lo : 0 ≤ r)
    (h_rem_hi : r < d)
    (h_q2 : Int)
    (h_r2 : Int)
    (h2_recon : h_q2 * d + h_r2 = n)
    (h2_rem_lo : 0 ≤ h_r2)
    (h2_rem_hi : h_r2 < d) :
    q = h_q2 := by
  loom_smt [hd_pos, h_recon, h_rem_lo, h_rem_hi, h2_recon, h2_rem_lo, h2_rem_hi]



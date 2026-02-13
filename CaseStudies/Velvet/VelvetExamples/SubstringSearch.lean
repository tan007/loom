import Auto
import Lean

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"
set_option loom.solver "grind"
set_option loom.solver.smt.timeout 5

--this will ne our answer type
structure SubstringResult where
  l : Nat
  r : Nat
  flag: Bool
deriving Repr, Inhabited

--predicate for substring all characters of which satisfy the predicate
@[loomAbstractionSimp]
def CorrectSubstring (s : Array Char) (p : Char -> Bool) (l r : Nat) : Prop :=
  l ≤ r ∧ r < s.size ∧
  (∀ i, l ≤ i ∧ i ≤ r → p s[i]!)

--actual method
--  if there are no substrings,
--  flag is false and all characters do not satisfy the predicate
method SubstringSearch (s: Array Char) (p: Char -> Bool) return (res: SubstringResult)
--postconditions, don't need any preconditions.
ensures (res.l ≤ res.r)
ensures 0 < s.size → res.r < s.size
ensures res.flag → CorrectSubstring s p res.l res.r
ensures res.flag →
  (∀ l₁ r₁, CorrectSubstring s p l₁ r₁ →
    r₁ - l₁ + 1 = res.r - res.l + 1 ∧ res.r ≤ r₁ ∨
    r₁ - l₁ + 1 < res.r - res.l + 1)
ensures ¬res.flag → ∀ i < s.size, ¬p s[i]!
do
    if s.size = 0 then
      --basic case with an empty string
      return ⟨0, 0, false⟩
    let mut cnt := 0
    let mut pnt := 0
    let mut ans := 0
    let mut l_ans := 0
    let mut r_ans := 0
    while pnt < s.size
    --loop invariants
    invariant 0 ≤ cnt
    invariant cnt ≤ pnt
    invariant pnt ≤ s.size
    invariant l_ans ≤ r_ans
    invariant r_ans < s.size
    invariant cnt ≤ ans
    invariant r_ans ≤ pnt
    invariant ∀ j, pnt - cnt ≤ j ∧ j < pnt → p s[j]!
    invariant ans > 0 →
        ans = r_ans - l_ans + 1 ∧
        CorrectSubstring s p l_ans r_ans
    invariant ans = 0 → (∀ i, i < pnt → ¬p s[i]!)
    invariant cnt < pnt → ¬p s[pnt - cnt - 1]!
    invariant ∀ l₁ r₁,
        CorrectSubstring s p l₁ r₁ ∧ r₁ < pnt →
        r₁ - l₁ + 1 = ans ∧ r_ans ≤ r₁ ∨ r₁ - l₁ + 1 < ans
    --value decreases by 1 with each iteration,
    --therefore time complexity is O(size s), as other parts
    --take constant time
    decreasing s.size - pnt
    do
      --loop body
      if p s[pnt]! then
        cnt := cnt + 1
        if ans < cnt then
          l_ans := pnt + 1 - cnt
          r_ans := pnt
          ans := cnt
      else
        cnt := 0
      pnt := pnt + 1
    return ⟨l_ans, r_ans, ans > 0⟩

prove_correct SubstringSearch by
  loom_goals_intro
  loom_unfold
  all_goals try loom_solver
  · intro hpos
    refine ⟨?_, ?_⟩
    · omega
    · constructor
      · omega
      · constructor
        · exact if_pos
        · intro i hi
          by_cases hip : i = pnt
          · subst hip
            simpa using if_pos_1
          · have hip_lt : i < pnt := by omega
            exact invariant_8 i (by omega) hip_lt
  · intro l₁ r₁ hcorr hr
    by_cases hrp : r₁ = pnt
    · rw [hrp]
      have hlen_le : r₁ - l₁ + 1 ≤ cnt + 1 := by
        by_cases hcp : cnt < pnt
        · have hlow : pnt - cnt ≤ l₁ := by
            by_contra hlt
            have hle : l₁ ≤ pnt - cnt - 1 := by omega
            have htrue : p s[pnt - cnt - 1]! = true := by
              simpa using (hcorr.2.2 (pnt - cnt - 1) ⟨hle, by omega⟩)
            exact (invariant_11 hcp) htrue
          omega
        · omega
      by_cases hlt : r₁ - l₁ + 1 < cnt + 1
      · exact Or.inr (by simpa [hrp] using hlt)
      · left
        constructor
        · omega
        · omega
    · have hrlt : r₁ < pnt := by omega
      have hold := invariant_12 l₁ r₁ hcorr hrlt
      rcases hold with hEq | hLt
      · right
        omega
      · right
        omega
  · intro l₁ r₁ hcorr hr
    by_cases hrp : r₁ = pnt
    · rw [hrp]
      have hlen_le : r₁ - l₁ + 1 ≤ cnt + 1 := by
        by_cases hcp : cnt < pnt
        · have hlow : pnt - cnt ≤ l₁ := by
            by_contra hlt
            have hle : l₁ ≤ pnt - cnt - 1 := by omega
            have htrue : p s[pnt - cnt - 1]! = true := by
              simpa using (hcorr.2.2 (pnt - cnt - 1) ⟨hle, by omega⟩)
            exact (invariant_11 hcp) htrue
          omega
        · omega
      by_cases hlt : r₁ - l₁ + 1 < ans
      · exact Or.inr (by simpa [hrp] using hlt)
      · left
        constructor
        · omega
        · omega
    · have hrlt : r₁ < pnt := by omega
      exact invariant_12 l₁ r₁ hcorr hrlt
  · intro l₁ r₁ hcorr hr
    have hrlt : r₁ < pnt := by
      have hrle : r₁ ≤ pnt := Nat.le_of_lt_succ hr
      rcases lt_or_eq_of_le hrle with hlt | hEq
      · exact hlt
      · subst hEq
        exfalso
        have hptrue : p s[r₁]! = true := by
          simpa using (hcorr.2.2 r₁ ⟨hcorr.1, le_rfl⟩)
        exact if_neg_1 (by simpa using hptrue)
    exact invariant_12 l₁ r₁ hcorr hrlt
  · intro hflag l₁ r₁ hcorr
    cases i_4
    have hans : ans > 0 := by simpa using hflag
    have hbest : ans = r_ans - l_ans + 1 := (invariant_9 hans).1
    have hrlt : r₁ < pnt := by
      have hrs : r₁ < s.size := hcorr.2.1
      omega
    simpa [hbest] using (invariant_12 l₁ r₁ hcorr hrlt)

--prove theorem not about the monadic computation but the actual
--extract result
theorem finalCorrectnessTheorem (s : Array Char) (p : Char → Bool) :
  let res := SubstringSearch s p |>.extract
  (res.flag = false → ∀ i < s.size, p s[i]! = false) ∧
  (res.flag = true →
    (∀ l₁ r₁, CorrectSubstring s p l₁ r₁ →
  r₁ - l₁ + 1 = res.r - res.l + 1 ∧ res.r ≤ r₁ ∨
  r₁ - l₁ + 1 < res.r - res.l + 1)) ∧
  (res.flag = true → CorrectSubstring s p res.l res.r) ∧
  (0 < s.size → res.r < s.size) ∧
  (res.l ≤ res.r) := by
    grind [VelvetM.extract_spec, SubstringSearch_correct]

import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

section insertionSort

/-

Dafny code below for reference

method insertionSort(arr: array<int>)
  modifies arr
  ensures forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures multiset(arr[..]) == old(multiset(arr[..]))
{
  if arr.Length <= 1 {
    return;
  }
  var n := 1;
  while n != arr.Length
  invariant 0 <= n <= arr.Length
  invariant forall i, j :: 0 <= i < j <= n - 1 ==> arr[i] <= arr[j]
  invariant multiset(arr[..]) == old(multiset(arr[..]))
  {
    var mind := n;
    while mind != 0
    invariant 0 <= mind <= n
    invariant multiset(arr[..]) == old(multiset(arr[..]))
    invariant forall i, j :: 0 <= i < j <= n && (j != mind)==> arr[i] <= arr[j]
    {
      if arr[mind] <= arr[mind - 1] {
        arr[mind], arr[mind - 1] := arr[mind - 1], arr[mind];
      }
      mind := mind - 1;
    }
    n := n + 1;
  }
}
-/

-- set_option trace.profiler true
attribute [grind] Array.multiset_swap

--partial correctness version of insertionSort
method insertionSort
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  do
    let mut n := 1
    while n ≠ arr.size
    invariant arr.size = arrOld.size
    invariant 1 ≤ n ∧ n ≤ arr.size
    invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
    invariant arr.toMultiset = arrOld.toMultiset
    done_with n = arr.size
    do
      let mut mind := n
      while mind ≠ 0
      invariant arr.size = arrOld.size
      invariant mind ≤ n
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
      invariant forall i, 0 ≤ i ∧ i < mind - 1 → arr[i]! ≤ arr[mind - 1]!
      invariant arr.toMultiset = arrOld.toMultiset
      done_with mind = 0
      do
        if arr[mind]! < arr[mind - 1]! then
          swap! arr[mind - 1]! arr[mind]!
        mind := mind - 1
      n := n + 1
    return

extract_program_for insertionSort
prove_precondition_decidable_for insertionSort
prove_postcondition_decidable_for insertionSort by
  (exact (decidable_by_nat_upperbound [(arr.size), (arr.size)]))
derive_tester_for insertionSort

-- doing simple testing
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arr ← Plausible.SampleableExt.interpSample (Array Int)
    let res := insertionSortTester arr
    pure (arr, res)
  for _ in [1: 500] do
    let res ← Plausible.Gen.run g 10
    unless res.2 do
      IO.println s!"postcondition violated for input {res.1}"
      break

set_option maxHeartbeats 1000000

prove_correct insertionSort by
  loom_solve
  · intro i j hi hij hjn hjm1
    by_cases hj : j = mind
    · subst j
      by_cases him1 : i = mind - 1
      · subst i
        have hlt : arr_1[mind]! ≤ arr_1[mind - 1]! := by omega
        grind
      · have hi_lt : i < mind - 1 := by omega
        have hleft : arr_1[i]! ≤ arr_1[mind - 1]! := invariant_8 i hi hi_lt
        grind
    · by_cases him1 : i = mind - 1
      · subst i
        have hmj : mind < j := by omega
        have hbase : arr_1[mind]! ≤ arr_1[j]! := invariant_7 mind j (by omega) hmj hjn hj
        grind
      · by_cases him : i = mind
        · subst i
          have hm1j : mind - 1 < j := by omega
          have hbase : arr_1[mind - 1]! ≤ arr_1[j]! :=
            invariant_7 (mind - 1) j (by omega) hm1j hjn (by omega)
          grind
        · have hbase : arr_1[i]! ≤ arr_1[j]! := invariant_7 i j hi hij hjn hj
          grind
  · intro i j hi hij hjs
    cases i_1
    by_cases hEq : i = j
    · subst hEq
      omega
    · exact invariant_3 i j hi (Nat.lt_of_le_of_ne hij hEq) (by omega)

end insertionSort

section squareRoot

--partial correctness version of square root
method sqrt (x: ℕ) return (res: ℕ)
  require x > 8
  ensures res * res ≤ x
  ensures ∀ i, i ≤ res → i * i ≤ x
  ensures ∀ i, i * i ≤ x → i ≤ res
  do
    if x = 0 then
      return 0
    let mut i := 0
    while i * i ≤ x
    invariant ∀ j, j < i → j * j ≤ x
    done_with x < i * i
    do
      i := i + 1
    return i - 1

prove_correct sqrt by
  loom_solve
  · intro j hj
    by_cases hEq : j = i
    · subst j
      exact if_pos
    · exact invariant_1 j (by omega)
  · intro i_1 hi_sq
    have hi_lt : i_1 < i := by
      by_contra hnot
      have hi_le : i ≤ i_1 := Nat.not_lt.mp hnot
      have hsq_le : i * i ≤ i_1 * i_1 := Nat.mul_le_mul hi_le hi_le
      omega
    exact Nat.le_pred_of_lt hi_lt
  · intro i_1 hi_le
    have hi_pos : 0 < i := by
      by_cases hi0 : i = 0
      · subst i
        omega
      · exact Nat.pos_of_ne_zero hi0
    have hi_lt : i_1 < i := by
      have hsucc : i_1 + 1 ≤ i := by omega
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i_1) hsucc
    exact invariant_1 i_1 hi_lt
  · have hi_pos : 0 < i := by
      by_cases hi0 : i = 0
      · subst i
        omega
      · exact Nat.pos_of_ne_zero hi0
    exact invariant_1 (i - 1) (Nat.sub_lt hi_pos (by decide))

end squareRoot

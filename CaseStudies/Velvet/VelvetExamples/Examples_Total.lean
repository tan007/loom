import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

attribute [grind] Array.multiset_swap

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

--insertion sort implemented in Velvet
method insertionSort_total
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arrOld.toMultiset = arr.toMultiset
  do
    let arr₀ := arr
    let arr_size := arr.size
    let mut n := 1
    while n ≠ arr.size
    invariant arr.size = arr_size
    invariant 1 ≤ n ∧ n ≤ arr.size
    invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
    invariant arr.toMultiset = arr₀.toMultiset
    --explicit decreasing measure for loop termination is required in TotalCorrectness
    decreasing arr.size - n
    do
      let mut mind := n
      while mind ≠ 0
      invariant arr.size = arr_size
      invariant mind ≤ n
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
      invariant forall i, 0 ≤ i ∧ i < mind - 1 → arr[i]! ≤ arr[mind - 1]!
      invariant arr.toMultiset = arr₀.toMultiset
      decreasing mind
      do
        if arr[mind]! < arr[mind - 1]! then
          swap! arr[mind - 1]! arr[mind]!
        mind := mind - 1
      -- comment out line below to check produced goals
      n := n + 1
    return
set_option maxHeartbeats 1000000 in
prove_correct insertionSort_total by
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

set_option loom.solver.smt.timeout 4

--square root of a non-negative integer implemented in Velvet
method sqrt_total (x: ℕ) return (res: ℕ)
  ensures res * res ≤ x
  ensures ∀ i, i ≤ res → i * i ≤ x
  ensures ∀ i, i * i ≤ x → i ≤ res
  do
    if x = 0 then
      return 0
    else
      let mut i := 0
      while i * i ≤ x
      invariant ∀ j, j < i → j * j ≤ x
      decreasing x + 8 - i
      do
        i := i + 1
      return i - 1
prove_correct sqrt_total by
  loom_solve
  · intro i hi_sq
    have hsq0 : i * i = 0 := le_antisymm (by simpa [if_pos] using hi_sq) (Nat.zero_le _)
    have hi0 : i = 0 := by
      rcases (Nat.mul_eq_zero.mp hsq0) with h | h <;> assumption
    simpa [hi0]
  · intro j hj
    by_cases hEq : j = i
    · subst j
      exact if_pos
    · exact invariant_1 j (by omega)
  · have hix : i ≤ x := le_trans (Nat.le_mul_self i) if_pos
    have hi_lt : i < x + 8 := by omega
    omega
  · intro i_1 hi_sq
    have hi_lt : i_1 < i := by
      by_contra hnot
      have hi_le : i ≤ i_1 := Nat.not_lt.mp hnot
      have hsq_le : i * i ≤ i_1 * i_1 := Nat.mul_le_mul hi_le hi_le
      exact done_1 (le_trans hsq_le hi_sq)
    exact Nat.le_pred_of_lt hi_lt
  · intro i_1 hi_le
    have hi_pos : 0 < i := by
      by_cases hi0 : i = 0
      · subst i
        exact False.elim (done_1 (by omega))
      · exact Nat.pos_of_ne_zero hi0
    have hi_lt : i_1 < i := by
      have hsucc : i_1 + 1 ≤ i := by omega
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i_1) hsucc
    exact invariant_1 i_1 hi_lt
  · have hi_pos : 0 < i := by
      by_cases hi0 : i = 0
      · subst i
        exact False.elim (done_1 (by omega))
      · exact Nat.pos_of_ne_zero hi0
    exact invariant_1 (i - 1) (Nat.sub_lt hi_pos (by decide))

--root of power 3 for a non-negative integer implemented in Velvet
method cbrt (x: ℕ) return (res: ℕ)
  ensures res * res * res ≤ x
  ensures ∀ i, i ≤ res → i * i * i ≤ x
  ensures ∀ i, i * i * i ≤ x → i ≤ res
  do
    if x = 0 then
      return 0
    else
      let mut i := 0
      while i * i * i ≤ x
      invariant ∀ j, j < i → j * j * j ≤ x
      decreasing x + 8 - i
      do
        i := i + 1
      return i - 1
prove_correct cbrt by
  loom_solve
  · intro i hi_cube
    have hcube0 : i * i * i = 0 := le_antisymm (by simpa [if_pos] using hi_cube) (Nat.zero_le _)
    have hi0 : i = 0 := by
      rcases (Nat.mul_eq_zero.mp hcube0) with h | h
      · rcases (Nat.mul_eq_zero.mp h) with h' | h' <;> exact h'
      · exact h
    simpa [hi0]
  · intro j hj
    by_cases hEq : j = i
    · subst j
      exact if_pos
    · exact invariant_1 j (by omega)
  · have h1 : i ≤ i * i := Nat.le_mul_self i
    have h2 : i * i ≤ i * i * i := by
      by_cases hi0 : i = 0
      · subst i
        simp
      · have hi1 : 1 ≤ i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0)
        simpa [Nat.mul_assoc] using (Nat.mul_le_mul_left (i * i) hi1)
    have hix : i ≤ x := le_trans h1 (le_trans h2 if_pos)
    have hi_lt : i < x + 8 := by omega
    omega
  · intro i_1 hi_cube
    have hi_lt : i_1 < i := by
      by_contra hnot
      have hi_le : i ≤ i_1 := Nat.not_lt.mp hnot
      have hcube_le : i * i * i ≤ i_1 * i_1 * i_1 :=
        Nat.mul_le_mul (Nat.mul_le_mul hi_le hi_le) hi_le
      exact done_1 (le_trans hcube_le hi_cube)
    exact Nat.le_pred_of_lt hi_lt
  · intro i_1 hi_le
    have hi_pos : 0 < i := by
      by_cases hi0 : i = 0
      · subst i
        exact False.elim (done_1 (by omega))
      · exact Nat.pos_of_ne_zero hi0
    have hi_lt : i_1 < i := by
      have hsucc : i_1 + 1 ≤ i := by omega
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i_1) hsucc
    exact invariant_1 i_1 hi_lt
  · have hi_pos : 0 < i := by
      by_cases hi0 : i = 0
      · subst i
        exact False.elim (done_1 (by omega))
      · exact Nat.pos_of_ne_zero hi0
    exact invariant_1 (i - 1) (Nat.sub_lt hi_pos (by decide))


/-
Dafny code for reference below

method sqrt_bn (x: nat, bnd: nat) returns (res: nat)
  requires x < bnd * bnd
  ensures res * res <= x
  ensures forall i: nat :: i <= res ==> i * i <= x
  ensures forall i: nat :: i * i <= x ==> i <= res
{
  var l: nat := 0;
  var r: nat := bnd;
  assert forall i: nat :: i * i <= x ==> i * i < r * r;
  assert forall i: nat :: i * i < r * r ==> 0 < (r - i) * (r + i);
  while 1 < r - l
  invariant l * l <= x
  invariant x < r * r
  invariant forall i: nat :: i <= l ==> i * i <= x
  invariant forall i: nat :: i * i <= x ==> i < r
  {
    var m: nat := (r + l) / 2;
    if m * m <= x {
      l := m;
      assert l <= m < r;
    } else {
      r := m;
      assert l < m <= r;
    }
  }
  return l;
}
-/

--binary search for square root of a non-negative integer implemented in Velvet
method sqrt_bn (x: ℕ) (bnd: ℕ) return (res: ℕ)
  require x < bnd * bnd
  ensures res * res ≤ x
  ensures ∀ i, i ≤ res → i * i ≤ x
  ensures ∀ i, i * i ≤ x → i ≤ res
  do
    let mut l := 0
    let mut r := bnd
    while 1 < r - l
    invariant l * l ≤ x
    invariant x < r * r
    invariant ∀ i, i ≤ l → i * i ≤ x
    decreasing r - l
    do
      let m := (r + l) / 2
      if m * m ≤ x then
        l := m
      else
        r := m
    return l
prove_correct sqrt_bn by
  loom_solve
  · intro i hi
    exact le_trans (Nat.mul_le_mul hi hi) if_pos_1
  · intro i_2 hi_sq
    have hi' : l = i := by simpa using congrArg (fun p => p.fst) i_1
    have hr' : r = r_1 := by simpa using congrArg (fun p => p.snd) i_1
    have hi : i = l := hi'.symm
    have hr : r_1 = r := hr'.symm
    subst i r_1
    have hi_r : i_2 < r := by
      by_contra hnot
      have hr_le : r ≤ i_2 := Nat.not_lt.mp hnot
      have hr_sq_le : r * r ≤ i_2 * i_2 := Nat.mul_le_mul hr_le hr_le
      exact (not_lt_of_ge hi_sq) (lt_of_lt_of_le invariant_2 hr_sq_le)
    by_contra hle
    have hl_lt : l < i_2 := Nat.lt_of_not_ge hle
    omega

end squareRoot

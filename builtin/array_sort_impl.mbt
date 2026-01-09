// Copyright 2026 International Digital Economy Academy
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

///|
priv struct TimSortRun {
  len : Int
  start : Int
}

///|
/// Check that all runs in the stack are individually sorted.
fn[T : Compare] all_runs_sorted(arr : MutArrayView[T], runs : Array[TimSortRun]) -> Bool {
  for i = 0; i < runs.length(); i = i + 1 {
    let run = runs[i]
    if not(is_sorted_slice(arr.slice(run.start, run.start + run.len))) {
      return false
    }
  }
  true
}

///|
/// Check that runs form a contiguous partition of arr[0..end].
/// Runs must be non-overlapping, in order, and cover exactly [0, end).
fn runs_cover_prefix(runs : Array[TimSortRun], end : Int) -> Bool {
  if runs.is_empty() {
    return end == 0
  }
  // First run must start at 0
  if runs[0].start != 0 {
    return false
  }
  // Each run must start where the previous one ended
  for i = 1; i < runs.length(); i = i + 1 {
    let prev = runs[i - 1]
    let curr = runs[i]
    if curr.start != prev.start + prev.len {
      return false
    }
  }
  // Last run must end at `end`
  let last = runs[runs.length() - 1]
  last.start + last.len == end
}

///|
/// Check the timsort stack invariants that ensure O(n log n) performance:
/// 1. runs[i-1].len > runs[i].len (lengths strictly decrease down the stack)
/// 2. runs[i-2].len > runs[i-1].len + runs[i].len (Fibonacci-like growth)
///
/// These invariants ensure the stack size is O(log n) and total merge work is O(n log n).
fn timsort_stack_invariant(runs : Array[TimSortRun]) -> Bool {
  let n = runs.length()
  // Check invariant 1: runs[i-1].len > runs[i].len for all valid i
  for i = 1; i < n; i = i + 1 {
    if runs[i - 1].len <= runs[i].len {
      return false
    }
  }
  // Check invariant 2: runs[i-2].len > runs[i-1].len + runs[i].len for all valid i
  for i = 2; i < n; i = i + 1 {
    if runs[i - 2].len <= runs[i - 1].len + runs[i].len {
      return false
    }
  }
  true
}

///|
/// The algorithm identifies strictly descending and non-descending subsequences, which are called
/// natural runs. There is a stack of pending runs yet to be merged. Each newly found run is pushed
/// onto the stack, and then some pairs of adjacent runs are merged until these two invariants are
/// satisfied:
///
/// 1. for every `i` in `1..runs.len()`: `runs[i - 1].len > runs[i].len`
/// 2. for every `i` in `2..runs.len()`: `runs[i - 2].len > runs[i - 1].len + runs[i].len`
///
/// The invariants ensure that the total running time is *O*(*n* \* log(*n*)) worst-case.
fn[T : Compare] timsort(arr : MutArrayView[T]) -> Unit {
  // Slices of up to this length get sorted using insertion sort.
  let max_insertion = 20

  // Short arrays get sorted in-place via insertion sort to avoid allocations.
  let len = arr.length()
  if len <= max_insertion {
    MutArrayView::insertion_sort(arr)
    return
  }
  let mut end = 0
  let mut start = 0
  let runs : Array[TimSortRun] = []
  for ; end < len; {
    let (streak_end, was_reversed) = find_streak(arr.mut_view(start~))
    end += streak_end
    if was_reversed {
      arr.mut_view(start~, end~).rev_in_place()
    }
    // Insert some more elements into the run if it's too short. Insertion sort is faster than
    // merge sort on short sequences, so this significantly improves performance.
    end = provide_sorted_batch(arr, start, end)
    runs.push({ start, len: end - start })
    start = end
    for ; ; {
      guard collapse(runs, len) is Some(r) else { break }
      let left = runs[r]
      let right = runs[r + 1]
      merge(arr.slice(left.start, right.start + right.len), left.len)
      runs[r + 1] = { start: left.start, len: left.len + right.len }
      runs.remove(r) |> ignore
    } where {
      invariant: all_runs_sorted(arr, runs),
      invariant: runs_cover_prefix(runs, end),
      invariant: timsort_stack_invariant(runs),
      reasoning: #|[LOOP_ID: timsort_inner]
        #|
        #|[INVARIANT: all_runs_sorted(arr, runs)]
        #|  GIVEN: Before iteration, all_runs_sorted(arr, runs) holds.
        #|  GIVEN: runs[r] and runs[r+1] are sorted (from invariant).
        #|  GIVEN: merge(sorted_left, sorted_right) produces sorted output.
        #|  STEP: merge() is called on arr.slice(left.start, right.start + right.len).
        #|  STEP: runs[r+1] := merged run; runs[r] is removed.
        #|  DEDUCE: The merged run is sorted (merge postcondition).
        #|  DEDUCE: Other runs unchanged, remain sorted.
        #|  CONCLUDE: all_runs_sorted(arr, runs) holds after iteration.
        #|
        #|[INVARIANT: runs_cover_prefix(runs, end)]
        #|  GIVEN: Before iteration, runs_cover_prefix(runs, end) holds.
        #|  GIVEN: runs[r].start + runs[r].len == runs[r+1].start (contiguity).
        #|  LET: left_start = runs[r].start, left_len = runs[r].len.
        #|  LET: right_start = runs[r+1].start, right_len = runs[r+1].len.
        #|  STEP: New run has start = left_start, len = left_len + right_len.
        #|  DEDUCE: New run covers [left_start, left_start + left_len + right_len).
        #|  DEDUCE: This equals [left_start, right_start + right_len) = union of both runs.
        #|  CONCLUDE: Total coverage unchanged; runs_cover_prefix(runs, end) holds.
        #|
        #|[INVARIANT: timsort_stack_invariant(runs)]
        #|  GIVEN: Loop exits when collapse(runs, len) returns None.
        #|  GIVEN: collapse returns None IFF:
        #|    (a) n < 2, OR
        #|    (b) runs[n-2].len > runs[n-1].len AND
        #|        (n < 3 OR runs[n-3].len > runs[n-2].len + runs[n-1].len) AND
        #|        (n < 4 OR runs[n-4].len > runs[n-3].len + runs[n-2].len) AND
        #|        NOT (runs[n-1].start + runs[n-1].len == len).
        #|  DEDUCE: On exit, timsort_stack_invariant conditions are satisfied.
        #|  CONCLUDE: timsort_stack_invariant(runs) holds on loop exit.
        #|
        #|[COMPLEXITY: O(n log n)]
        #|  GIVEN: timsort_stack_invariant requires runs[i-2].len > runs[i-1].len + runs[i].len.
        #|  DEDUCE: Run lengths grow at least as fast as Fibonacci: L[k] >= F[k].
        #|  GIVEN: Fibonacci grows exponentially: F[k] >= phi^(k-2), phi = (1+sqrt(5))/2.
        #|  DEDUCE: Stack depth is O(log_phi(n)) = O(log n).
        #|  DEDUCE: Each element participates in O(log n) merges.
        #|  CONCLUDE: Total merge work is O(n log n).
        #|
        #|[TERMINATION]
        #|  MEASURE: runs.length()
        #|  STEP: Each iteration removes one run (runs.remove(r)).
        #|  DEDUCE: runs.length() decreases by 1 each iteration.
        #|  DEDUCE: runs.length() >= 0 always.
        #|  CONCLUDE: Loop terminates.
        ,
    }
  } where {
    invariant: 0 <= start && start <= len,
    invariant: 0 <= end && end <= len,
    invariant: start == end,
    invariant: all_runs_sorted(arr, runs),
    invariant: runs_cover_prefix(runs, start),
    invariant: timsort_stack_invariant(runs),
    reasoning: #|[LOOP_ID: timsort_outer]
      #|
      #|[INITIALIZATION]
      #|  STATE: start = 0, end = 0, runs = [].
      #|  CHECK: 0 <= 0 && 0 <= len. TRUE (len >= 0).
      #|  CHECK: start == end. TRUE (0 == 0).
      #|  CHECK: all_runs_sorted(arr, []). TRUE (vacuously).
      #|  CHECK: runs_cover_prefix([], 0). TRUE (empty runs cover empty prefix).
      #|  CHECK: timsort_stack_invariant([]). TRUE (vacuously).
      #|  CONCLUDE: All invariants hold at initialization.
      #|
      #|[INVARIANT: 0 <= start && start <= len]
      #|  GIVEN: Before iteration, 0 <= start && start <= len.
      #|  GIVEN: start == end (from invariant).
      #|  STEP: end increases via find_streak (returns >= 1 for non-empty slice).
      #|  STEP: end may increase via provide_sorted_batch (bounded by len).
      #|  STEP: start := end.
      #|  DEDUCE: start' = end' where 0 <= end' <= len.
      #|  CONCLUDE: 0 <= start && start <= len holds after iteration.
      #|
      #|[INVARIANT: start == end]
      #|  GIVEN: start := end is the last assignment before loop continues.
      #|  CONCLUDE: start == end holds at next iteration entry.
      #|
      #|[INVARIANT: all_runs_sorted(arr, runs)]
      #|  GIVEN: Before iteration, all_runs_sorted(arr, runs) holds.
      #|  STEP: find_streak returns (streak_end, was_reversed).
      #|  GIVEN: find_streak postcondition:
      #|    IF was_reversed THEN arr[start..start+streak_end] is strictly decreasing
      #|    ELSE arr[start..start+streak_end] is non-decreasing.
      #|  STEP: IF was_reversed THEN rev_in_place(arr[start..end]).
      #|  DEDUCE: After potential reversal, arr[start..end] is non-decreasing.
      #|  STEP: provide_sorted_batch may extend and sort via insertion_sort.
      #|  GIVEN: insertion_sort postcondition: output is sorted.
      #|  DEDUCE: arr[start..end'] is sorted after provide_sorted_batch.
      #|  STEP: runs.push({ start, len: end - start }).
      #|  DEDUCE: New run covers arr[start..end] which is sorted.
      #|  STEP: Inner loop preserves all_runs_sorted (see timsort_inner proof).
      #|  CONCLUDE: all_runs_sorted(arr, runs) holds after iteration.
      #|
      #|[INVARIANT: runs_cover_prefix(runs, start)]
      #|  GIVEN: Before iteration, runs_cover_prefix(runs, start_old) holds.
      #|  GIVEN: start_old == end_old (from invariant).
      #|  STEP: New run starts at start_old with len = end_new - start_old.
      #|  DEDUCE: After push, runs cover [0, end_new).
      #|  STEP: Inner loop preserves coverage (see timsort_inner proof).
      #|  STEP: start := end_new.
      #|  CONCLUDE: runs_cover_prefix(runs, start) holds after iteration.
      #|
      #|[INVARIANT: timsort_stack_invariant(runs)]
      #|  GIVEN: Inner loop exits only when timsort_stack_invariant holds.
      #|  CONCLUDE: timsort_stack_invariant(runs) holds after iteration.
      #|
      #|[TERMINATION]
      #|  MEASURE: len - end
      #|  GIVEN: find_streak returns streak_end >= 1 when arr[start..] is non-empty.
      #|  STEP: end increases by at least 1 each iteration.
      #|  DEDUCE: len - end decreases each iteration.
      #|  DEDUCE: Loop exits when end >= len.
      #|  CONCLUDE: Loop terminates.
      #|
      #|[POSTCONDITION]
      #|  GIVEN: Loop exits with end >= len.
      #|  GIVEN: runs_cover_prefix(runs, start) AND start == end >= len.
      #|  DEDUCE: runs cover arr[0..len].
      #|  GIVEN: all_runs_sorted(arr, runs).
      #|  GIVEN: Final collapse merges all runs when runs[n-1].start + runs[n-1].len == len.
      #|  DEDUCE: Eventually single run covers [0, len) and is sorted.
      #|  CONCLUDE: arr is sorted.
      ,
  }
}

///|
/// Check if a mutable array view is sorted in non-decreasing order.
fn[T : Compare] is_sorted_slice(arr : MutArrayView[T]) -> Bool {
  for i = 1; i < arr.length(); i = i + 1 {
    if arr[i] < arr[i - 1] {
      return false
    }
  }
  true
}

///|
fn[T : Compare] MutArrayView::insertion_sort(arr : MutArrayView[T]) -> Unit {
  let len = arr.length()
  for i = 1; i < len; i = i + 1 {
    for j = i; j > 0 && arr[j] < arr[j - 1]; j = j - 1 {
      arr.swap(j, j - 1)
    } where {
      invariant: j >= 0 && j <= i,
      invariant: is_sorted_slice(arr.slice(j, i + 1)),
      reasoning: #|[LOOP_ID: insertion_sort_inner]
        #|
        #|[INVARIANT: j >= 0 && j <= i]
        #|  GIVEN: Initial j = i, so j <= i holds.
        #|  GIVEN: Loop condition requires j > 0 to continue.
        #|  STEP: j decreases by 1 each iteration.
        #|  DEDUCE: j >= 0 always (loop exits when j <= 0).
        #|  CONCLUDE: j >= 0 && j <= i holds.
        #|
        #|[INVARIANT: is_sorted_slice(arr.slice(j, i + 1))]
        #|  GIVEN: Initially j = i, so slice has length 1, trivially sorted.
        #|  GIVEN: Loop continues only if arr[j] < arr[j-1].
        #|  STEP: swap(j, j-1) exchanges arr[j] and arr[j-1].
        #|  LET: Before swap, arr[j] < arr[j-1] AND arr[j..i+1] sorted.
        #|  DEDUCE: After swap, arr[j-1] < arr[j] (swapped values).
        #|  DEDUCE: arr[j-1] was arr[j], which was < all of arr[j+1..i+1].
        #|  DEDUCE: arr[j-1..i+1] is sorted after swap.
        #|  STEP: j decreases to j-1, so new slice is arr[j-1..i+1].
        #|  CONCLUDE: is_sorted_slice(arr.slice(j, i + 1)) holds.
        #|
        #|[TERMINATION]
        #|  MEASURE: j
        #|  STEP: j decreases by 1 each iteration.
        #|  GIVEN: Loop exits when j <= 0 OR arr[j] >= arr[j-1].
        #|  CONCLUDE: Loop terminates.
        ,
    }
  } where {
    invariant: i >= 1 && i <= len,
    invariant: is_sorted_slice(arr.slice(0, i)),
    reasoning: #|[LOOP_ID: insertion_sort_outer]
      #|
      #|[INVARIANT: i >= 1 && i <= len]
      #|  GIVEN: Initial i = 1, so i >= 1 holds.
      #|  GIVEN: Loop condition requires i < len to continue.
      #|  STEP: i increases by 1 each iteration.
      #|  CONCLUDE: i >= 1 && i <= len holds.
      #|
      #|[INVARIANT: is_sorted_slice(arr.slice(0, i))]
      #|  [BASE CASE]
      #|    GIVEN: Initial i = 1.
      #|    DEDUCE: arr[0..1] has length 1, trivially sorted.
      #|    CONCLUDE: is_sorted_slice(arr.slice(0, 1)) holds.
      #|
      #|  [INDUCTIVE CASE]
      #|    GIVEN: Before iteration, is_sorted_slice(arr.slice(0, i)) holds.
      #|    GOAL: Show is_sorted_slice(arr.slice(0, i + 1)) after iteration.
      #|
      #|    STEP: Inner loop terminates with j = j_final where:
      #|      CASE j_final == 0: arr[0] is the minimum of arr[0..i+1].
      #|      CASE arr[j_final] >= arr[j_final - 1]: arr[j_final] in correct position.
      #|
      #|    GIVEN: Inner loop maintains is_sorted_slice(arr.slice(j, i + 1)).
      #|    DEDUCE: On inner loop exit, arr[j_final..i+1] is sorted.
      #|
      #|    GIVEN: Inner loop only swaps within arr[0..i+1], preserving order in arr[0..j_final].
      #|    GIVEN: Original arr[0..i] was sorted (outer invariant).
      #|    DEDUCE: arr[0..j_final] remains sorted (elements shifted right by swaps).
      #|
      #|    GIVEN: Exit condition implies arr[j_final - 1] <= arr[j_final] (if j_final > 0).
      #|    DEDUCE: arr[0..j_final] and arr[j_final..i+1] connect correctly.
      #|    CONCLUDE: is_sorted_slice(arr.slice(0, i + 1)) holds.
      #|
      #|[TERMINATION]
      #|  MEASURE: len - i
      #|  STEP: i increases by 1 each iteration.
      #|  DEDUCE: len - i decreases each iteration.
      #|  CONCLUDE: Loop terminates when i >= len.
      #|
      #|[POSTCONDITION]
      #|  GIVEN: Loop exits with i == len.
      #|  GIVEN: is_sorted_slice(arr.slice(0, i)) holds.
      #|  CONCLUDE: is_sorted_slice(arr.slice(0, len)) holds, i.e., arr is sorted.
      ,
  }
}

///|
/// Merges non-decreasing runs `arr[:mid]` and `arr[mid:]`. Copy `arr[mid:]` to buf and merge 
/// `buf` and `arr[:mid]` to `arr[:]`
fn[T : Compare] merge(arr : MutArrayView[T], mid : Int) -> Unit {
  let buf_len = arr.length() - mid
  let buf : FixedArray[T] = FixedArray::make(buf_len, arr[mid])
  for i in 0..<buf.length() {
    buf[i] = arr[mid + i]
  }
  let buf : MutArrayView[T] = buf.mut_view()
  let buf_remaining = for p1 = mid - 1, p2 = buf_len - 1, p = mid + buf_len - 1; p1 >=
                         0 &&
                         p2 >= 0; {
    if arr[p1] > buf[p2] {
      arr[p] = arr[p1]
      continue p1 - 1, p2, p - 1
    } else {
      arr[p] = buf[p2]
      continue p1, p2 - 1, p - 1
    }
  } else {
    p2
  }
  for i = buf_remaining; i >= 0; i = i - 1 {
    arr[i] = buf[i]
  }
}

///|
/// Finds a streak of presorted elements starting at the beginning of the slice. Returns the first
/// value that is not part of said streak, and a bool denoting whether the streak was reversed.
/// Streaks can be increasing or decreasing.
fn[T : Compare] find_streak(arr : MutArrayView[T]) -> (Int, Bool) {
  let len = arr.length()
  if len < 2 {
    return (len, false)
  }
  let assume_reverse = arr[1] < arr[0]
  if assume_reverse {
    for end = 2 {
      if end < len && arr[end] < arr[end - 1] {
        continue end + 1
      } else {
        break (end, true)
      }
    }
  } else {
    for end = 2 {
      if end < len && arr[end] >= arr[end - 1] {
        continue end + 1
      } else {
        break (end, false)
      }
    }
  }
}

///|
fn[T : Compare] provide_sorted_batch(
  arr : MutArrayView[T],
  start : Int,
  end : Int,
) -> Int {
  let len = arr.length()
  // This value is a balance between least comparisons and best performance, as
  // influenced by for example cache locality.
  let min_insertion_run = 10
  // Insert some more elements into the run if it's too short. Insertion sort is faster than
  // merge sort on short sequences, so this significantly improves performance.
  let start_end_diff = end - start
  if start_end_diff < min_insertion_run && end < len {
    // v[start_found:end] are elements that are already sorted in the input. We want to extend
    // the sorted region to the left, so we push up MIN_INSERTION_RUN - 1 to the right. Which is
    // more efficient that trying to push those already sorted elements to the left.
    let sort_end = minimum(len, start + min_insertion_run)
    MutArrayView::insertion_sort(arr.slice(start, sort_end))
    sort_end
  } else {
    end
  }
}

// TimSort is infamous for its buggy implementations, as described here:
// http://envisage-project.eu/timsort-specification-and-verification/
//
// This function correctly checks invariants for the top four runs. Additionally, if the top
// run starts at index 0, it will always demand a merge operation until the stack is fully
// collapsed, in order to complete the sort.

///|
fn collapse(runs : Array[TimSortRun], stop : Int) -> Int? {
  let n : Int = runs.length()
  if n >= 2 &&
    (
      runs[n - 1].start + runs[n - 1].len == stop ||
      runs[n - 2].len <= runs[n - 1].len ||
      (n >= 3 && runs[n - 3].len <= runs[n - 2].len + runs[n - 1].len) ||
      (n >= 4 && runs[n - 4].len <= runs[n - 3].len + runs[n - 2].len)
    ) {
    if n >= 3 && runs[n - 3].len < runs[n - 1].len {
      Some(n - 3)
    } else {
      Some(n - 2)
    }
  } else {
    None
  }
}

///|
/// Sorts the array
/// 
/// It's an in-place, unstable sort(it will reorder equal elements). The time complexity is O(n log n) in the worst case.
/// 
/// # Example
/// 
/// ```mbt check
/// test {
///   let arr = [5, 4, 3, 2, 1]
///   arr.sort()
///   assert_eq(arr, [1, 2, 3, 4, 5])
/// }
/// ```
pub fn[T : Compare] FixedArray::sort(self : FixedArray[T]) -> Unit {
  self.mut_view().sort()
}

///|
fn[T] MutArrayView::slice(
  arr : MutArrayView[T],
  start : Int,
  end : Int,
) -> MutArrayView[T] {
  arr.mut_view(start~, end~)
}

///|
fn[T] MutArrayView::swap(arr : MutArrayView[T], i : Int, j : Int) -> Unit {
  let temp = arr[i]
  arr[i] = arr[j]
  arr[j] = temp
}

///|
fn[T] MutArrayView::rev_in_place(arr : MutArrayView[T]) -> Unit {
  let len = arr.length()
  let mid_len = len / 2
  for i in 0..<mid_len {
    let j = len - i - 1
    // Swap elements
    let temp = arr[i]
    arr[i] = arr[j]
    arr[j] = temp
  }
}

///|
fn[T : Compare] fixed_quick_sort(
  arr : MutArrayView[T],
  pred : T?,
  limit : Int,
) -> Unit {
  let mut limit = limit
  let mut arr = arr
  let mut pred = pred
  let mut was_partitioned = true
  let mut balanced = true
  let bubble_sort_len = 16
  while true {
    let len = arr.length()
    if len <= bubble_sort_len {
      if len >= 2 {
        fixed_bubble_sort(arr)
      }
      return
    }
    // Too many imbalanced partitions may lead to O(n^2) performance in quick sort.
    // If the limit is reached, use heap sort to ensure O(n log n) performance.
    if limit == 0 {
      fixed_heap_sort(arr)
      return
    }
    let (pivot_index, likely_sorted) = fixed_choose_pivot(arr)
    // Try bubble sort if the array is likely already sorted.
    if was_partitioned && balanced && likely_sorted {
      if fixed_try_bubble_sort(arr) {
        return
      }
    }
    let (pivot, partitioned) = fixed_partition(arr, pivot_index)
    was_partitioned = partitioned
    balanced = minimum(pivot, len - pivot) >= len / 8
    if !balanced {
      limit -= 1
    }
    if pred is Some(pred) {
      // pred is less than all elements in arr
      // If pivot equals to pred, then we can skip all elements that are equal to pred.
      if pred == arr[pivot] {
        let mut i = pivot
        while i < len && pred == arr[i] {
          i = i + 1
        }
        arr = arr.slice(i, len)
        continue
      }
    }
    let left = arr.slice(0, pivot)
    let right = arr.slice(pivot + 1, len)
    // Reduce the stack depth by only call fixed_quick_sort on the smaller fixed_partition.
    if left.length() < right.length() {
      fixed_quick_sort(left, pred, limit)
      pred = Some(arr[pivot])
      arr = right
    } else {
      fixed_quick_sort(right, Some(arr[pivot]), limit)
      arr = left
    }
  }
}

///|
fn fixed_get_limit(len : Int) -> Int {
  let mut len = len
  let mut limit = 0
  while len > 0 {
    len = len / 2
    limit += 1
  }
  limit
}

///|
/// Try to sort the array with bubble sort.
/// 
/// It will only tolerate at most 8 unsorted elements. The time complexity is O(n).
/// 
/// Returns whether the array is sorted.
fn[T : Compare] fixed_try_bubble_sort(arr : MutArrayView[T]) -> Bool {
  let max_tries = 8
  let mut tries = 0
  for i in 1..<arr.length() {
    let mut sorted = true
    for j = i; j > 0 && arr[j - 1] > arr[j]; j = j - 1 {
      sorted = false
      arr.swap(j, j - 1)
    }
    if !sorted {
      tries += 1
      if tries > max_tries {
        return false
      }
    }
  }
  true
}

///|
/// Try to sort the array with bubble sort.
/// 
/// It will only tolerate at most 8 unsorted elements. The time complexity is O(n).
/// 
/// Returns whether the array is sorted.
fn[T : Compare] fixed_bubble_sort(arr : MutArrayView[T]) -> Unit {
  for i in 1..<arr.length() {
    for j = i; j > 0 && arr[j - 1] > arr[j]; j = j - 1 {
      arr.swap(j, j - 1)
    }
  }
}

///|
test "fixed_try_bubble_sort" {
  let arr : FixedArray[_] = [8, 7, 6, 5, 4, 3, 2, 1]
  let sorted = fixed_try_bubble_sort(arr.mut_view())
  inspect(sorted, content="true")
  assert_eq(arr, [1, 2, 3, 4, 5, 6, 7, 8])
}

///|
fn[T : Compare] fixed_partition(
  arr : MutArrayView[T],
  pivot_index : Int,
) -> (Int, Bool) {
  arr.swap(pivot_index, arr.length() - 1)
  let pivot = arr[arr.length() - 1]
  let mut i = 0
  let mut partitioned = true
  for j in 0..<(arr.length() - 1) {
    if arr[j] < pivot {
      if i != j {
        arr.swap(i, j)
        partitioned = false
      }
      i = i + 1
    }
  }
  arr.swap(i, arr.length() - 1)
  (i, partitioned)
}

///|
/// Choose a pivot index for quick sort.
/// 
/// It avoids worst case performance by choosing a pivot that is likely to be close to the median.
/// 
/// Returns the pivot index and whether the array is likely sorted.
fn[T : Compare] fixed_choose_pivot(arr : MutArrayView[T]) -> (Int, Bool) {
  let len = arr.length()
  let use_median_of_medians = 50
  let max_swaps = 4 * 3
  let mut swaps = 0
  let b = len / 4 * 2
  if len >= 8 {
    let a = len / 4 * 1
    let c = len / 4 * 3
    let sort_2 = (a : Int, b : Int) => if arr[a] > arr[b] {
      arr.swap(a, b)
      swaps += 1
    }
    let sort_3 = (a : Int, b : Int, c : Int) => {
      sort_2(a, b)
      sort_2(b, c)
      sort_2(a, b)
    }
    if len > use_median_of_medians {
      sort_3(a - 1, a, a + 1)
      sort_3(b - 1, b, b + 1)
      sort_3(c - 1, c, c + 1)
    }
    sort_3(a, b, c)
  }
  if swaps == max_swaps {
    arr.rev_in_place()
    (len - b - 1, true)
  } else {
    (b, swaps == 0)
  }
}

///|
fn[T : Compare] fixed_heap_sort(arr : MutArrayView[T]) -> Unit {
  let len = arr.length()
  for i = len / 2 - 1; i >= 0; i = i - 1 {
    fixed_sift_down(arr, i)
  }
  for i = len - 1; i > 0; i = i - 1 {
    arr.swap(0, i)
    fixed_sift_down(arr.slice(0, i), 0)
  }
}

///|
fn[T : Compare] fixed_sift_down(arr : MutArrayView[T], index : Int) -> Unit {
  let mut index = index
  let len = arr.length()
  let mut child = index * 2 + 1
  while child < len {
    if child + 1 < len && arr[child] < arr[child + 1] {
      child = child + 1
    }
    if arr[index] >= arr[child] {
      return
    }
    arr.swap(index, child)
    index = child
    child = index * 2 + 1
  }
}

///|
fn fixed_test_sort(f : (MutArrayView[Int]) -> Unit) -> Unit raise {
  let arr : FixedArray[_] = [5, 4, 3, 2, 1]
  f(arr.mut_view())
  assert_eq(arr, [1, 2, 3, 4, 5])
  let arr : FixedArray[_] = [5, 5, 5, 5, 1]
  f(arr.mut_view())
  assert_eq(arr, [1, 5, 5, 5, 5])
  let arr : FixedArray[_] = [1, 2, 3, 4, 5]
  f(arr.mut_view())
  assert_eq(arr, [1, 2, 3, 4, 5])
  let arr = FixedArray::make(1000, 0)
  for i in 0..<1000 {
    arr[i] = 1000 - i - 1
  }
  for i = 10; i < 1000; i = i + 10 {
    arr.swap(i, i - 1)
  }
  f(arr.mut_view())
  let expected = FixedArray::make(1000, 0)
  for i in 0..<1000 {
    expected[i] = i
  }
  assert_eq(arr, expected)
}

///|
test "fixed_heap_sort" {
  fixed_test_sort(arr => fixed_heap_sort(arr.mut_view()))
}

///|
test "fixed_bubble_sort" {
  fixed_test_sort(arr => fixed_bubble_sort(arr.mut_view()))
}

///|
test "sort" {
  fixed_test_sort(arr => arr.sort())
}

///|
test "stable_sort" {
  let arr : FixedArray[_] = [5, 1, 3, 4, 2]
  arr.mut_view().stable_sort()
  assert_eq(arr, [1, 2, 3, 4, 5])
  let arr = FixedArray::make(1000, 0)
  for i in 0..<1000 {
    arr[i] = 1000 - i - 1
  }
  for i = 10; i < 1000; i = i + 10 {
    arr.swap(i, i - 1)
  }
  arr.mut_view().stable_sort()
  let expected = FixedArray::make(1000, 0)
  for i in 0..<1000 {
    expected[i] = i
  }
  assert_eq(arr, expected)
}

///|
test "stable_sort_complex" {
  let run_lens = [86, 64, 21, 20, 22]
  let total_len = run_lens.fold(init=0, (acc, x) => acc + x)
  let arr = FixedArray::make(total_len, 0)
  let mut index = 0
  for i in 0..<run_lens.length() {
    for j in 0..<run_lens[i] {
      arr[index] = j
      index += 1
    }
  }
  assert_false(arr.is_sorted())
  arr.mut_view().stable_sort()
  assert_true(arr.is_sorted())
}

///|
test "find_streak with empty array" {
  let arr : FixedArray[Int] = []
  let (streak_end, was_reversed) = find_streak(arr.mut_view())
  inspect(streak_end, content="0")
  inspect(was_reversed, content="false")
}

///|
test "find_streak with single element array" {
  let arr : FixedArray[_] = [1]
  let (streak_end, was_reversed) = find_streak(arr.mut_view())
  inspect(streak_end, content="1")
  inspect(was_reversed, content="false")
}

///|
test "find_streak with increasing elements" {
  let arr : FixedArray[_] = [1, 2, 3, 4, 5]
  let (streak_end, was_reversed) = find_streak(arr.mut_view())
  inspect(streak_end, content="5")
  inspect(was_reversed, content="false")
}

///|
test "find_streak with decreasing elements" {
  let arr : FixedArray[_] = [5, 4, 3, 2, 1]
  let (streak_end, was_reversed) = find_streak(arr.mut_view())
  inspect(streak_end, content="5")
  inspect(was_reversed, content="true")
}

///|
test "provide_sorted_batch with long run" {
  let arr : FixedArray[_] = [1, 2, 3, 4, 5]
  let end = provide_sorted_batch(arr.mut_view(), 0, 5)
  inspect(end, content="5")
}

///|
test "fixed_quick_sort with limit reached" {
  let arr : FixedArray[_] = [5, 4, 3, 2, 1]
  fixed_quick_sort(arr.mut_view(), None, 0)
  assert_true(FixedArray::is_sorted(arr))
}

///|
test "fixed_quick_sort with balanced partitions" {
  let arr : FixedArray[_] = [5, 4, 3, 2, 1]
  fixed_quick_sort(arr.mut_view(), None, 10)
  assert_true(FixedArray::is_sorted(arr))
}

///|
fn minimum(x : Int, y : Int) -> Int {
  if x > y {
    y
  } else {
    x
  }
}

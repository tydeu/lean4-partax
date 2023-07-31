/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

/-!
# String Utilities
String theorems that help prove termination of parsers.
-/

namespace Partax.String

@[simp] theorem next'_eq_next {s : String} {p} {h} : s.next' p h = s.next p := rfl

theorem byteIdx_lt_of_atEnd {s : String} (h : ¬ s.atEnd p) : p.byteIdx < s.utf8ByteSize :=
  Nat.gt_of_not_le (mt decide_eq_true h)

theorem decreasing_remainder (s : String) (p p')
(he : ¬ s.atEnd p) (hlt : p < p') : s.utf8ByteSize - p'.byteIdx < s.utf8ByteSize - p.byteIdx :=
  Nat.sub_lt_sub_left (byteIdx_lt_of_atEnd he) hlt

macro_rules
| `(tactic| decreasing_trivial) =>
  `(tactic| apply String.decreasing_remainder; all_goals try decreasing_trivial)

nonrec theorem lt_next {s : String} {p} : p < s.next p := String.lt_next s p

theorem lt_next_of_lt {s : String} {p p'} (h : p < p') : p < s.next p' :=
  Nat.lt_trans h lt_next

theorem lt_next_of_le {s : String} {p p'} (h : p ≤ p') : p < s.next p' :=
  Nat.lt_of_le_of_lt h lt_next

theorem le_next_of_le {s : String} {p p'} (h : p ≤ p') : p ≤ s.next p' :=
  Nat.le_trans h (Nat.le_of_lt lt_next)

macro_rules
| `(tactic| decreasing_trivial) =>
  `(tactic| apply lt_next_of_le; (repeat apply le_next_of_le); apply Nat.le_refl)

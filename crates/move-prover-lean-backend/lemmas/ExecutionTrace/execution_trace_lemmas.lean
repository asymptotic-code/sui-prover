-- ExecutionTrace Lemmas for Requires/Ensures Reasoning
-- These lemmas help prove verification theorems about requires and ensures clauses

-- Helper lemma: accessing a list element within bounds
theorem list_getElem?_eq_some {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
  l[i]? = some l[i] := by
  simp [List.getElem?_eq_getElem h]

-- Helper lemma: for a singleton list, index 0 gives the element
theorem list_getElem?_singleton {α : Type} (x : α) :
  [x][0]? = some x := by
  rfl

-- Helper lemma: for a two-element list
theorem list_getElem?_two_0 {α : Type} (x y : α) :
  [x, y][0]? = some x := by
  rfl

theorem list_getElem?_two_1 {α : Type} (x y : α) :
  [x, y][1]? = some y := by
  rfl

-- Helper lemma: for a three-element list
theorem list_getElem?_three_0 {α : Type} (x y z : α) :
  [x, y, z][0]? = some x := by
  rfl

theorem list_getElem?_three_1 {α : Type} (x y z : α) :
  [x, y, z][1]? = some y := by
  rfl

theorem list_getElem?_three_2 {α : Type} (x y z : α) :
  [x, y, z][2]? = some z := by
  rfl

-- Lemma: if all elements are true, then specific indices are true
theorem forall_list_true_implies_index {l : List Bool} (h : ∀ (i : Nat), l[i]? = some true) (i : Nat) (hi : i < l.length) :
  l[i] = true := by
  have := h i
  simp [List.getElem?_eq_getElem hi] at this
  exact this

-- Lemma: if a specific index has true, the condition holds
theorem list_index_true_iff_decide {b : Bool} :
  [b][0]? = some true ↔ b = true := by
  simp

-- Lemma: for two-element list with decides
theorem list_two_index_0_true {b1 b2 : Bool} (h : ∀ (i : Nat), [b1, b2][i]? = some true) :
  b1 = true := by
  have := h 0
  simp at this
  exact this

theorem list_two_index_1_true {b1 b2 : Bool} (h : ∀ (i : Nat), [b1, b2][i]? = some true) :
  b2 = true := by
  have := h 1
  simp at this
  exact this

-- Lemma: for three-element list with decides
theorem list_three_index_0_true {b1 b2 b3 : Bool} (h : ∀ (i : Nat), [b1, b2, b3][i]? = some true) :
  b1 = true := by
  have := h 0
  simp at this
  exact this

theorem list_three_index_1_true {b1 b2 b3 : Bool} (h : ∀ (i : Nat), [b1, b2, b3][i]? = some true) :
  b2 = true := by
  have := h 1
  simp at this
  exact this

theorem list_three_index_2_true {b1 b2 b3 : Bool} (h : ∀ (i : Nat), [b1, b2, b3][i]? = some true) :
  b3 = true := by
  have := h 2
  simp at this
  exact this

-- Lemmas for 4-element lists
theorem list_getElem?_four_0 {α : Type} (a b c d : α) :
  [a, b, c, d][0]? = some a := by
  rfl

theorem list_getElem?_four_1 {α : Type} (a b c d : α) :
  [a, b, c, d][1]? = some b := by
  rfl

theorem list_getElem?_four_2 {α : Type} (a b c d : α) :
  [a, b, c, d][2]? = some c := by
  rfl

theorem list_getElem?_four_3 {α : Type} (a b c d : α) :
  [a, b, c, d][3]? = some d := by
  rfl

theorem list_four_index_0_true {b1 b2 b3 b4 : Bool} (h : ∀ (i : Nat), [b1, b2, b3, b4][i]? = some true) :
  b1 = true := by
  have := h 0
  simp at this
  exact this

theorem list_four_index_1_true {b1 b2 b3 b4 : Bool} (h : ∀ (i : Nat), [b1, b2, b3, b4][i]? = some true) :
  b2 = true := by
  have := h 1
  simp at this
  exact this

theorem list_four_index_2_true {b1 b2 b3 b4 : Bool} (h : ∀ (i : Nat), [b1, b2, b3, b4][i]? = some true) :
  b3 = true := by
  have := h 2
  simp at this
  exact this

theorem list_four_index_3_true {b1 b2 b3 b4 : Bool} (h : ∀ (i : Nat), [b1, b2, b3, b4][i]? = some true) :
  b4 = true := by
  have := h 3
  simp at this
  exact this

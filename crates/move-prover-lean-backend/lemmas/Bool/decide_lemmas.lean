-- Decide Lemmas for Boolean Conditions
-- These help with decide (condition) = true patterns in proofs

-- Basic decide lemmas
theorem decide_eq_true_iff {p : Prop} [Decidable p] :
  decide p = true ↔ p := by
  simp

theorem decide_eq_false_iff {p : Prop} [Decidable p] :
  decide p = false ↔ ¬p := by
  simp

-- Decide with conjunction
theorem decide_and_true {p q : Prop} [Decidable p] [Decidable q] (hp : p) (hq : q) :
  decide (p ∧ q) = true := by
  simp [hp, hq]

theorem decide_and_eq_true_iff {p q : Prop} [Decidable p] [Decidable q] :
  decide (p ∧ q) = true ↔ p ∧ q := by
  simp

-- Decide with disjunction
theorem decide_or_true_left {p q : Prop} [Decidable p] [Decidable q] (hp : p) :
  decide (p ∨ q) = true := by
  simp [hp]

theorem decide_or_true_right {p q : Prop} [Decidable p] [Decidable q] (hq : q) :
  decide (p ∨ q) = true := by
  simp [hq]

-- Decide with implication
theorem decide_implies_of_true {p q : Prop} [Decidable p] [Decidable q] (h : p → q) (hp : p) :
  decide q = true := by
  simp [h hp]

-- Decide with Bool
theorem decide_bool_eq_true (b : Bool) :
  decide (b = true) = b := by
  cases b <;> simp

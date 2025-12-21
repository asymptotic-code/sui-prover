-- Native implementations for Move vector module
-- These map Move vector operations to Lean's List type

namespace MoveVector

-- Vector is represented as List in Lean
-- Native functions provide the basic operations

def length (T : Type) [BEq T] [Inhabited T] (v : List T) : UInt64 :=
  v.length.toUInt64

def empty (T : Type) [BEq T] [Inhabited T] : List T :=
  []

def push_back (T : Type) [BEq T] [Inhabited T] (v : List T) (e : T) : Unit :=
  -- In pure Lean, we can't mutate, but for verification we model the effect
  ()

def pop_back (T : Type) [BEq T] [Inhabited T] (v : List T) : T :=
  match v.getLast? with
  | some e => e
  | none => default

def borrow (T : Type) [BEq T] [Inhabited T] (v : List T) (i : UInt64) : T :=
  v.getD i.toNat default

def borrow_mut (T : Type) [BEq T] [Inhabited T] (v : List T) (i : UInt64) : T :=
  v.getD i.toNat default

def swap (T : Type) [BEq T] [Inhabited T] (v : List T) (i : UInt64) (j : UInt64) : Unit :=
  ()

def destroy_empty (T : Type) [BEq T] [Inhabited T] (v : List T) : Unit :=
  ()

-- contains: Check if element is in vector (has early return, provided as native)
-- Non-monadic version (same as pure)
def contains (T : Type) [BEq T] [Inhabited T] (v : List T) (e : T) : Prop :=
  v.contains e

def contains.pure (T : Type) [BEq T] [Inhabited T] (v : List T) (e : T) : Prop :=
  v.contains e

def contains.aborts (_T : Type) [BEq _T] [Inhabited _T] (_v : List _T) (_e : _T) : Prop :=
  False

instance (T : Type) [BEq T] [Inhabited T] (v : List T) (e : T) : Decidable (contains.aborts T v e) := by
  unfold contains.aborts; infer_instance

-- index_of: Find index of element (has early return, provided as native)
def index_of.pure (T : Type) [BEq T] [Inhabited T] (v : List T) (e : T) : (Prop × UInt64) :=
  let rec findIdx (l : List T) (idx : Nat) : (Prop × UInt64) :=
    match l with
    | [] => (False, 0)
    | h :: t => if h == e then (True, idx.toUInt64) else findIdx t (idx + 1)
  findIdx v 0

def index_of.aborts (_T : Type) [BEq _T] [Inhabited _T] (_v : List _T) (_e : _T) : Prop :=
  False

instance (T : Type) [BEq T] [Inhabited T] (v : List T) (e : T) : Decidable (index_of.aborts T v e) := by
  unfold index_of.aborts; infer_instance

-- skip: Skip first n elements (uses macro, provided as native)
def skip (T : Type) [BEq T] [Inhabited T] (v : List T) (n : UInt64) : List T :=
  v.drop n.toNat

-- take: Take first n elements (uses macro, provided as native)
def take.pure (T : Type) [BEq T] [Inhabited T] (v : List T) (n : UInt64) : List T :=
  v.take n.toNat

def take.aborts (T : Type) [BEq T] [Inhabited T] (v : List T) (n : UInt64) : Prop :=
  n > (length T v)

instance (T : Type) [BEq T] [Inhabited T] (v : List T) (n : UInt64) : Decidable (take.aborts T v n) := by
  unfold take.aborts; infer_instance

-- swap_remove: Swap element with last and remove (has incomplete if, provided as native)
def swap_remove.pure (T : Type) [BEq T] [Inhabited T] (v : List T) (i : UInt64) : T :=
  v.getD i.toNat default

def swap_remove.aborts (T : Type) [BEq T] [Inhabited T] (v : List T) (_i : UInt64) : Prop :=
  (length T v) == 0

instance (T : Type) [BEq T] [Inhabited T] (v : List T) (i : UInt64) : Decidable (swap_remove.aborts T v i) := by
  unfold swap_remove.aborts; infer_instance

-- insert: Insert element at index (has while loop with complex abort tracking)
def insert.pure (_T : Type) [BEq _T] [Inhabited _T] (_v : List _T) (_e : _T) (_i : UInt64) : Unit :=
  ()

def insert.aborts (T : Type) [BEq T] [Inhabited T] (v : List T) (_e : T) (i : UInt64) : Prop :=
  i > (length T v)

instance (T : Type) [BEq T] [Inhabited T] (v : List T) (e : T) (i : UInt64) : Decidable (insert.aborts T v e i) := by
  unfold insert.aborts; infer_instance

-- remove: Remove element at index (has while loop with complex abort tracking)
def remove.pure (T : Type) [BEq T] [Inhabited T] (v : List T) (i : UInt64) : T :=
  v.getD i.toNat default

def remove.aborts (T : Type) [BEq T] [Inhabited T] (v : List T) (i : UInt64) : Prop :=
  i ≥ (length T v)

instance (T : Type) [BEq T] [Inhabited T] (v : List T) (i : UInt64) : Decidable (remove.aborts T v i) := by
  unfold remove.aborts; infer_instance

end MoveVector

-- Native implementations for prover::ghost module
-- Ghost variables for specification state tracking

namespace Ghost

-- Global ghost state accessor - returns a default value
-- In practice, this would track verification state, but we model it simply
def global (T : Type) (U : Type) [Inhabited U] : U := default

-- Set ghost state - no-op since we're not tracking state
def set (T : Type) (U : Type) (x : U) : Unit := ()

-- Borrow mutable ghost state - returns default
def borrow_mut (T : Type) (U : Type) [Inhabited U] : U := default

-- Declare global ghost variable - no-op
def declare_global (T : Type) (U : Type) : Unit := ()

-- Declare mutable global ghost variable - no-op
def declare_global_mut (T : Type) (U : Type) : Unit := ()

-- Havoc global state - no-op
def havoc_global (T : Type) (U : Type) : Unit := ()

end Ghost

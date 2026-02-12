import Loom.MonadAlgebras.Defs
import Loom.MonadAlgebras.Instances.Basic
import Loom.MonadAlgebras.Instances.ReaderT
import Loom.MonadAlgebras.Instances.StateT
-- import Plausible.Gen  -- Disabled: Plausible.Gen has been restructured

-- open Plausible

-- universe u

/-
NOTE: The Plausible.Gen type has changed from:
  ReaderT (ULift Nat) (StateT (ULift StdGen) Id)
to:
  RandT (ReaderT (ULift Nat) (Except GenError))
  = StateT (ULift StdGen) (ReaderT (ULift Nat) (Except GenError))

The monad transformer composition order has changed and there's now
an Except transformer at the base. This instance needs to be updated
to work with the new definition if Gen support is needed.
-/

/- Ordered Monad Algebra instance for Gen - DISABLED due to Plausible.Gen restructuring
instance MAlgGenInst : MAlgOrdered Gen (ULift Nat -> ULift StdGen -> Prop) :=
  inferInstanceAs
    (MAlgOrdered
      (ReaderT (ULift Nat)
        (StateT (ULift StdGen) Id))
      (ULift Nat ->
        ULift StdGen -> Prop))
-/

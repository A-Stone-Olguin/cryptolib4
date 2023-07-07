import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- To Probability : Might not be needed

noncomputable section 

instance : Monad Pmf where
  pure := Pmf.pure 
  bind := Pmf.bind

instance : LawfulFunctor Pmf where
  id_map := Pmf.map_id
  comp_map := λ f g x => (Pmf.map_comp f x g).symm
  map_const := sorry

instance : LawfulMonad Pmf where
  pure_bind := Pmf.pure_bind
  bind_assoc := Pmf.bind_bind
  bind_pure_comp := Pmf.bind_pure_comp 
  bind_map := sorry

#check Pmf.map_const
#check Pmf.map
#check Functor.mapConst

import SampLib.Syntax.ClosedExp
import SampLib.Syntax.ListValues
import SampLib.NatCounters
import SampLib.WeightedValidation
import SampLib.GeneralSyntax
import Samplers.Discrete.Urns

/-! # Closed constants and natural data in urn sampler binders -/

open ProbLang

namespace SampLib.UrnTerms

scoped instance uniform_closed {rT : Type _} : ClosedExp (Occil.uniformInt : Exp rT) where
  lc := UniformInt.uniformInt_lc
  fv := UniformInt.uniformInt_fv

scoped instance weighted_closed {rT : Type _} : ClosedExp (Occil.weightedChoice : Exp rT) where
  lc := MarkovTerms.weightedChoice_lc
  fv := by simp [Occil.weightedChoice, Occil.sumInts, Occil.uniformInt, Exp.fv]

scoped instance length_closed {rT : Type _} : ClosedExp (Occil.length : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.length, Exp.fv]

scoped instance sum_closed {rT : Type _} : ClosedExp (Occil.sumInts : Exp rT) where
  lc := WeightedValidation.sumInts_lc
  fv := WeightedValidation.sumInts_fv

scoped instance valid_closed {rT : Type _} :
    ClosedExp (Occil.DiscreteExtra.validUrn : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.DiscreteExtra.validUrn, Exp.fv]

scoped instance weights_closed {rT : Type _} :
    ClosedExp (Occil.DiscreteExtra.urnWeights : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.DiscreteExtra.urnWeights, Exp.fv]

scoped instance decrement_closed {rT : Type _} :
    ClosedExp (Occil.DiscreteExtra.adjustCounter : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.DiscreteExtra.adjustCounter, Exp.fv]

scoped instance increment_closed {rT : Type _} :
    ClosedExp (Occil.DiscreteExtra.incrementCounter : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.DiscreteExtra.incrementCounter, Exp.fv]

scoped instance zeros_closed {rT : Type _} :
    ClosedExp (Occil.DiscreteExtra.zeroCounters : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.DiscreteExtra.zeroCounters, Exp.fv]

scoped instance natData_closed {rT : Type _} [ProbLangℝ rT] (xs : List ℕ) :
    ClosedExp (NatCounters.encode (rT := rT) xs).fst where
  lc := (NatCounters.encode xs).lc
  fv := ListValues.listVal_fv _ xs (fun _ _ => rfl)

scoped instance wallenius_closed {rT : Type _} :
    ClosedExp (Occil.DiscreteExtra.walleniusMultivariate : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.DiscreteExtra.walleniusMultivariate, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

end SampLib.UrnTerms

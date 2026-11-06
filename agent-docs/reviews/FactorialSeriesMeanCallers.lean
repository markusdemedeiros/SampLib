import SampLib.Bernoulli.Laws.FactorialSeriesMean

open SampLib

example (m : FactorialSeries.Mode) :
    GeometricThreshold.mean (FactorialSeries.callbackBias m 0)
      (FactorialSeries.partialBias m) (FactorialSeries.limitBias m) 0 = 1 := by
  rw [FactorialSeries.mean_eq_value]
  cases m <;> simp [FactorialSeries.value]

example (m : FactorialSeries.Mode) :
    GeometricThreshold.mean (FactorialSeries.callbackBias m 1)
      (FactorialSeries.partialBias m) (FactorialSeries.limitBias m) 0 =
        FactorialSeries.value m 1 := FactorialSeries.mean_eq_value m 1

#print axioms FactorialSeries.mean_eq_value
#print axioms FactorialSeries.value_mem

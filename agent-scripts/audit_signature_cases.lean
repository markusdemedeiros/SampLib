-- The runner prepends the current audit command and imports the compiled suite.
open ProbLang Iris Iris.BI Iris.ProofMode TotalEris

namespace ReviewAuditSignatures

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem wrapped (E : CoPset) :
    let _ : True := True.intro
    SampLib.IsDistSpec (GF := GF) E pl(&Occil.fairCoin #())
      (SampLib.RealCoin.law SampLib.VonNeumann.fairBias) Val.bool :=
  SampLib.FairCoin.fairCoin_distSpec E

#audit_dist_spec ReviewAuditSignatures.wrapped for Occil.fairCoin
#audit_dist_spec SampLib.IntegralMixture.integralMixture_distSpec
  for Occil.FactoryExtra.integralMixture

omit [ProbLangDist.IsUniformInt rT] in
private theorem framePlain (E : CoPset) (P : IProp GF)
    (h : SampLib.IsDistSpec (GF := GF) E pl(&Occil.fairCoin #())
      (SampLib.RealCoin.law SampLib.VonNeumann.fairBias) Val.bool) :
    SampLib.IsOwnedDistSpec E P pl(&Occil.fairCoin #())
      (SampLib.RealCoin.law SampLib.VonNeumann.fairBias) Val.bool where
  spec F hF := by
    iintro ⟨HP, Hcredit⟩
    iapply (h.wp F hF _) $$ Hcredit
    iintro %b Hcredit
    iexists b
    iframe HP Hcredit
    itrivial

theorem owned (E : CoPset) (P : IProp GF) :
    SampLib.IsOwnedDistSpec E P pl(&Occil.fairCoin #())
      (SampLib.RealCoin.law SampLib.VonNeumann.fairBias) Val.bool :=
  framePlain E P (SampLib.FairCoin.fairCoin_distSpec E)

#audit_owned_dist_spec ReviewAuditSignatures.owned for Occil.fairCoin

omit [ProbLangDist.IsUniformInt rT] in
theorem circularOwned (E : CoPset) (P : IProp GF)
    (h : SampLib.IsOwnedDistSpec E P pl(&Occil.fairCoin #())
      (SampLib.RealCoin.law SampLib.VonNeumann.fairBias) Val.bool) :
    SampLib.IsOwnedDistSpec E P pl(&Occil.fairCoin #())
      (SampLib.RealCoin.law SampLib.VonNeumann.fairBias) Val.bool := h

/-- error: ReviewAuditSignatures.circularOwned assumes its own concrete sampler in a premise -/
#guard_msgs in
#audit_owned_dist_spec ReviewAuditSignatures.circularOwned for Occil.fairCoin

omit [ProbLangDist.IsUniformInt rT] in
theorem circularMixed (E : CoPset) (P : IProp GF)
    (h : SampLib.IsDistSpec (GF := GF) E pl(&Occil.fairCoin #())
      (SampLib.RealCoin.law SampLib.VonNeumann.fairBias) Val.bool) :
    SampLib.IsOwnedDistSpec E P pl(&Occil.fairCoin #())
      (SampLib.RealCoin.law SampLib.VonNeumann.fairBias) Val.bool := framePlain E P h

/-- error: ReviewAuditSignatures.circularMixed assumes its own concrete sampler in a premise -/
#guard_msgs in
#audit_owned_dist_spec ReviewAuditSignatures.circularMixed for Occil.fairCoin

/-- error: ReviewAuditSignatures.owned does not conclude with IsDistSpec -/
#guard_msgs in
#audit_dist_spec ReviewAuditSignatures.owned for Occil.fairCoin

/-- error: ReviewAuditSignatures.owned does not specify a call to Occil.realCoin -/
#guard_msgs in
#audit_owned_dist_spec ReviewAuditSignatures.owned for Occil.realCoin

omit [ProbLangDist.IsUniformInt rT] in
theorem circular (E : CoPset)
    (h : let _ : True := True.intro
      SampLib.IsDistSpec (GF := GF) E pl(&Occil.fairCoin #())
        (SampLib.RealCoin.law SampLib.VonNeumann.fairBias) Val.bool) :
    SampLib.IsDistSpec (GF := GF) E pl(&Occil.fairCoin #())
      (SampLib.RealCoin.law SampLib.VonNeumann.fairBias) Val.bool := h

/-- error: ReviewAuditSignatures.circular assumes its own concrete sampler in a premise -/
#guard_msgs in
#audit_dist_spec ReviewAuditSignatures.circular for Occil.fairCoin

/-- error: ReviewAuditSignatures.wrapped does not specify a call to Occil.realCoin -/
#guard_msgs in
#audit_dist_spec ReviewAuditSignatures.wrapped for Occil.realCoin

end ReviewAuditSignatures

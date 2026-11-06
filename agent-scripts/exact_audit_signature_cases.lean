-- The runner prepends the current exact auditor and imports the concrete vector proof.

#audit_latent_vector_spec SampLib.PSRNInsideShape.newInsideShape_vectorSpec
  for Occil.PSRN.newInsideShape

open Lean Elab Command Meta

-- Construct kernel-checked negative fixtures from the real theorem's exact type.
elab "make_circular_vector_fixtures" : command => liftTermElabM do
  let theoremName := ``SampLib.PSRNInsideShape.newInsideShape_vectorSpec
  let info ← getConstInfo theoremName
  let levels := info.levelParams.map Level.param
  forallTelescopeReducing info.type fun params result => do
    let proof := mkAppN (.const theoremName levels) params
    withLocalDeclD `h result fun h => do
      let type ← mkForallFVars (params.push h) result
      let value ← mkLambdaFVars (params.push h) h
      addDecl (.thmDecl {
        name := `ExactAuditRegression.circularVector, levelParams := info.levelParams,
        type, value })
    let payloadType ← inferType (.proj ``SampLib.LatentReal.IsLatentVectorSpec 1 proof)
    withLocalDeclD `h payloadType fun h => do
      let type ← mkForallFVars (params.push h) result
      let value ← mkLambdaFVars (params.push h) proof
      addDecl (.thmDecl {
        name := `ExactAuditRegression.circularPayload, levelParams := info.levelParams,
        type, value })

make_circular_vector_fixtures

/-- error: ExactAuditRegression.circularVector assumes its own concrete sampler in a premise -/
#guard_msgs in
#audit_latent_vector_spec ExactAuditRegression.circularVector for Occil.PSRN.newInsideShape

/-- error: ExactAuditRegression.circularPayload assumes its own concrete sampler in a premise -/
#guard_msgs in
#audit_latent_vector_spec ExactAuditRegression.circularPayload for Occil.PSRN.newInsideShape

/-- error: SampLib.PSRNInsideShape.newInsideShape_vectorSpec does not conclude with SampLib.LatentReal.IsLatentDistSpec -/
#guard_msgs in
#audit_latent_real_spec SampLib.PSRNInsideShape.newInsideShape_vectorSpec
  for Occil.PSRN.newInsideShape

#print axioms ExactAuditRegression.circularVector
#print axioms ExactAuditRegression.circularPayload

#audit_conditional_coin_spec SampLib.LatentReal.Coin.coin_programSpec
  for Occil.PSRN.coin

elab "make_circular_coin_fixture" : command => liftTermElabM do
  let theoremName := ``SampLib.LatentReal.Coin.coin_programSpec
  let info ← getConstInfo theoremName
  forallTelescopeReducing info.type fun params result => do
    withLocalDeclD `h result fun h => do
      let type ← mkForallFVars (params.push h) result
      let value ← mkLambdaFVars (params.push h) h
      addDecl (.thmDecl {
        name := `ExactAuditRegression.circularCoin, levelParams := info.levelParams,
        type, value })

make_circular_coin_fixture

/-- error: ExactAuditRegression.circularCoin assumes its own concrete sampler in a premise -/
#guard_msgs in
#audit_conditional_coin_spec ExactAuditRegression.circularCoin for Occil.PSRN.coin

/-- error: SampLib.LatentReal.Coin.coin_programSpec does not specify a call to Occil.PSRN.newUniform -/
#guard_msgs in
#audit_conditional_coin_spec SampLib.LatentReal.Coin.coin_programSpec
  for Occil.PSRN.newUniform

#print axioms ExactAuditRegression.circularCoin

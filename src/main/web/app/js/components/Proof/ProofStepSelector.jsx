import React from 'react'

const ProofStepSelector = ({
  onAssertClick,
  onAssumeClick,
  onTakeArbitraryClick,
  onCaseAnalysisClick
}) => (
  <div className="btn-group" role="group">
    <button type="button" className="btn btn-default"
     onClick={ onAssertClick }>Assert</button>
    <button type="button" className="btn btn-default"
     onClick={ onAssumeClick } disabled="disabled">Assume</button>
    <button type="button" className="btn btn-default"
     onClick={ onTakeArbitraryClick } disabled="disabled">Take Arbitrary</button>
    <button type="button" className="btn btn-default"
     onClick={ onCaseAnalysisClick } disabled="disabled">Case Analysis</button>
  </div>
)

export default ProofStepSelector

import React from 'react'

const ProofStepSelector = ({
  onAssertClick,
  onAssumeClick,
  onTakeArbitraryClick,
  onCaseAnalysisClick,
  onMarkCompleteClick,
  canMarkComplete
}) => {
  
  const completeButton = canMarkComplete ? (
      <button type="button" className="btn btn-primary"
       onClick={ onMarkCompleteClick }>Mark Complete</button>
    ) : (
      <button type="button" className="btn btn-primary"
       onClick={ onMarkCompleteClick } disabled="disabled">Mark Complete</button>
    )

  return (
    <div className="btn-group" role="group">
      <button type="button" className="btn btn-default"
       onClick={ onAssertClick }>Assert</button>
      <button type="button" className="btn btn-default"
       onClick={ onAssumeClick }>Assume</button>
      <button type="button" className="btn btn-default"
       onClick={ onTakeArbitraryClick } disabled="disabled">Take Arbitrary</button>
      <button type="button" className="btn btn-default"
       onClick={ onCaseAnalysisClick } disabled="disabled">Case Analysis</button>
      { completeButton }
    </div>
  )
}

export default ProofStepSelector

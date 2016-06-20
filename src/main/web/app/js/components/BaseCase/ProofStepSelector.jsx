import React from 'react'

const ProofStepSelector = ({
  onAssertClick,
  onAssumeClick,
  onTakeArbitraryClick,
  onCaseAnalysisClick,
  onMarkCompleteClick,
  canMarkComplete,
  area
}) => {
  
  const completeButton = canMarkComplete ? (
      <button type="button" className="btn btn-primary"
       onClick={ () => onMarkCompleteClick(area) }>Mark Complete</button>
    ) : (
      <button type="button" className="btn btn-primary"
       onClick={ () => onMarkCompleteClick(area) } disabled="disabled">Mark Complete</button>
    )

    // <button type="button" className="btn btn-default"
    //    onClick={ () => onCaseAnalysisClick(area) } disabled="disabled">Case Analysis</button>
 
  return (
    <div className="btn-group" role="group">
      <button type="button" className="btn btn-default"
       onClick={ () => onAssertClick(area) }>Assert</button>
      <button type="button" className="btn btn-default"
       onClick={ () => onAssumeClick(area) }>Assume</button>
      <button type="button" className="btn btn-default"
       onClick={ () => onTakeArbitraryClick(area) }>Take Arbitrary</button>
     { completeButton }
    </div>
  )
}

export default ProofStepSelector

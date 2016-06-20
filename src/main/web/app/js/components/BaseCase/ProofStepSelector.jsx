import React from 'react'

const ProofStepSelector = ({
  onEqualityClick,
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
       onClick={ onEqualityClick }>=</button>
     { completeButton }
    </div>
  )
}

export default ProofStepSelector


import React from 'react'

const ProofLine = ({ step }) => {

  const justified = step.justification != "INITIAL_STEP"

  return (
    <div>
      <div className="col-sm-1"></div>
      <div className="col-sm-6">{ justified ? "= " : ""}{ step.term }</div>
      <div className="col-sm-5">{ justified ? step.justification : "" }</div>
      <div className="clearfix" />
    </div>
  )
}

export default ProofLine


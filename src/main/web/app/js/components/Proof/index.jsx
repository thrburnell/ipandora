import React from 'react'
import CentredButton from '../CentredButton'
import RProofStepSelector from '../../containers/RProof/RProofStepSelector'
import RAssertLine from '../../containers/RProof/RAssertLine'
import { PROOF_STEP_TYPE } from '../../constants'

const Proof = ({ lines, complete, stepType }) => {

  const footerPanel = 
    stepType == PROOF_STEP_TYPE.ASSERT ? <RAssertLine />
    : <RProofStepSelector />

  const footer = complete ? null : (
      <div className="panel-footer text-center">
      { footerPanel }
      </div>)

  return (
    <div className="panel panel-default">
      <div className="panel-heading">
        <h3 className="panel-title pull-left">Proof</h3>
        <div className="clearfix" />
      </div>
      <ul className="list-group">
        {lines.map((g, i) => null)}
      </ul>
      { footer }
    </div>
  )
}

export default Proof


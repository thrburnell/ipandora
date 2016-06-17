import React from 'react'
import CentredButton from '../CentredButton'
import RProofStepSelector from '../../containers/RProof/RProofStepSelector'
import RAssertLine from '../../containers/RProof/RAssertLine'
import RImplicationLine from '../../containers/RProof/RImplicationLine'
import { PROOF_STEP_TYPE } from '../../constants'

const makeProofLine = (node, i, lineSelectable, onLineSelect) => {

  switch (node.type) {
    case "ASSERTION":
      return (
        <RImplicationLine lineNo={ node.lineNo } body={ node.body }
         justification={ node.justification } key={ i }
         selectable={ lineSelectable } onSelect={() => onLineSelect(node.id) } />
      )

    default:
      return <p>Not supported yet</p>
  }
}

const Proof = ({ lines, complete, stepType, lineSelectable, onLineSelect }) => {

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
      <table className="table">
        <tbody>
          {lines.map((g, i) => makeProofLine(g, i, lineSelectable, onLineSelect))}
        </tbody>
      </table>
      { footer }
    </div>
  )
}

export default Proof


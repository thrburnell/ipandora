import React from 'react'
import CentredButton from '../CentredButton'
import RProofStepSelector from '../../containers/RProof/RProofStepSelector'
import RAssertLine from '../../containers/RProof/RAssertLine'
import RAssumeLine from '../../containers/RProof/RAssumeLine'
import RImplicationLine from '../../containers/RProof/RImplicationLine'
import AssumptionLine from './AssumptionLine'
import { PROOF_STEP_TYPE } from '../../constants'

const makeProofLine = (node, i, lineSelectable, onLineSelect) => {

  switch (node.type) {
    case "ASSERTION":
      return (
        <RImplicationLine lineNo={ node.lineNo } body={ node.body }
         justification={ node.justification } key={ i }
         selectable={ lineSelectable } onSelect={() => onLineSelect(node.id) } />
      )

    case "ASSUMPTION":
      return (
        <AssumptionLine lineNo={ node.lineNo } body={ node.body } key={ i }
         selectable={ lineSelectable } onSelect={() => onLineSelect(node.id) } />
      )

    default:
      return <p>Not supported yet</p>
  }
}

const getFooterComponent = (type) => {
  switch (type) {
    case PROOF_STEP_TYPE.ASSERT:
      return <RAssertLine />

    case PROOF_STEP_TYPE.ASSUME:
      return <RAssumeLine />

    default:
      return <RProofStepSelector />
  }
}

const Proof = ({ lines, complete, stepType, lineSelectable, onLineSelect }) => {

  const footer = complete ? null : (
      <div className="panel-footer text-center">
      { getFooterComponent(stepType) }
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


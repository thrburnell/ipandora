import React from 'react'
import CentredButton from '../CentredButton'
import RProofStepSelector from '../../containers/RInductiveCase/RProofStepSelector'
import RAssertLine from '../../containers/RInductiveCase/RAssertLine'
import RAssumeLine from '../../containers/RInductiveCase/RAssumeLine'
import RTakeArbitraryLine from '../../containers/RInductiveCase/RTakeArbitraryLine'
import RImplicationLine from '../../containers/RInductiveCase/RImplicationLine'
import AssumptionLine from './AssumptionLine'
import ArbitraryLine from './ArbitraryLine'
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

    case "TAKE_ARBITRARY":
      return (
        <ArbitraryLine lineNo={ node.lineNo } body={ node.body } key={ i }
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

    case PROOF_STEP_TYPE.TAKE_ARBITRARY:
      return <RTakeArbitraryLine />

    default:
      return <RProofStepSelector />
  }
}

const InductiveCase = ({ lines, complete, stepType, 
  lineSelectable, onLineSelect,
  arbitrary, hypothesis, toShow
}) => {

  const footer = complete ? null : (
      <div className="panel-footer text-center">
      { getFooterComponent(stepType) }
      </div>)

  const divClassName = ["panel", "panel-default",
    complete ? "panel-success" : ""].join(" ")

  return (
    <div className={ divClassName }>
      <div className="panel-heading">
        <h3 className="panel-title pull-left">Inductive Case</h3>
        <div className="clearfix" />
      </div>
      <table className="table">
        <tbody>
          <tr>
            <td colspan="2">Take an arbitrary <strong>{ arbitrary.name }</strong> in  <strong>{ arbitrary.domain }</strong></td>
          </tr>
          <tr>
            <td><strong>Inductive Hypothesis:</strong></td>
            <td>{ hypothesis }</td>
          </tr>
          <tr>
            <td><strong>To Show:</strong></td>
            <td>{ toShow }</td>
          </tr>
        </tbody>
      </table>
      <table className="table">
        <tbody>
          {lines.map((g, i) => 
            makeProofLine(g, i, lineSelectable, onLineSelect))}
        </tbody>
      </table>
      { footer }
    </div>
  )
}

export default InductiveCase


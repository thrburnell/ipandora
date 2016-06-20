import React from 'react'
import CentredButton from '../CentredButton'
import RProofStepSelector from '../../containers/RInductiveCase/RProofStepSelector'
import REqualityLine from '../../containers/RInductiveCase/REqualityLine'
import InitialTermLine from './InitialTermLine'
import FunctionDefinitionLine from './FunctionDefinitionLine'
import ArithmeticLine from './ArithmeticLine'
import InductiveHypothesisLine from './InductiveHypothesisLine'
import { PROOF_STEP_TYPE } from '../../constants'

const makeProofLine = (node, i, lineSelectable, onLineSelect) => {

  switch (node.type) {
    case "INITIAL_TERM":
      return <InitialTermLine key={i} body={ node.body } />

    case "FUNCTION_DEFINITION":
      return <FunctionDefinitionLine key={i} body={ node.body } />

    case "ARITHMETIC":
      return <ArithmeticLine key={i} body={ node.body } />

    case "INDUCTIVE_HYPOTHESIS":
      return <InductiveHypothesisLine key={i} body={ node.body } />

    default:
      return <p>Not supported yet</p>
  }
}

const getFooterComponent = (type) => {
  switch (type) {
    case PROOF_STEP_TYPE.EQUALITY:
      return <REqualityLine />

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


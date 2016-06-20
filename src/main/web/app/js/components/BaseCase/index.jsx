import React from 'react'
import CentredButton from '../CentredButton'
import RProofStepSelector from '../../containers/RBaseCase/RProofStepSelector'
import REqualityLine from '../../containers/RBaseCase/REqualityLine'
import InitialTermLine from './InitialTermLine'
import FunctionDefinitionLine from './FunctionDefinitionLine'
import ArithmeticLine from './ArithmeticLine'
import { PROOF_STEP_TYPE } from '../../constants'

const makeProofLine = (node, i) => {

  switch (node.type) {
    case "INITIAL_TERM":
      return <InitialTermLine key={i} body={ node.body } />

    case "FUNCTION_DEFINITION":
      return <FunctionDefinitionLine key={i} body={ node.body } />

    case "ARITHMETIC":
      return <ArithmeticLine key={i} body={ node.body } />

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

const BaseCase = ({ lines, complete, stepType, 
  lineSelectable, onLineSelect, toShow
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
        <h3 className="panel-title pull-left">Base Case</h3>
        <div className="clearfix" />
      </div>
      <table className="table">
        <tbody>
          <tr>
            <td><strong>To Show</strong></td>
            <td>{ toShow }</td>
          </tr>
        </tbody>
      </table>
      <table className="table">
        <tbody>
          {lines.map((g, i) => 
            makeProofLine(g, i))}
        </tbody>
      </table>
      { footer }
    </div>
  )
}

export default BaseCase


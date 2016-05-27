import React from 'react'
import InitialStepInput from './InitialStepInput'
import NewStepInput from './NewStepInput'
import ProofLine from './ProofLine'

const BaseCase = ({ 
  toShow, 
  steps=[],
  stateValid=true,
  active=false, 
  onInitialEntry,
  onStepEntry
}) => {

  if (!active) {
    return null
  }

  const initial = steps.length == 0 ? (
      <li className="list-group-item">
        <InitialStepInput onButtonClick={(input) => onInitialEntry(input)} />
      </li>) : null

  const rest = steps.length > 0 ? (
      <li className="list-group-item">
        <NewStepInput 
          invalid={!stateValid} 
          onCheckClick={(input, justification) => onStepEntry(input, justification)} />
      </li>) : null

  const stepLis = steps.map((step, i) => (
    <li className="list-group-item" key={i}>
      <ProofLine step={step} />
    </li>
  ))

  return (
    <div className="panel panel-default">
      <div className="panel-heading">
        <h3 className="panel-title">Base Case</h3>
      </div>
      <ul className="list-group">
        <li className="list-group-item">
          <strong>To Show: </strong>
          { toShow }
        </li>
      </ul>
      <ul className="list-group">
        { stepLis }
      </ul>
      <ul className="list-group">
        { initial }
        { rest }
      </ul>
    </div>
  )
}

export default BaseCase


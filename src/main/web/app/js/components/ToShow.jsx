import React from 'react'
import { PROOF_MODE } from '../constants'

const ToggleText = ({ mode, knownValid, onToggleClick }) => {
  const text = mode == PROOF_MODE.INDUCTION ? "By direct" : "By induction"
  return knownValid ? null : (
    <p className="panel-title pull-right">
      <a href="#" onClick={(e) => { onToggleClick(); e.preventDefault(); }}>{ text }</a>
    </p>
  )
}

const Form = ({ mode, knownInvalid, onButtonClick }) => {
  let formulaEntry
  let variableEntry

  const inductionVarEntry = () => (
    mode == PROOF_MODE.INDUCTION 
    ? (<div className="col-sm-3">
        <input ref={node => { variableEntry = node }} type="text" 
        className="form-control monospace-font" placeholder="by induction on" />
      </div>)
    : null
  )

  const button = () => {
    const className = ["btn", knownInvalid ? "btn-danger" : "btn-primary"].join(" ")
    const text = knownInvalid ? "Retry" : "Get Started"

    return (<button type="button" className={ className } onClick={(e) => {
      onButtonClick(formulaEntry.value, variableEntry ? variableEntry.value : undefined)
      e.preventDefault();  
    }}>{ text }</button>)
  }

  return (
    <form className="form-horizontal">
      <div className="form-group">
        <div className={["col-sm-", mode == PROOF_MODE.INDUCTION ? "9" : "12"].join("")}>
          <input ref={node => { formulaEntry = node }} type="text" className="form-control monospace-font" placeholder="\FORALL n in Nat. ..." />
        </div>
        { inductionVarEntry() }
      </div>
      <div className="form-group bottom-no-margin">
        <div className="col-sm-12 text-center">
          { button() }
        </div>
      </div>
    </form>
  )
}

const ToShow = ({ 
  active=true, 
  valid, 
  mode,
  onToggleClick,
  onButtonClick,
  formula
}) => {

  if (!active) return null

  const knownValid = valid != undefined && valid
  const knownInvalid = valid != undefined && !valid

  const panelClassName = [
    "panel", "panel-default", 
    knownValid ? "panel-success" : knownInvalid ? "panel-danger" : ""
  ].join(" ")

  const body = () => {
    return knownValid ? formula : <Form mode={ mode } knownInvalid={ knownInvalid } onButtonClick={ onButtonClick } />
  }

  return (
    <div className={ panelClassName }>
      <div className="panel-heading">
        <h3 className="panel-title pull-left">To Show</h3>
        <ToggleText mode={ mode } knownValid={ knownValid } onToggleClick={ onToggleClick }/>
        <div className="clearfix" />
      </div>
      <div className="panel-body">
        { body() }
      </div>
    </div>
  )
}

export default ToShow


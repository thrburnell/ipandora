import React from 'react'
import ToggleText from './ToggleText'
import Form from './Form'

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


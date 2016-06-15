import React from 'react'
import { PROOF_MODE } from '../../constants'

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
    <div className="form-horizontal">
      <div className="form-group">
        <div className={["col-sm-", mode == PROOF_MODE.INDUCTION ? "9" : "12"].join("")}>
          <input ref={node => { formulaEntry = node }} type="text" 
           className="form-control monospace-font" placeholder="\FORALL n in Nat. ..." />
        </div>
        { inductionVarEntry() }
      </div>
      <div className="form-group bottom-no-margin">
        <div className="col-sm-12 text-center">
          { button() }
        </div>
      </div>
    </div>
  )
}

export default Form


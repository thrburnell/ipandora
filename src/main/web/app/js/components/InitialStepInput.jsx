import React from 'react'

const InitialStepInput = ({ onButtonClick }) => {

  let input
  return (
    <div className="input-group">
      <input ref={node => { input = node }} type="text" className="form-control monospace-font" placeholder="f(n)" />
      <span className="input-group-btn">
        <button className="btn btn-default" type="button" onClick={() => onButtonClick(input.value)}>Next</button>
      </span>
    </div>
  )
}

export default InitialStepInput


import React from 'react'

const NewStepInput = ({ onCheckClick, invalid=false }) => {

  const btnClassName = ["btn", "btn-default", invalid ? "btn-danger" : ""].join(" ")

  let input, sel
  return (
    <div className="form-horizontal">
      <div className="form-group bottom-no-margin">
        <div className="col-sm-7">
          <div className="input-group">
            <span className="input-group-addon">=</span>
            <input ref={node => { input = node}} type="text" className="form-control monospace-font" />
          </div>
        </div>
        <div className="col-sm-3">
          <select className="form-control" ref={node => { sel = node }}>
            <option value="ARITHMETIC">by arithmetic</option>
            <option value="FUNCTION_DEFINITION">by function definition</option>
          </select>
        </div>
        <div className="col-sm-2">
          <button className={btnClassName} type="button" onClick={() => onCheckClick(input.value, sel.value)}>Check</button>
        </div>
      </div>
    </div>
  )
}

export default NewStepInput


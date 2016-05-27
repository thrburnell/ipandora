import React from 'react'

const FunctionInput = ({ title, onValidateClick, valid }) => {

  const className = ["panel", "panel-default", valid ? "panel-success" : valid == undefined ? "" : "panel-danger"].join(" ")

  let input
  return (
    <div className={className}>
      <div className="panel-heading">
        <h3 className="panel-title pull-left">Function Definition</h3>
        <p className="panel-title pull-right">
          <a href="#" onClick={ (e) => { onValidateClick(input.value); e.preventDefault(); } }>Validate</a>
        </p>
        <div className="clearfix"></div>
      </div>
      <div className="panel-body">
        <form>
          <div className="form-group bottom-no-margin">
            <textarea ref={node => { input = node }} className="form-control monospace-font" rows="3" />
          </div>
        </form>
      </div>
    </div>
  )
}

export default FunctionInput


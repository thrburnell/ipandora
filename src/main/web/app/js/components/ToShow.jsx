import React from 'react'

const ToShow = ({ active=false, onValidateClick, valid }) => {

  if (!active) {
    return null
  }

  const className = ["panel", "panel-default", valid ? "panel-success" : valid == undefined ? "" : "panel-danger"].join(" ")

  let formula
  let variable
  return (
    <div className={className}>
      <div className="panel-heading">
        <h3 className="panel-title pull-left">To Show</h3>
        <p className="panel-title pull-right">
          <a href="#" onClick={ (e) => { onValidateClick(formula.value, variable.value); e.preventDefault(); } }>Validate</a>
        </p>
        <div className="clearfix"></div>
      </div>
      <div className="panel-body">
        <form className="form-horizontal">
          <div className="form-group bottom-no-margin">
            <div className="col-sm-9">
              <input ref={node => { formula = node }} type="text" className="form-control monospace-font" placeholder="\FORALL n in Nat. ..." />
            </div>
            <div className="col-sm-3">
              <input ref={node => { variable = node }} type="text" className="form-control monospace-font" placeholder="by induction on" />
            </div>
          </div>
        </form>
      </div>
    </div>
  )
}

export default ToShow


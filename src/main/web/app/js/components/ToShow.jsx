import React from 'react'
import { PROOF_MODE } from '../constants'

const ToShow = ({ active=true, valid, mode, onToggleClick }) => {

  if (!active) {
    return null
  }

  const className = [
    "panel", "panel-default", 
    valid ? "panel-success" : valid == undefined ? "" : "panel-danger"
  ].join(" ")

  const toggleText = mode == PROOF_MODE.INDUCTION ? "By direct" : "By induction"

  let formula
  let variable
  return (
    <div className={className}>
      <div className="panel-heading">
        <h3 className="panel-title pull-left">To Show</h3>
        <p className="panel-title pull-right">
          <a href="#" onClick={(e) => { onToggleClick(); e.preventDefault(); }}>{ toggleText }</a>
        </p>
        <div className="clearfix"></div>
      </div>
      <div className="panel-body">
        <form className="form-horizontal">
          <div className="form-group">
            <div className={["col-sm-", mode == PROOF_MODE.INDUCTION ? "9" : "12"].join("")}>
              <input ref={node => { formula = node }} type="text" className="form-control monospace-font" placeholder="\FORALL n in Nat. ..." />
            </div>
            { mode == PROOF_MODE.INDUCTION 
              ? <div className="col-sm-3">
                <input ref={node => { variable = node }} type="text" className="form-control monospace-font" placeholder="by induction on" />
              </div>
              : null }
          </div>
          <div className="form-group bottom-no-margin">
            <div className="col-sm-12 text-center">
              <button type="button" className="btn btn-primary">Get Started</button>
            </div>
          </div>
        </form>
      </div>
    </div>
  )
}

export default ToShow


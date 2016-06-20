import React from 'react'
import { EQUALITY_JUSTIFICATION } from '../../constants'

const AssertLine = ({
  fields: { formula, justification },
  onSubmit,
  error,
  resetForm,
  handleSubmit,
  submitting,
  onCloseClick
}) => {

  const formulaClassName = ["col-sm-6",
    formula.touched && formula.error ? "has-error" : ""].join(" ")

  const justClassName = ["col-sm-3",
    justification.touched && justification.error ? "has-error" : ""].join(" ")

  return (
    <form className="form-horizontal" onSubmit={ handleSubmit }>
      <div className="form-group bottom-no-margin">
        <div className={ formulaClassName }>
          <div className="input-group">
            <span className="input-group-addon" id="basic-addon1">=</span>
            <input type="text" {...formula}
             className="form-control monospace-font" placeholder="..." />
          </div>
        </div>
        <div className={ justClassName }>
          <select className="form-control full-width" {...justification}>
            <option></option>
            <option value={ EQUALITY_JUSTIFICATION.ARITHMETIC }>by arithmetic</option>
            <option value={ EQUALITY_JUSTIFICATION.FUNCTION_DEFINITION }>by function def.</option>
            <option value={ EQUALITY_JUSTIFICATION.INDUCTIVE_HYPOTHESIS }>by ind. hyp.</option>
          </select>
        </div>
        <div className="col-sm-2 text-right">
          <button type="submit" className="btn btn-primary full-width"
           disabled={ submitting }>Add</button>
        </div>
        <div className="col-sm-1 text-right">
          <button type="button" className="btn btn-default full-width"
           onClick={ onCloseClick }>
            x
          </button>
        </div>
      </div>
    </form>
  )
}

export default AssertLine


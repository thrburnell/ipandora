import React from 'react'
import { ASSERT_JUSTIFICATION_TYPE } from '../../constants'

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
          <input type="text" {...formula}
           className="form-control monospace-font" placeholder="..." />
        </div>
        <div className={ justClassName }>
          <select className="form-control full-width" {...justification}>
            <option></option>
            <option value={ ASSERT_JUSTIFICATION_TYPE.IMPLICATION }>by implication</option>
            <option value={ null }>by something else</option> 
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


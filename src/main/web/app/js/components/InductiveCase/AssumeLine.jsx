import React from 'react'

const AssumeLine = ({
  fields: { formula },
  onSubmit,
  handleSubmit,
  submitting,
  onCloseClick
}) => {

  const formulaClassName = ["col-sm-9",
    formula.touched && formula.error ? "has-error" : ""].join(" ")

  return (
    <form className="form-horizontal" onSubmit={ handleSubmit }>
      <div className="form-group bottom-no-margin">
        <div className={ formulaClassName }>
          <input type="text" {...formula}
           className="form-control monospace-font" placeholder="..." />
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

export default AssumeLine

